#!/usr/bin/env bash
# Kernel check of meld's Rocq proofs: compile every gated .v file with coqc,
# re-check the compiled libraries with coqchk, and fail if the kernel reports
# any axiom outside proofs/kernel-axioms-allowlist.txt, or any other trust
# assumption (impredicative Set, type-in-type, unsafe fixpoints, assumed
# positivity, rewrite rules).
#
# Why on top of `bazel test`: a Rocq proof that compiles can still rest on an
# `Axiom` or `Parameter`, and the census in proofs.yml only counts the text
# `Admitted.`. coqchk reports every axiom the checked libraries reach,
# including ones reached through a dependency, which no text scan sees.
#
# Needs coqc and coqchk on PATH (proofs.yml runs it under nix-shell).
# Usage: proofs/kernel_check.sh   (from the repository root)
set -uo pipefail

root=$(pwd)
[ -d "$root/proofs" ] || { echo "::error::run from the repository root"; exit 2; }
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Logical prefix per directory, as the BUILD.bazel include_path values give
# them. A .v file this table does not place fails the check rather than being
# skipped: an unplaced file would otherwise be a proof nothing kernel-checks.
prefix_of() {
  case "$1" in
    proofs/spec/copy_layout_spec.v)        echo MeldCopyLayout ;;
    proofs/spec/*.v)                       echo MeldSpec ;;
    proofs/transformations/adapter/*.v)    echo MeldAdapter ;;
    proofs/transformations/merge/*.v)      echo MeldMerge ;;
    proofs/transformations/resolve/*.v)    echo MeldResolve ;;
    proofs/rust_verified/*_proofs.v)       echo Standalone ;;
    proofs/adapter/*.v | proofs/attestation/*.v | proofs/merger/*.v | \
    proofs/parser/*.v | proofs/resolver/*.v | proofs/rewriter/*.v | \
    proofs/segments/*.v)                   echo Standalone ;;
    *) return 1 ;;
  esac
}

excluded=$(sed 's/#.*//' proofs/gate-exclusions.txt | tr -d ' \t' | grep -v '^$' || true)
files=()
while IFS= read -r f; do
  if printf '%s\n' "$excluded" | grep -qxF "$f"; then continue; fi
  if ! p=$(prefix_of "$f"); then
    echo "::error::$f has no logical prefix in proofs/kernel_check.sh, so nothing would kernel-check it. Add it to prefix_of."
    exit 1
  fi
  mkdir -p "$work/$p"
  cp "$f" "$work/$p/"
  files+=("$p/$(basename "$f")")
done < <(find proofs -name '*.v' | sed 's|^\./||' | sort)
[ "${#files[@]}" -gt 0 ] || { echo "::error::no .v files found; the check would be vacuous"; exit 1; }

Q=()
for d in "$work"/*/; do d=$(basename "$d"); Q+=(-Q "$d" "$d"); done

# Compile in dependency order by retrying: each pass compiles what it can.
cd "$work" || exit 2
left=("${files[@]}")
for _ in $(seq 1 ${#files[@]}); do
  next=()
  for f in "${left[@]}"; do
    coqc "${Q[@]}" "$f" > "${f%.v}.log" 2>&1 || next+=("$f")
  done
  [ "${#next[@]}" -eq "${#left[@]}" ] && break
  left=("${next[@]}")
  [ "${#left[@]}" -eq 0 ] && break
done
if [ "${#left[@]}" -ne 0 ]; then
  for f in "${left[@]}"; do echo "::error::coqc failed on $f:"; tail -20 "${f%.v}.log"; done
  exit 1
fi

mods=()
for f in "${files[@]}"; do m=${f%.v}; mods+=("${m//\//.}"); done
coqchk -o "${Q[@]}" "${mods[@]}" > coqchk.out 2>&1
rc=$?
cd "$root" || exit 2
if [ "$rc" -ne 0 ] || ! grep -q '^Modules were successfully checked' "$work/coqchk.out"; then
  echo "::error::coqchk exited $rc or did not finish checking"
  tail -40 "$work/coqchk.out"
  exit 1
fi
checked=$(grep -c '^Checking library: ' "$work/coqchk.out" || true)
if [ "$checked" -lt "${#files[@]}" ]; then
  echo "::error::coqchk checked $checked libraries, fewer than the ${#files[@]} compiled"
  exit 1
fi

# The CONTEXT SUMMARY lists each trust category as `* <name>: <items>`, the
# items either `<none>` or one per following line.
summary=$(sed -n '/^CONTEXT SUMMARY/,$p' "$work/coqchk.out")
echo "$summary"
section() {
  printf '%s\n' "$summary" | awk -v h="$1" '
    index($0, "* " h ":") == 1 { on = 1; sub(/^[^:]*:[ ]*/, ""); if ($0 != "") print; next }
    on && /^\* / { on = 0 }
    on { gsub(/^[ \t]+|[ \t]+$/, ""); if ($0 != "") print }'
}

fail=0
# Fail closed on the summary format: every `* ` line must be one this script
# judges. A category a newer coqchk adds would otherwise go unread.
while IFS= read -r line; do
  case "$line" in
    "* Theory: Set is predicative" | "* Theory: Rewrite rules are not allowed" | \
    "* Axioms:"* | "* Constants/Inductives relying on type-in-type:"* | \
    "* Constants/Inductives relying on unsafe (co)fixpoints:"* | \
    "* Inductives whose positivity is assumed:"*) ;;
    *) echo "::error::coqchk summary line this check does not judge: $line"; fail=1 ;;
  esac
done < <(printf '%s\n' "$summary" | grep '^\* ')
printf '%s\n' "$summary" | grep -q '^\* Theory: Set is predicative' ||
  { echo "::error::the checked libraries use impredicative Set"; fail=1; }
printf '%s\n' "$summary" | grep -q '^\* Theory: Rewrite rules are not allowed' ||
  { echo "::error::the checked libraries allow rewrite rules"; fail=1; }
for cat in "Constants/Inductives relying on type-in-type" \
           "Constants/Inductives relying on unsafe (co)fixpoints" \
           "Inductives whose positivity is assumed"; do
  got=$(section "$cat")
  [ "$got" = "<none>" ] || { echo "::error::$cat: $got"; fail=1; }
done

allow=$(sed 's/#.*//' proofs/kernel-axioms-allowlist.txt | tr -d ' \t' | grep -v '^$' || true)
axioms=$(section "Axioms")
[ -n "$axioms" ] || { echo "::error::coqchk printed no Axioms line; the summary format changed"; exit 1; }
if [ "$axioms" != "<none>" ]; then
  while IFS= read -r ax; do
    name=${ax%% :*}
    if ! printf '%s\n' "$allow" | grep -qxF "$name"; then
      echo "::error::axiom $name is not in proofs/kernel-axioms-allowlist.txt"
      fail=1
    fi
  done <<< "$axioms"
fi
[ "$fail" -eq 0 ] && echo "::notice::kernel check: ${#files[@]} files compiled, $checked libraries checked by coqchk, no axioms outside the allowlist"
exit "$fail"
