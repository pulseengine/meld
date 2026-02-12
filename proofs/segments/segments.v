(*
  Segments proofs.

  Source: meld-core/src/segments.rs
  Spec baseline: WebAssembly Core Specification, Release 3.0.
  See proofs/DECISIONS.md.
*)

From Stdlib Require Import Arith Lia.

(*
  Minimal model of index offsetting used during segment layout. This models the
  idea that applying a fixed base offset to segment indices is injective, which
  is a key invariant when re-indexing tables, memories, or data segments.
*)
Definition offset_map (base idx : nat) : nat := base + idx.

Theorem offset_map_injective :
  forall base i j,
    offset_map base i = offset_map base j -> i = j.
Proof.
  intros base i j H.
  unfold offset_map in H.
  lia.
Qed.
