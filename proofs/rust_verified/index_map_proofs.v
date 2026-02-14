(*
  Pure-model proofs for index offset mapping.

  This file is intentionally independent from the translated Rust module.
  It establishes a simple injectivity property that we later mirror for the
  translated code.
*)

From Stdlib Require Import Arith Lia.

Definition offset_map (base idx : nat) : nat := base + idx.

Theorem offset_map_injective :
  forall base i j,
    offset_map base i = offset_map base j -> i = j.
Proof.
  intros base i j H.
  unfold offset_map in H.
  lia.
Qed.
