(*
  Resolver proofs.

  Source: meld-core/src/resolver.rs
  Spec baseline: WebAssembly Core Specification, Release 3.0.
  See proofs/DECISIONS.md.
*)

From Coq Require Import List Arith Lia PeanoNat.
Import ListNotations.

(*
  Minimal model of name resolution as an association list from identifiers to
  indices. If the resolver produces a mapping with unique keys, then any key
  maps to at most one index.
*)
Definition key_map := list (nat * nat).

Fixpoint lookup (k : nat) (m : key_map) : option nat :=
  match m with
  | [] => None
  | (k0, v0) :: m' =>
      if Nat.eqb k k0 then Some v0 else lookup k m'
  end.

Theorem unique_key_value :
  forall (m : key_map) k v1 v2,
    NoDup (map fst m) ->
    In (k, v1) m ->
    In (k, v2) m ->
    v1 = v2.
Proof.
  induction m as [| [k0 v0] m IH]; intros k v1 v2 Hnodup H1 H2.
  - contradiction.
  - simpl in Hnodup.
    inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
    simpl in H1, H2.
    destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
    + inversion H1; inversion H2; subst; reflexivity.
    + inversion H1; subst.
      exfalso.
      apply Hnotin.
      apply in_map with (f := fst) in H2.
      exact H2.
    + inversion H2; subst.
      exfalso.
      apply Hnotin.
      apply in_map with (f := fst) in H1.
      exact H1.
    + apply IH with (k := k); auto.
Qed.

Theorem lookup_complete :
  forall (m : key_map) k v,
    NoDup (map fst m) ->
    In (k, v) m ->
    lookup k m = Some v.
Proof.
  induction m as [| [k0 v0] m IH]; intros k v Hnodup Hin.
  - contradiction.
  - simpl in Hnodup.
    inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      rewrite Nat.eqb_refl.
      reflexivity.
    + destruct (Nat.eqb k k0) eqn:Heq.
      * apply Nat.eqb_eq in Heq; subst.
        exfalso.
        apply Hnotin.
        apply in_map with (f := fst) in Hin.
        exact Hin.
      * apply IH; auto.
Qed.
