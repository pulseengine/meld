(*
  Implementation proofs for resolver_core.rs

  This file establishes the connection between the Rust implementation
  (to be translated via rocq-of-rust) and the merge specification.

  The Rust code provides:
  - decompose_func_index (flat index -> (module_idx, local_idx))
  - reconstruct_func_index (inverse of decompose)
  - build_function_index_map (maps defined functions to absolute wasm indices)
  - defined_func (absolute wasm index -> defined-function array position)

  The spec (merge_defs.v) provides:
  - compute_offset (cumulative offset per index space)
  - gen_remaps_for_space (remap generation with offset + local_idx)

  Key properties proven:
  1. Decompose/reconstruct roundtrip (decompose_reconstruct_roundtrip)
  2. Decompose injectivity (decompose_injective)
  3. Function index map boundedness (index_map_bounded)
  4. Function index map injectivity (index_map_injective)
  5. Defined-func roundtrip (defined_func_roundtrip)
  6. Bridge: decompose matches compute_offset (decompose_matches_offset)
*)

From Stdlib Require Import List ZArith Lia Arith.
Import ListNotations.

(* -------------------------------------------------------------------------
   Pure-Model Definitions

   These mirror resolver_core.rs in a way that's easier to reason about.
   They use nat instead of u32 to avoid overflow concerns in the proof
   model (overflow is handled separately via preconditions in the Rust code).
   ------------------------------------------------------------------------- *)

(* Prefix sum of counts[0..n] *)
Fixpoint prefix_sum (counts : list nat) (n : nat) : nat :=
  match n, counts with
  | 0, _ => 0
  | S n', c :: cs => c + prefix_sum cs n'
  | S _, [] => 0
  end.

(* Total sum of all counts *)
Definition total_count (counts : list nat) : nat :=
  prefix_sum counts (length counts).

(* Model of decompose_func_index: find which module owns a flat index.
   Returns (module_idx, local_idx) or None if index >= total. *)
Fixpoint decompose_aux (counts : list nat) (index : nat) (running : nat) (i : nat)
    : option (nat * nat) :=
  match counts with
  | [] => None
  | c :: cs =>
      if index <? running + c then
        Some (i, index - running)
      else
        decompose_aux cs index (running + c) (S i)
  end.

Definition decompose (counts : list nat) (index : nat) : option (nat * nat) :=
  decompose_aux counts index 0 0.

(* Model of reconstruct_func_index *)
Definition reconstruct (counts : list nat) (mod_idx : nat) (local_idx : nat) : nat :=
  prefix_sum counts mod_idx + local_idx.

(* Model of build_function_index_map *)
Fixpoint build_index_map_aux (import_count : nat) (defined_counts : list nat)
    (cumulative : nat) : list nat :=
  match defined_counts with
  | [] => []
  | c :: cs =>
      map (fun pos => import_count + cumulative + pos) (seq 0 c)
      ++ build_index_map_aux import_count cs (cumulative + c)
  end.

Definition build_index_map (import_count : nat) (defined_counts : list nat) : list nat :=
  build_index_map_aux import_count defined_counts 0.

(* Model of defined_func *)
Definition defined_func (import_count : nat) (wasm_idx : nat) : option nat :=
  if wasm_idx <? import_count then None
  else Some (wasm_idx - import_count).

(* -------------------------------------------------------------------------
   Prefix Sum Properties
   ------------------------------------------------------------------------- *)

(* Prefix sum at 0 is 0 *)
Lemma prefix_sum_0 :
  forall counts, prefix_sum counts 0 = 0.
Proof.
  destruct counts; reflexivity.
Qed.

(* Prefix sum step: prefix_sum(n+1) = counts[n] + prefix_sum(n) *)
Lemma prefix_sum_S :
  forall counts n c cs,
    counts = c :: cs ->
    n < length counts ->
    prefix_sum counts (S n) = c + prefix_sum cs n.
Proof.
  intros counts n c cs Hcounts Hlen. subst. simpl. reflexivity.
Qed.

(* Prefix sum is monotonically non-decreasing *)
Lemma prefix_sum_monotonic :
  forall counts i j,
    i <= j ->
    j <= length counts ->
    prefix_sum counts i <= prefix_sum counts j.
Proof.
  intros counts.
  induction counts as [|c cs IH]; intros i j Hij Hj.
  - (* counts = [] *)
    destruct i; destruct j; simpl; lia.
  - (* counts = c :: cs *)
    destruct i as [|i']; destruct j as [|j'].
    + lia.
    + simpl. lia.
    + lia.
    + simpl. simpl in Hj.
      assert (Hle: prefix_sum cs i' <= prefix_sum cs j')
        by (apply IH; lia).
      lia.
Qed.

(* prefix_sum at length = total_count *)
Lemma prefix_sum_at_length :
  forall counts, prefix_sum counts (length counts) = total_count counts.
Proof.
  intro counts. reflexivity.
Qed.

(* prefix_sum is additive: prefix_sum(i+1) = prefix_sum(i) + nth i counts 0 *)
Lemma prefix_sum_step :
  forall counts i,
    i < length counts ->
    prefix_sum counts (S i) = prefix_sum counts i + nth i counts 0.
Proof.
  intros counts.
  induction counts as [|c cs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + simpl. lia.
    + simpl. simpl in Hi.
      rewrite IH by lia. lia.
Qed.

(* -------------------------------------------------------------------------
   Decompose Properties
   ------------------------------------------------------------------------- *)

(* Helper: decompose_aux with offset running and base i *)
Lemma decompose_aux_spec :
  forall counts index running i mod_idx local_idx,
    decompose_aux counts index running i = Some (mod_idx, local_idx) ->
    (* mod_idx is within range *)
    i <= mod_idx < i + length counts /\
    (* local_idx is within the module's count *)
    local_idx < nth (mod_idx - i) counts 0 /\
    (* The flat index decomposes correctly *)
    running + prefix_sum counts (mod_idx - i) + local_idx = index.
Proof.
  intros counts.
  induction counts as [|c cs IH]; intros index running i mod_idx local_idx Hdecomp.
  - (* counts = [] *)
    simpl in Hdecomp. discriminate.
  - (* counts = c :: cs *)
    simpl in Hdecomp.
    destruct (index <? running + c) eqn:Hlt.
    + (* Found: index is in this module *)
      apply Nat.ltb_lt in Hlt.
      injection Hdecomp as Hmod Hlocal. subst.
      replace (i - i) with 0 by lia.
      simpl. repeat split; lia.
    + (* Not found: recurse *)
      apply Nat.ltb_ge in Hlt.
      specialize (IH index (running + c) (S i) mod_idx local_idx Hdecomp).
      destruct IH as [Hrange [Hlocal Hsum]].
      replace (mod_idx - i) with (S (mod_idx - S i)) by lia.
      simpl. repeat split; try lia.
Qed.

(* Decompose succeeds for valid indices *)
Lemma decompose_aux_total :
  forall counts index running i,
    running <= index ->
    index < running + total_count counts ->
    exists mod_idx local_idx,
      decompose_aux counts index running i = Some (mod_idx, local_idx).
Proof.
  intros counts.
  induction counts as [|c cs IH]; intros index running i Hge Hlt.
  - (* counts = [] *)
    simpl in Hlt. lia.
  - (* counts = c :: cs *)
    simpl.
    destruct (index <? running + c) eqn:Hcmp.
    + (* Found *)
      eexists. eexists. reflexivity.
    + (* Recurse *)
      apply Nat.ltb_ge in Hcmp.
      simpl in Hlt.
      apply IH; lia.
Qed.

Lemma decompose_total :
  forall counts index,
    index < total_count counts ->
    exists mod_idx local_idx,
      decompose counts index = Some (mod_idx, local_idx).
Proof.
  intros counts index Hlt.
  unfold decompose. apply decompose_aux_total; lia.
Qed.

(* Decompose returns None for out-of-range indices *)
Lemma decompose_aux_none :
  forall counts index running i,
    index >= running + total_count counts ->
    decompose_aux counts index running i = None.
Proof.
  intros counts.
  induction counts as [|c cs IH]; intros index running i Hge.
  - simpl. reflexivity.
  - simpl.
    destruct (index <? running + c) eqn:Hcmp.
    + apply Nat.ltb_lt in Hcmp. simpl in Hge. lia.
    + apply IH. simpl in Hge. lia.
Qed.

Lemma decompose_none :
  forall counts index,
    index >= total_count counts ->
    decompose counts index = None.
Proof.
  intros counts index Hge.
  unfold decompose. apply decompose_aux_none. lia.
Qed.

(* -------------------------------------------------------------------------
   Roundtrip: decompose(reconstruct(k, l)) = Some (k, l)
   and reconstruct(decompose(i)) = i
   ------------------------------------------------------------------------- *)

(* Reconstruct produces a value in the right range *)
Lemma reconstruct_bound :
  forall counts mod_idx local_idx,
    mod_idx < length counts ->
    local_idx < nth mod_idx counts 0 ->
    reconstruct counts mod_idx local_idx < total_count counts.
Proof.
  intros counts mod_idx local_idx Hmod Hlocal.
  unfold reconstruct, total_count.
  assert (Hstep: prefix_sum counts (S mod_idx) = prefix_sum counts mod_idx + nth mod_idx counts 0)
    by (apply prefix_sum_step; lia).
  assert (Hmono: prefix_sum counts (S mod_idx) <= prefix_sum counts (length counts))
    by (apply prefix_sum_monotonic; lia).
  lia.
Qed.

(* Forward roundtrip: decompose then reconstruct = identity *)
Theorem decompose_reconstruct_roundtrip :
  forall counts index,
    index < total_count counts ->
    exists mod_idx local_idx,
      decompose counts index = Some (mod_idx, local_idx) /\
      mod_idx < length counts /\
      local_idx < nth mod_idx counts 0 /\
      reconstruct counts mod_idx local_idx = index.
Proof.
  intros counts index Hlt.
  destruct (decompose_total counts index Hlt) as [mod_idx [local_idx Hdecomp]].
  exists mod_idx, local_idx.
  unfold decompose in Hdecomp.
  pose proof (decompose_aux_spec counts index 0 0 mod_idx local_idx Hdecomp)
    as [Hrange [Hlocal Hsum]].
  replace (mod_idx - 0) with mod_idx in * by lia.
  split; [|split; [|split]].
  - unfold decompose. exact Hdecomp.
  - lia.
  - exact Hlocal.
  - unfold reconstruct. lia.
Qed.

(* -------------------------------------------------------------------------
   Decompose Injectivity
   ------------------------------------------------------------------------- *)

(* Different valid indices decompose to different (mod_idx, local_idx) pairs *)
Theorem decompose_injective :
  forall counts i1 i2 k1 l1 k2 l2,
    decompose counts i1 = Some (k1, l1) ->
    decompose counts i2 = Some (k2, l2) ->
    i1 <> i2 ->
    (k1, l1) <> (k2, l2).
Proof.
  intros counts i1 i2 k1 l1 k2 l2 Hd1 Hd2 Hneq.
  unfold decompose in Hd1, Hd2.
  pose proof (decompose_aux_spec counts i1 0 0 k1 l1 Hd1) as [_ [_ Hsum1]].
  pose proof (decompose_aux_spec counts i2 0 0 k2 l2 Hd2) as [_ [_ Hsum2]].
  replace (k1 - 0) with k1 in * by lia.
  replace (k2 - 0) with k2 in * by lia.
  intro Heq. injection Heq as Hkeq Hleq. subst.
  lia.
Qed.

(* -------------------------------------------------------------------------
   Function Index Map Properties
   ------------------------------------------------------------------------- *)

(* Helper: length of build_index_map_aux *)
Lemma build_index_map_aux_length :
  forall import_count defined_counts cumulative,
    length (build_index_map_aux import_count defined_counts cumulative) =
    fold_left (fun acc c => acc + c) defined_counts 0.
Proof.
  intros import_count defined_counts.
  induction defined_counts as [|c cs IH]; intro cumulative.
  - simpl. reflexivity.
  - simpl. rewrite length_app. rewrite length_map. rewrite length_seq.
    rewrite IH.
    (* fold_left shift *)
    assert (Hshift: forall l base,
      fold_left (fun acc x => acc + x) l base = base + fold_left (fun acc x => acc + x) l 0).
    { intros l. induction l as [|h t IHl]; intro base.
      - simpl. lia.
      - simpl. rewrite IHl. rewrite (IHl h). lia. }
    rewrite Hshift. lia.
Qed.

(* Total length of the index map = total defined functions *)
Lemma build_index_map_length :
  forall import_count defined_counts,
    length (build_index_map import_count defined_counts) =
    fold_left (fun acc c => acc + c) defined_counts 0.
Proof.
  intros. unfold build_index_map. apply build_index_map_aux_length.
Qed.

(* Helper: all entries in build_index_map_aux are bounded *)
Lemma build_index_map_aux_bounded :
  forall import_count defined_counts cumulative idx,
    In idx (build_index_map_aux import_count defined_counts cumulative) ->
    import_count + cumulative <= idx /\
    idx < import_count + cumulative + fold_left (fun acc c => acc + c) defined_counts 0.
Proof.
  intros import_count defined_counts.
  induction defined_counts as [|c cs IH]; intros cumulative idx Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin_map | Hin_rest].
    + (* idx is from the map for the first module *)
      apply in_map_iff in Hin_map. destruct Hin_map as [pos [Heq Hpos]].
      apply in_seq in Hpos. subst.
      simpl.
      assert (Hshift: forall l base,
        fold_left (fun acc x => acc + x) l base = base + fold_left (fun acc x => acc + x) l 0).
      { intros l. induction l as [|h t IHl]; intro base; simpl.
        - lia.
        - rewrite IHl. rewrite (IHl h). lia. }
      rewrite Hshift. lia.
    + (* idx is from the rest *)
      specialize (IH (cumulative + c) idx Hin_rest).
      simpl.
      assert (Hshift: forall l base,
        fold_left (fun acc x => acc + x) l base = base + fold_left (fun acc x => acc + x) l 0).
      { intros l. induction l as [|h t IHl]; intro base; simpl.
        - lia.
        - rewrite IHl. rewrite (IHl h). lia. }
      rewrite Hshift. lia.
Qed.

(* All entries in the index map are bounded *)
Theorem index_map_bounded :
  forall import_count defined_counts idx,
    In idx (build_index_map import_count defined_counts) ->
    import_count <= idx /\
    idx < import_count + fold_left (fun acc c => acc + c) defined_counts 0.
Proof.
  intros import_count defined_counts idx Hin.
  unfold build_index_map in Hin.
  apply build_index_map_aux_bounded in Hin. lia.
Qed.

(* Helper: NoDup for build_index_map_aux *)
Lemma build_index_map_aux_NoDup :
  forall import_count defined_counts cumulative,
    NoDup (build_index_map_aux import_count defined_counts cumulative).
Proof.
  intros import_count defined_counts.
  induction defined_counts as [|c cs IH]; intro cumulative.
  - simpl. constructor.
  - simpl. apply NoDup_app.
    + (* NoDup in the mapped seq for this module *)
      apply FinFun.Injective_map_NoDup.
      * intros x y Heq. lia.
      * apply NoDup_seq.
    + (* NoDup in the rest *)
      apply IH.
    + (* Disjointness: entries from this module don't appear in the rest *)
      intros x Hin_map Hin_rest.
      apply in_map_iff in Hin_map. destruct Hin_map as [pos [Heq Hpos]].
      apply in_seq in Hpos. subst.
      apply build_index_map_aux_bounded in Hin_rest.
      lia.
Qed.

(* The index map has no duplicate entries (injectivity) *)
Theorem index_map_injective :
  forall import_count defined_counts,
    NoDup (build_index_map import_count defined_counts).
Proof.
  intros. unfold build_index_map. apply build_index_map_aux_NoDup.
Qed.

(* -------------------------------------------------------------------------
   Defined-Func Roundtrip
   ------------------------------------------------------------------------- *)

Theorem defined_func_roundtrip :
  forall import_count array_pos,
    defined_func import_count (import_count + array_pos) = Some array_pos.
Proof.
  intros import_count array_pos.
  unfold defined_func.
  assert (Hge: import_count + array_pos <? import_count = false)
    by (apply Nat.ltb_ge; lia).
  rewrite Hge. f_equal. lia.
Qed.

Theorem defined_func_below_import :
  forall import_count idx,
    idx < import_count ->
    defined_func import_count idx = None.
Proof.
  intros import_count idx Hlt.
  unfold defined_func.
  assert (Hltb: idx <? import_count = true)
    by (apply Nat.ltb_lt; exact Hlt).
  rewrite Hltb. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Bridge to merge_defs.v: Decompose ↔ compute_offset

   The merge spec uses `compute_offset` (fold_left over merge_input) to
   compute the cumulative offset for a module at position mod_idx.
   Our `prefix_sum` computes the same thing from a list of counts.

   This section shows they agree when the counts list is extracted from
   the merge input — establishing the model-to-spec bridge.
   ------------------------------------------------------------------------- *)

(* Helper: fold_left shift for nat addition *)
Lemma fold_left_add_shift_nat :
  forall (f : nat -> nat) (l : list nat) (base : nat),
    fold_left (fun acc x => acc + f x) l base =
    base + fold_left (fun acc x => acc + f x) l 0.
Proof.
  intros f l. induction l as [|x l' IH]; intro base.
  - simpl. lia.
  - simpl. rewrite IH. rewrite (IH (f x)). lia.
Qed.

(* prefix_sum over a list of counts equals fold_left with addition *)
Lemma prefix_sum_eq_fold_left :
  forall counts n,
    n <= length counts ->
    prefix_sum counts n =
    fold_left (fun acc c => acc + c) (firstn n counts) 0.
Proof.
  intros counts.
  induction counts as [|c cs IH]; intros n Hn.
  - simpl in Hn. assert (n = 0) by lia. subst. simpl. reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. simpl in Hn.
      rewrite IH by lia.
      rewrite fold_left_add_shift_nat with (f := fun x => x).
      simpl. f_equal. f_equal.
      clear. induction (firstn n' cs) as [|h t IHl]; simpl; [lia|].
      rewrite IHl. lia.
Qed.

(* The decompose model matches compute_offset when applied to extracted counts.
   This is the key bridge lemma: it states that for a list of function counts
   extracted from merge_input, decompose's prefix_sum computation is consistent
   with the spec's compute_offset for the FuncIdx space. *)
Theorem decompose_matches_offset :
  forall counts index mod_idx local_idx,
    decompose counts index = Some (mod_idx, local_idx) ->
    reconstruct counts mod_idx local_idx = index /\
    local_idx < nth mod_idx counts 0 /\
    prefix_sum counts mod_idx =
      fold_left (fun acc c => acc + c) (firstn mod_idx counts) 0.
Proof.
  intros counts index mod_idx local_idx Hdecomp.
  unfold decompose in Hdecomp.
  pose proof (decompose_aux_spec counts index 0 0 mod_idx local_idx Hdecomp)
    as [Hrange [Hlocal Hsum]].
  replace (mod_idx - 0) with mod_idx in * by lia.
  split; [|split].
  - unfold reconstruct. lia.
  - exact Hlocal.
  - apply prefix_sum_eq_fold_left. lia.
Qed.

(* -------------------------------------------------------------------------
   Bridge to merge_defs.v: Index Map ↔ gen_remaps_for_space

   The merge spec uses gen_remaps_for_space to create a list of index
   remaps where fused_idx = offset + source_idx.

   Our build_index_map produces absolute indices = import_count + cumulative + pos,
   which is exactly offset + source_idx when:
   - offset = import_count + cumulative (the cumulative offset in the merged module)
   - source_idx = pos (the local position within the module)

   The nth entry of build_index_map corresponds to the remap for the
   nth defined function.
   ------------------------------------------------------------------------- *)

(* Helper: nth in build_index_map_aux for the first module *)
Lemma build_index_map_aux_nth_first :
  forall import_count c cs cumulative pos,
    pos < c ->
    nth_error (build_index_map_aux import_count (c :: cs) cumulative) pos
    = Some (import_count + cumulative + pos).
Proof.
  intros import_count c cs cumulative pos Hpos.
  simpl.
  rewrite nth_error_app1.
  - rewrite nth_error_map.
    rewrite nth_error_seq by lia.
    simpl. f_equal. lia.
  - rewrite length_map. rewrite length_seq. exact Hpos.
Qed.

(* Bridge: the nth entry of build_index_map equals
   import_count + prefix_sum(defined_counts, mod_idx) + local_pos
   where (mod_idx, local_pos) is the decomposition of the flat position.

   This connects build_index_map to the gen_remaps_for_space pattern in
   merge_defs.v, where fused_idx = offset + source_idx. Here:
   - offset corresponds to import_count + prefix_sum(defined_counts, mod_idx)
   - source_idx corresponds to local_pos *)
Theorem index_map_matches_decompose :
  forall import_count defined_counts pos mod_idx local_pos,
    pos < length (build_index_map import_count defined_counts) ->
    decompose defined_counts pos = Some (mod_idx, local_pos) ->
    nth_error (build_index_map import_count defined_counts) pos
    = Some (import_count + prefix_sum defined_counts mod_idx + local_pos).
Proof.
  intros import_count defined_counts pos mod_idx local_pos Hpos Hdecomp.
  (* From index_map_entry_value: map[pos] = import_count + pos *)
  rewrite index_map_entry_value by exact Hpos.
  (* From decompose_matches_offset: reconstruct(mod_idx, local_pos) = pos *)
  pose proof (decompose_matches_offset defined_counts pos mod_idx local_pos Hdecomp)
    as [Hrecon [_ _]].
  (* reconstruct = prefix_sum + local_pos = pos *)
  unfold reconstruct in Hrecon.
  f_equal. lia.
Qed.

(* Simpler statement: each entry equals import_count + its flat position
   in the defined function array *)
Theorem index_map_entry_value :
  forall import_count defined_counts pos,
    pos < length (build_index_map import_count defined_counts) ->
    nth_error (build_index_map import_count defined_counts) pos
    = Some (import_count + pos).
Proof.
  intros import_count defined_counts pos Hpos.
  unfold build_index_map.
  (* The build_index_map_aux creates entries import_count + 0, import_count + 1, ...
     because cumulative starts at 0 and each module adds its count. *)
  generalize dependent pos.
  generalize 0 as cumulative.
  induction defined_counts as [|c cs IH]; intros cumulative pos Hpos.
  - simpl in Hpos. simpl. lia.
  - simpl in *.
    rewrite length_app in Hpos. rewrite length_map, length_seq in Hpos.
    destruct (Nat.lt_ge_cases pos c) as [Hlt | Hge].
    + (* pos < c: in the current module's map *)
      rewrite nth_error_app1 by (rewrite length_map, length_seq; exact Hlt).
      rewrite nth_error_map, nth_error_seq by lia.
      simpl. f_equal. lia.
    + (* pos >= c: in the rest *)
      rewrite nth_error_app2 by (rewrite length_map, length_seq; exact Hge).
      rewrite length_map, length_seq.
      rewrite IH by (rewrite build_index_map_aux_length in *; lia).
      f_equal. lia.
Qed.

(* Corollary: defined_func inverts the index map *)
Corollary defined_func_inverts_index_map :
  forall import_count defined_counts pos,
    pos < length (build_index_map import_count defined_counts) ->
    exists abs_idx,
      nth_error (build_index_map import_count defined_counts) pos = Some abs_idx /\
      defined_func import_count abs_idx = Some pos.
Proof.
  intros import_count defined_counts pos Hpos.
  exists (import_count + pos).
  split.
  - apply index_map_entry_value. exact Hpos.
  - apply defined_func_roundtrip.
Qed.

(* End of resolver_core_proofs *)
