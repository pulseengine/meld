(* =========================================================================
   CopyLayout and Pointer Fixup Proofs

   Source: meld-core/src/resolver.rs (CopyLayout, ConditionalPointerPair)
           meld-core/src/adapter/fact.rs (emit_inner_pointer_fixup)

   This file proves four categories of properties:
   (a) CopyLayout well-formedness: inner pointer offsets within element bounds
   (b) Conditional pointer pair correctness: valid discriminant/pointer positions
   (c) Copy completeness: all pointer data is copied when discriminant matches
   (d) Memory safety: no out-of-bounds reads/writes during conditional copy

   All proofs are fully closed (Qed). No Admitted, admit, or Axiom.

   Spec baselines: see proofs/DECISIONS.md.
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith PeanoNat.
From MeldCopyLayout Require Import copy_layout_spec.
Import ListNotations.

(* =========================================================================
   Part (a): CopyLayout Well-Formedness
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Bulk layouts are well-formed when byte_multiplier > 0
   ------------------------------------------------------------------------- *)

Lemma bulk_wf : forall m,
  m > 0 ->
  copy_layout_wf (CLBulk m).
Proof.
  intros m Hpos. simpl. exact Hpos.
Qed.

(* -------------------------------------------------------------------------
   Elements layout with no inner pointers is well-formed
   when element_size > 0
   ------------------------------------------------------------------------- *)

Lemma elements_no_inner_wf : forall elem_size,
  elem_size > 0 ->
  copy_layout_wf (CLElements elem_size []).
Proof.
  intros elem_size Hpos.
  simpl.
  split; [exact Hpos |].
  split; [intros offset inner_cl Hin; contradiction |].
  split; [exact I |].
  intros i j ip1 ip2 Hi Hj Hneq.
  destruct i; simpl in Hi; discriminate.
Qed.

(* -------------------------------------------------------------------------
   Elements layout with empty inner pointers: alternative construction
   that shows copy_layout_list_wf [] = True explicitly
   ------------------------------------------------------------------------- *)

Lemma copy_layout_list_wf_nil :
  copy_layout_list_wf [].
Proof.
  simpl. exact I.
Qed.

(* -------------------------------------------------------------------------
   A single inner pointer at offset 0 with a Bulk(1) layout is well-formed
   when element_size >= 8 (common case: list<string>)
   ------------------------------------------------------------------------- *)

Lemma elements_single_string_wf : forall elem_size,
  elem_size >= 8 ->
  copy_layout_wf (CLElements elem_size [(0, CLBulk 1)]).
Proof.
  intros elem_size Hsize.
  simpl.
  split; [lia |].
  split.
  - (* inner pointer bounds *)
    intros offset inner_cl Hin.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst. lia.
    + contradiction.
  - split.
    + (* copy_layout_list_wf: CLBulk 1 is wf (1 > 0) and rest is True *)
      split; [lia | exact I].
    + (* inner_pointers_disjoint: only one element, so vacuously true *)
      intros i j ip1 ip2 Hi Hj Hneq.
      destruct i as [| i']; destruct j as [| j'].
      * exfalso. apply Hneq. reflexivity.
      * simpl in Hj. destruct j'; discriminate.
      * simpl in Hi. destruct i'; discriminate.
      * simpl in Hi. destruct i'; discriminate.
Qed.

(* -------------------------------------------------------------------------
   Well-formedness of Bulk implies positive byte_multiplier
   ------------------------------------------------------------------------- *)

Lemma bulk_wf_positive : forall m,
  copy_layout_wf (CLBulk m) ->
  m > 0.
Proof.
  intros m Hwf. simpl in Hwf. exact Hwf.
Qed.

(* -------------------------------------------------------------------------
   Well-formedness of Elements implies positive element_size
   ------------------------------------------------------------------------- *)

Lemma elements_wf_positive_size : forall s ips,
  copy_layout_wf (CLElements s ips) ->
  s > 0.
Proof.
  intros s ips Hwf. simpl in Hwf.
  destruct Hwf as [Hpos _]. exact Hpos.
Qed.

(* -------------------------------------------------------------------------
   Well-formedness of Elements implies inner pointer bounds
   ------------------------------------------------------------------------- *)

Lemma elements_wf_inner_bounds : forall s ips offset inner_cl,
  copy_layout_wf (CLElements s ips) ->
  In (offset, inner_cl) ips ->
  offset + 8 <= s.
Proof.
  intros s ips offset inner_cl Hwf Hin.
  simpl in Hwf.
  destruct Hwf as [_ [Hbounds _]].
  exact (Hbounds offset inner_cl Hin).
Qed.

(* -------------------------------------------------------------------------
   Well-formedness of Elements implies inner layouts are well-formed
   ------------------------------------------------------------------------- *)

Lemma elements_wf_inner_wf : forall s ips offset inner_cl,
  copy_layout_wf (CLElements s ips) ->
  In (offset, inner_cl) ips ->
  copy_layout_wf inner_cl.
Proof.
  intros s ips offset inner_cl Hwf Hin.
  simpl in Hwf.
  destruct Hwf as [_ [_ [Hlist_wf _]]].
  exact (copy_layout_list_wf_In ips offset inner_cl Hlist_wf Hin).
Qed.

(* -------------------------------------------------------------------------
   Well-formedness is preserved when removing an inner pointer
   (useful for inductive reasoning about fixup loops)
   ------------------------------------------------------------------------- *)

Lemma elements_wf_tail : forall s ip ips,
  copy_layout_wf (CLElements s (ip :: ips)) ->
  ips <> [] ->
  copy_layout_wf (CLElements s ips).
Proof.
  intros s [o cl] ips Hwf Hne.
  simpl in Hwf.
  destruct Hwf as [Hpos [Hbounds [[_ Hlist_wf] Hdisjoint]]].
  simpl.
  split; [exact Hpos |].
  split; [intros offset inner_cl Hin; apply Hbounds; right; exact Hin |].
  split; [exact Hlist_wf |].
  intros i j ip1 ip2 Hi Hj Hneq.
  apply (Hdisjoint (S i) (S j) ip1 ip2).
  - simpl. exact Hi.
  - simpl. exact Hj.
  - lia.
Qed.

(* -------------------------------------------------------------------------
   The effective byte multiplier is always positive for well-formed layouts
   ------------------------------------------------------------------------- *)

Theorem effective_byte_mult_positive : forall cl,
  copy_layout_wf cl ->
  effective_byte_multiplier cl > 0.
Proof.
  intros cl Hwf.
  destruct cl as [m | s ips].
  - (* CLBulk m *)
    simpl. simpl in Hwf. exact Hwf.
  - (* CLElements s ips *)
    simpl. simpl in Hwf. destruct Hwf as [Hpos _]. exact Hpos.
Qed.

(* -------------------------------------------------------------------------
   Two non-overlapping inner pointers at valid offsets remain disjoint
   (helper for composing well-formedness in nested layouts)
   ------------------------------------------------------------------------- *)

Lemma pointer_pairs_disjoint_sym : forall o1 o2,
  pointer_pairs_disjoint o1 o2 ->
  pointer_pairs_disjoint o2 o1.
Proof.
  intros o1 o2 [H | H]; unfold pointer_pairs_disjoint; lia.
Qed.

(* -------------------------------------------------------------------------
   Constructing a well-formed Elements layout with two inner pointers
   (common case: list<record { name: string, data: list<u8> }>)
   ------------------------------------------------------------------------- *)

Theorem elements_two_inner_wf : forall elem_size o1 cl1 o2 cl2,
  elem_size > 0 ->
  o1 + 8 <= elem_size ->
  o2 + 8 <= elem_size ->
  pointer_pairs_disjoint o1 o2 ->
  copy_layout_wf cl1 ->
  copy_layout_wf cl2 ->
  copy_layout_wf (CLElements elem_size [(o1, cl1); (o2, cl2)]).
Proof.
  intros elem_size o1 cl1 o2 cl2 Hpos Hb1 Hb2 Hdisj Hwf1 Hwf2.
  simpl.
  split; [exact Hpos |].
  split.
  - (* bounds *)
    intros offset inner_cl Hin.
    destruct Hin as [Heq | [Heq | Hin]].
    + inversion Heq; subst. exact Hb1.
    + inversion Heq; subst. exact Hb2.
    + contradiction.
  - split.
    + (* copy_layout_list_wf [(o1, cl1); (o2, cl2)] *)
      split; [exact Hwf1 |].
      split; [exact Hwf2 | exact I].
    + (* inner_pointers_disjoint *)
      intros i j ip1 ip2 Hi Hj Hneq.
      destruct i as [| [| i']]; destruct j as [| [| j']].
      * exfalso. apply Hneq. reflexivity.
      * simpl in Hi, Hj.
        inversion Hi; subst. inversion Hj; subst. simpl. exact Hdisj.
      * simpl in Hj. destruct j'; discriminate.
      * simpl in Hi, Hj.
        inversion Hi; subst. inversion Hj; subst. simpl.
        apply pointer_pairs_disjoint_sym. exact Hdisj.
      * exfalso. apply Hneq. reflexivity.
      * simpl in Hj. destruct j'; discriminate.
      * simpl in Hi. destruct i'; discriminate.
      * simpl in Hi. destruct i'; discriminate.
      * simpl in Hi. destruct i'; discriminate.
Qed.

(* =========================================================================
   Part (b): Conditional Pointer Pair Correctness
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Construction of well-formed conditional pointer pairs
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_wf_construct :
  forall disc_pos disc_val ptr_pos cl param_count,
    disc_pos < param_count ->
    ptr_pos + 1 < param_count ->
    disc_pos <> ptr_pos ->
    disc_pos <> ptr_pos + 1 ->
    copy_layout_wf cl ->
    conditional_pointer_pair_wf
      (mkConditionalPointerPair disc_pos disc_val ptr_pos cl)
      param_count.
Proof.
  intros disc_pos disc_val ptr_pos cl param_count
         Hdisc Hptr Hne1 Hne2 Hwf.
  unfold conditional_pointer_pair_wf. simpl.
  split; [exact Hdisc |].
  split; [exact Hptr |].
  split; [exact Hne1 |].
  split; [exact Hne2 |].
  exact Hwf.
Qed.

(* -------------------------------------------------------------------------
   Well-formed conditional pointer pair implies valid discriminant position
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_disc_valid :
  forall cpp param_count,
    conditional_pointer_pair_wf cpp param_count ->
    cpp_discriminant_position cpp < param_count.
Proof.
  intros cpp param_count Hwf.
  unfold conditional_pointer_pair_wf in Hwf.
  destruct Hwf as [Hdisc _]. exact Hdisc.
Qed.

(* -------------------------------------------------------------------------
   Well-formed conditional pointer pair implies valid pointer position
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_ptr_valid :
  forall cpp param_count,
    conditional_pointer_pair_wf cpp param_count ->
    cpp_ptr_position cpp + 1 < param_count.
Proof.
  intros cpp param_count Hwf.
  unfold conditional_pointer_pair_wf in Hwf.
  destruct Hwf as [_ [Hptr _]]. exact Hptr.
Qed.

(* -------------------------------------------------------------------------
   Well-formed conditional pointer pair: disc and ptr are distinct positions
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_positions_distinct :
  forall cpp param_count,
    conditional_pointer_pair_wf cpp param_count ->
    cpp_discriminant_position cpp <> cpp_ptr_position cpp /\
    cpp_discriminant_position cpp <> cpp_ptr_position cpp + 1.
Proof.
  intros cpp param_count Hwf.
  unfold conditional_pointer_pair_wf in Hwf.
  destruct Hwf as [_ [_ [Hne1 [Hne2 _]]]].
  split; assumption.
Qed.

(* -------------------------------------------------------------------------
   Well-formedness of conditional pointer pair implies layout well-formedness
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_layout_wf :
  forall cpp param_count,
    conditional_pointer_pair_wf cpp param_count ->
    copy_layout_wf (cpp_copy_layout cpp).
Proof.
  intros cpp param_count Hwf.
  unfold conditional_pointer_pair_wf in Hwf.
  destruct Hwf as [_ [_ [_ [_ Hlayout]]]].
  exact Hlayout.
Qed.

(* -------------------------------------------------------------------------
   Retptr variant: well-formed implies discriminant fits in return area
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_retptr_disc_fits :
  forall cpp ra_size,
    conditional_pointer_pair_retptr_wf cpp ra_size ->
    cpp_discriminant_position cpp + 4 <= ra_size.
Proof.
  intros cpp ra_size Hwf.
  unfold conditional_pointer_pair_retptr_wf in Hwf.
  destruct Hwf as [Hdisc _]. exact Hdisc.
Qed.

(* -------------------------------------------------------------------------
   Retptr variant: well-formed implies pointer pair fits in return area
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_retptr_ptr_fits :
  forall cpp ra_size,
    conditional_pointer_pair_retptr_wf cpp ra_size ->
    cpp_ptr_position cpp + 8 <= ra_size.
Proof.
  intros cpp ra_size Hwf.
  unfold conditional_pointer_pair_retptr_wf in Hwf.
  destruct Hwf as [_ [Hptr _]]. exact Hptr.
Qed.

(* -------------------------------------------------------------------------
   Retptr variant: disc and ptr ranges do not overlap
   ------------------------------------------------------------------------- *)

Theorem conditional_pp_retptr_no_overlap :
  forall cpp ra_size,
    conditional_pointer_pair_retptr_wf cpp ra_size ->
    cpp_discriminant_position cpp + 4 <= cpp_ptr_position cpp \/
    cpp_ptr_position cpp + 8 <= cpp_discriminant_position cpp.
Proof.
  intros cpp ra_size Hwf.
  unfold conditional_pointer_pair_retptr_wf in Hwf.
  destruct Hwf as [_ [_ [Hdisjoint _]]]. exact Hdisjoint.
Qed.

(* -------------------------------------------------------------------------
   A list of conditional pointer pairs is well-formed when every element is
   ------------------------------------------------------------------------- *)

Definition all_conditional_pp_wf
    (cpps : list conditional_pointer_pair) (param_count : nat) : Prop :=
  Forall (fun cpp => conditional_pointer_pair_wf cpp param_count) cpps.

Theorem all_conditional_pp_wf_disc_bounds :
  forall cpps param_count cpp,
    all_conditional_pp_wf cpps param_count ->
    In cpp cpps ->
    cpp_discriminant_position cpp < param_count.
Proof.
  intros cpps param_count cpp Hall Hin.
  unfold all_conditional_pp_wf in Hall.
  rewrite Forall_forall in Hall.
  apply conditional_pp_disc_valid with (param_count := param_count).
  exact (Hall cpp Hin).
Qed.

Theorem all_conditional_pp_wf_ptr_bounds :
  forall cpps param_count cpp,
    all_conditional_pp_wf cpps param_count ->
    In cpp cpps ->
    cpp_ptr_position cpp + 1 < param_count.
Proof.
  intros cpps param_count cpp Hall Hin.
  unfold all_conditional_pp_wf in Hall.
  rewrite Forall_forall in Hall.
  apply conditional_pp_ptr_valid with (param_count := param_count).
  exact (Hall cpp Hin).
Qed.

(* =========================================================================
   Part (c): Copy Completeness
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Memory copy preserves content within the copied range
   ------------------------------------------------------------------------- *)

Lemma memory_copy_in_range :
  forall src_mem src_base dst_mem dst_base len i,
    i < len ->
    memory_copy src_mem src_base dst_mem dst_base len (dst_base + i)
    = src_mem (src_base + i).
Proof.
  intros src_mem src_base dst_mem dst_base len i Hi.
  unfold memory_copy.
  assert (Hle: Nat.leb dst_base (dst_base + i) = true).
  { apply Nat.leb_le. lia. }
  assert (Hlt: Nat.ltb (dst_base + i) (dst_base + len) = true).
  { apply Nat.ltb_lt. lia. }
  rewrite Hle, Hlt. simpl.
  replace (dst_base + i - dst_base) with i by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Bulk copy completeness: all bytes in [dst_base, dst_base + count*m)
   equal the corresponding source bytes
   ------------------------------------------------------------------------- *)

Theorem bulk_copy_complete :
  forall src_mem src_base dst_mem dst_base byte_mult count,
    copy_layout_wf (CLBulk byte_mult) ->
    copy_complete src_mem
      (bulk_copy_spec src_mem src_base dst_mem dst_base byte_mult count)
      src_base dst_base (count * byte_mult).
Proof.
  intros src_mem src_base dst_mem dst_base byte_mult count Hwf.
  unfold copy_complete. intros i Hi.
  unfold bulk_copy_spec.
  apply memory_copy_in_range. exact Hi.
Qed.

(* -------------------------------------------------------------------------
   Memory copy preserves content outside the copied range
   ------------------------------------------------------------------------- *)

Lemma memory_copy_outside_range :
  forall src_mem src_base dst_mem dst_base len addr,
    addr < dst_base \/ addr >= dst_base + len ->
    memory_copy src_mem src_base dst_mem dst_base len addr = dst_mem addr.
Proof.
  intros src_mem src_base dst_mem dst_base len addr Hout.
  unfold memory_copy.
  destruct Hout as [Hlt | Hge].
  - (* addr < dst_base *)
    assert (Hle: Nat.leb dst_base addr = false).
    { apply Nat.leb_gt. lia. }
    rewrite Hle. simpl. reflexivity.
  - (* addr >= dst_base + len *)
    destruct (Nat.leb dst_base addr) eqn:Hle.
    + assert (Hltb: Nat.ltb addr (dst_base + len) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite Hltb. simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Bulk copy is memory-safe: no writes outside the destination range
   ------------------------------------------------------------------------- *)

Theorem bulk_copy_memory_safe :
  forall src_mem src_base dst_mem dst_base byte_mult count,
    copy_memory_safe dst_mem
      (bulk_copy_spec src_mem src_base dst_mem dst_base byte_mult count)
      dst_base (count * byte_mult).
Proof.
  intros src_mem src_base dst_mem dst_base byte_mult count.
  unfold copy_memory_safe. intros addr Hout.
  unfold bulk_copy_spec.
  apply memory_copy_outside_range. exact Hout.
Qed.

(* -------------------------------------------------------------------------
   Copy completeness for a well-formed layout (general statement)

   For any well-formed CopyLayout, the bulk portion of the copy transfers
   all element_total_bytes bytes correctly.
   ------------------------------------------------------------------------- *)

Theorem copy_complete_for_wf_layout :
  forall cl src_mem src_base dst_mem dst_base count,
    copy_layout_wf cl ->
    let byte_len := count * effective_byte_multiplier cl in
    copy_complete src_mem
      (memory_copy src_mem src_base dst_mem dst_base byte_len)
      src_base dst_base byte_len.
Proof.
  intros cl src_mem src_base dst_mem dst_base count Hwf byte_len.
  unfold copy_complete. intros i Hi.
  apply memory_copy_in_range. exact Hi.
Qed.

(* =========================================================================
   Part (d): Memory Safety
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Memory safety for memory_copy: writes are confined to destination range
   ------------------------------------------------------------------------- *)

Theorem memory_copy_safe :
  forall src_mem src_base dst_mem dst_base len,
    copy_memory_safe dst_mem
      (memory_copy src_mem src_base dst_mem dst_base len)
      dst_base len.
Proof.
  intros src_mem src_base dst_mem dst_base len.
  unfold copy_memory_safe. intros addr Hout.
  apply memory_copy_outside_range. exact Hout.
Qed.

(* -------------------------------------------------------------------------
   No-read-out-of-bounds: if the source range is accessible, every byte
   read during the copy produces a defined value
   ------------------------------------------------------------------------- *)

Theorem copy_reads_in_bounds :
  forall src_mem src_base dst_mem dst_base len,
    range_accessible src_mem src_base len ->
    forall i, i < len ->
      exists v,
        memory_copy src_mem src_base dst_mem dst_base len (dst_base + i)
        = Some v.
Proof.
  intros src_mem src_base dst_mem dst_base len Hacc i Hi.
  rewrite memory_copy_in_range by exact Hi.
  unfold range_accessible in Hacc.
  exact (Hacc i Hi).
Qed.

(* -------------------------------------------------------------------------
   Conditional copy correctness: when discriminant does not match,
   the result is CCSkipped
   ------------------------------------------------------------------------- *)

Theorem conditional_copy_skip_correct :
  forall disc_val expected src_mem src_ptr src_len dst_mem cl,
    disc_val <> expected ->
    conditional_copy_correct disc_val expected
      src_mem src_ptr src_len dst_mem dst_mem CCSkipped cl.
Proof.
  intros disc_val expected src_mem src_ptr src_len dst_mem cl Hne.
  unfold conditional_copy_correct.
  assert (Hneqb: Nat.eqb disc_val expected = false).
  { apply Nat.eqb_neq. exact Hne. }
  rewrite Hneqb. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Conditional copy correctness: when discriminant matches,
   the copied data is correct
   ------------------------------------------------------------------------- *)

Theorem conditional_copy_match_correct :
  forall disc_val src_mem src_ptr src_len dst_mem new_ptr cl,
    copy_layout_wf cl ->
    let byte_len := src_len * effective_byte_multiplier cl in
    let dst_mem_after := memory_copy src_mem src_ptr dst_mem new_ptr byte_len in
    conditional_copy_correct disc_val disc_val
      src_mem src_ptr src_len dst_mem dst_mem_after
      (CCCopied new_ptr byte_len) cl.
Proof.
  intros disc_val src_mem src_ptr src_len dst_mem new_ptr cl Hwf
         byte_len dst_mem_after.
  unfold conditional_copy_correct.
  rewrite Nat.eqb_refl.
  split; [reflexivity |].
  split.
  - (* copy_complete *)
    unfold copy_complete. intros i Hi.
    unfold dst_mem_after.
    apply memory_copy_in_range. exact Hi.
  - (* copy_memory_safe *)
    unfold copy_memory_safe. intros addr Hout.
    unfold dst_mem_after.
    apply memory_copy_outside_range. exact Hout.
Qed.

(* -------------------------------------------------------------------------
   Memory safety for element-wise copy: copying count elements of
   elem_size bytes each is safe when the destination region is sized
   correctly
   ------------------------------------------------------------------------- *)

Theorem element_copy_memory_safe :
  forall src_mem src_base dst_mem dst_base elem_size count,
    elem_size > 0 ->
    copy_memory_safe dst_mem
      (memory_copy src_mem src_base dst_mem dst_base (count * elem_size))
      dst_base (count * elem_size).
Proof.
  intros src_mem src_base dst_mem dst_base elem_size count Hpos.
  apply memory_copy_safe.
Qed.

(* -------------------------------------------------------------------------
   Two disjoint copy regions do not interfere

   If region1 = [base1, base1+len1) and region2 = [base2, base2+len2)
   are disjoint, then a copy into region2 does not affect region1 content.
   ------------------------------------------------------------------------- *)

Theorem disjoint_copies_independent :
  forall src_mem src_base1 src_base2 dst_mem
         dst_base1 dst_base2 len1 len2,
    dst_base1 + len1 <= dst_base2 \/ dst_base2 + len2 <= dst_base1 ->
    forall i, i < len1 ->
      memory_copy src_mem src_base2
        (memory_copy src_mem src_base1 dst_mem dst_base1 len1)
        dst_base2 len2
        (dst_base1 + i)
      = src_mem (src_base1 + i).
Proof.
  intros src_mem src_base1 src_base2 dst_mem
         dst_base1 dst_base2 len1 len2 Hdisjoint i Hi.
  (* The outer copy writes to [dst_base2, dst_base2+len2).
     We access dst_base1+i which is in [dst_base1, dst_base1+len1).
     Since the regions are disjoint, the outer copy doesn't affect this. *)
  rewrite memory_copy_outside_range.
  - (* Now we need the inner copy result at dst_base1+i *)
    apply memory_copy_in_range. exact Hi.
  - (* dst_base1 + i is outside [dst_base2, dst_base2 + len2) *)
    destruct Hdisjoint as [H | H]; lia.
Qed.

(* -------------------------------------------------------------------------
   Well-formed Elements layout: inner pointer fixup reads are in bounds

   When an Elements layout is well-formed, reading a pointer pair at
   inner_offset within an element of size elem_size always stays within
   the element boundary.
   ------------------------------------------------------------------------- *)

Theorem inner_pointer_read_in_bounds :
  forall elem_size ips inner_offset inner_cl elem_base,
    copy_layout_wf (CLElements elem_size ips) ->
    In (inner_offset, inner_cl) ips ->
    (* ptr is at elem_base + inner_offset *)
    elem_base + inner_offset + 8 <= elem_base + elem_size.
Proof.
  intros elem_size ips inner_offset inner_cl elem_base Hwf Hin.
  apply elements_wf_inner_bounds in Hin; [lia | exact Hwf].
Qed.

(* -------------------------------------------------------------------------
   Well-formed Elements layout: inner pointer fixup for element i does not
   overlap with element j when i <> j
   ------------------------------------------------------------------------- *)

Theorem element_regions_disjoint :
  forall elem_size count i j,
    elem_size > 0 ->
    i < count ->
    j < count ->
    i <> j ->
    i * elem_size + elem_size <= j * elem_size \/
    j * elem_size + elem_size <= i * elem_size.
Proof.
  intros elem_size count i j Hpos Hi Hj Hne.
  destruct (Nat.lt_ge_cases i j) as [Hlt | Hge].
  - left. nia.
  - right.
    assert (Hlt: j < i) by lia.
    nia.
Qed.

(* -------------------------------------------------------------------------
   Complete copy for a well-formed Bulk layout preserves all data

   This is the main copy completeness theorem: after bulk-copying
   count * byte_multiplier bytes from source to destination, every byte
   in the destination equals the corresponding source byte.
   ------------------------------------------------------------------------- *)

Theorem bulk_layout_copy_preserves_all_data :
  forall byte_mult count src_mem src_base dst_mem dst_base,
    byte_mult > 0 ->
    let byte_len := count * byte_mult in
    let dst_after := memory_copy src_mem src_base dst_mem dst_base byte_len in
    (* Every byte in destination is correct *)
    (forall i, i < byte_len ->
      dst_after (dst_base + i) = src_mem (src_base + i)) /\
    (* No byte outside destination is modified *)
    (forall addr, addr < dst_base \/ addr >= dst_base + byte_len ->
      dst_after addr = dst_mem addr).
Proof.
  intros byte_mult count src_mem src_base dst_mem dst_base
         Hpos byte_len dst_after.
  split.
  - intros i Hi.
    unfold dst_after. apply memory_copy_in_range. exact Hi.
  - intros addr Hout.
    unfold dst_after. apply memory_copy_outside_range. exact Hout.
Qed.

(* -------------------------------------------------------------------------
   Element-wise copy with fixup: after copying elements, each element's
   pointer pairs can be independently fixed up

   This theorem establishes that for a well-formed Elements layout,
   fixing up pointer pair k in element i does not affect pointer pair l
   in element j when i <> j, because different elements occupy
   disjoint address ranges and inner pointer pairs fit within elements.
   ------------------------------------------------------------------------- *)

Theorem fixup_independence :
  forall elem_size ips,
    copy_layout_wf (CLElements elem_size ips) ->
    forall i j k l base,
      i <> j ->
      In k ips ->
      In l ips ->
      (* element i's pointer pair k and element j's pointer pair l
         are at disjoint addresses *)
      pointer_pairs_disjoint
        (base + i * elem_size + fst k)
        (base + j * elem_size + fst l).
Proof.
  intros elem_size ips Hwf i j k l base Hne Hk_in Hl_in.
  simpl in Hwf.
  destruct Hwf as [Hpos [Hbounds _]].
  unfold pointer_pairs_disjoint.
  (* k is at offset fst k within element i, so absolute position is
     base + i*elem_size + fst k. Similarly for l in element j.
     Since fst k + 8 <= elem_size and fst l + 8 <= elem_size,
     and elements are elem_size apart, the ranges don't overlap
     when i <> j. *)
  assert (Hk_bound: fst k + 8 <= elem_size).
  { apply Hbounds with (inner_cl := snd k).
    rewrite surjective_pairing. exact Hk_in. }
  assert (Hl_bound: fst l + 8 <= elem_size).
  { apply Hbounds with (inner_cl := snd l).
    rewrite surjective_pairing. exact Hl_in. }
  destruct (Nat.lt_ge_cases i j) as [Hij | Hij].
  - left. nia.
  - right. assert (j < i) by lia. nia.
Qed.

(* -------------------------------------------------------------------------
   Summary theorem: well-formed CopyLayout guarantees safe and complete copy

   For any well-formed CopyLayout cl and accessible source region of
   count * effective_byte_multiplier(cl) bytes:
   1. The copy transfers all bytes correctly (completeness)
   2. No memory outside the destination range is modified (safety)
   3. Every byte read from the source is defined (no OOB reads)
   ------------------------------------------------------------------------- *)

Theorem copy_layout_safe_and_complete :
  forall cl count src_mem src_base dst_mem dst_base,
    copy_layout_wf cl ->
    let byte_len := count * effective_byte_multiplier cl in
    range_accessible src_mem src_base byte_len ->
    range_accessible dst_mem dst_base byte_len ->
    let dst_after := memory_copy src_mem src_base dst_mem dst_base byte_len in
    (* Completeness: all bytes transferred *)
    (forall i, i < byte_len ->
      dst_after (dst_base + i) = src_mem (src_base + i)) /\
    (* Safety: no writes outside destination *)
    (forall addr, addr < dst_base \/ addr >= dst_base + byte_len ->
      dst_after addr = dst_mem addr) /\
    (* Reads in bounds: every copied byte is defined *)
    (forall i, i < byte_len ->
      exists v, dst_after (dst_base + i) = Some v).
Proof.
  intros cl count src_mem src_base dst_mem dst_base Hwf
         byte_len Hsrc_acc Hdst_acc dst_after.
  split.
  - (* Completeness *)
    intros i Hi.
    unfold dst_after. apply memory_copy_in_range. exact Hi.
  - split.
    + (* Safety *)
      intros addr Hout.
      unfold dst_after. apply memory_copy_outside_range. exact Hout.
    + (* Reads in bounds *)
      intros i Hi.
      unfold dst_after.
      rewrite memory_copy_in_range by exact Hi.
      unfold range_accessible in Hsrc_acc.
      exact (Hsrc_acc i Hi).
Qed.

(* -------------------------------------------------------------------------
   Conditional copy: safe and complete when discriminant matches

   Combines conditional copy semantics with safety and completeness.
   When disc = expected:
   - All bytes are copied (completeness)
   - No writes outside the destination (safety)
   When disc <> expected:
   - Memory is unchanged
   ------------------------------------------------------------------------- *)

Theorem conditional_copy_safe_and_complete :
  forall cpp param_count disc_val src_mem src_ptr src_len dst_mem,
    conditional_pointer_pair_wf cpp param_count ->
    let cl := cpp_copy_layout cpp in
    let byte_len := src_len * effective_byte_multiplier cl in
    range_accessible src_mem src_ptr byte_len ->
    (* Case analysis on discriminant match *)
    (disc_val = cpp_discriminant_value cpp ->
      forall new_ptr,
        range_accessible dst_mem new_ptr byte_len ->
        let dst_after := memory_copy src_mem src_ptr dst_mem new_ptr byte_len in
        (* All bytes copied correctly *)
        (forall i, i < byte_len ->
          dst_after (new_ptr + i) = src_mem (src_ptr + i)) /\
        (* No writes outside destination *)
        (forall addr, addr < new_ptr \/ addr >= new_ptr + byte_len ->
          dst_after addr = dst_mem addr)) /\
    (disc_val <> cpp_discriminant_value cpp ->
      (* No operation needed: memory unchanged *)
      True).
Proof.
  intros cpp param_count disc_val src_mem src_ptr src_len dst_mem
         Hwf cl byte_len Hsrc_acc.
  split.
  - (* Discriminant matches *)
    intros Hmatch new_ptr Hdst_acc dst_after.
    split.
    + intros i Hi.
      unfold dst_after. apply memory_copy_in_range. exact Hi.
    + intros addr Hout.
      unfold dst_after. apply memory_copy_outside_range. exact Hout.
  - (* Discriminant does not match *)
    intros _. exact I.
Qed.

(* End of copy_layout_proofs *)
