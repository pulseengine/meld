(* =========================================================================
   Bridge Theorem: gen_all_remaps → instr_rewrites

   Connects the merger's remap table to the instruction rewriting
   specification: every instruction in every function body can be
   rewritten using gen_all_remaps, provided sources are unique.

   This bridges merge_correctness.v (remap generation) to fusion_spec.v
   (instruction rewriting and forward simulation).
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith Wf_nat.
From MeldSpec Require Import wasm_core component_model fusion_types.
From MeldMerge Require Import merge_defs merge_layout merge_remap merge_correctness.
Import ListNotations.

(* -------------------------------------------------------------------------
   Instruction Well-formedness

   All index references in an instruction must be within the module's
   index space bounds. This mirrors WASM validation: a validated module
   guarantees all indices are in range. Nested Block/Loop/If bodies
   must be recursively well-formed.
   ------------------------------------------------------------------------- *)

Inductive instr_wf (m : module) : instr -> Prop :=
  | WF_instr : forall i,
      (* Index-referencing instructions: each index must be in bounds *)
      (forall funcidx, i = Call funcidx ->
        funcidx < space_count_of_module m FuncIdx) ->
      (forall tableidx typeidx, i = CallIndirect tableidx typeidx ->
        tableidx < space_count_of_module m TableIdx /\
        typeidx < space_count_of_module m TypeIdx) ->
      (forall globalidx, i = GlobalGet globalidx ->
        globalidx < space_count_of_module m GlobalIdx) ->
      (forall globalidx, i = GlobalSet globalidx ->
        globalidx < space_count_of_module m GlobalIdx) ->
      (forall funcidx, i = RefFunc funcidx ->
        funcidx < space_count_of_module m FuncIdx) ->
      (forall tableidx, i = TableGet tableidx ->
        tableidx < space_count_of_module m TableIdx) ->
      (forall tableidx, i = TableSet tableidx ->
        tableidx < space_count_of_module m TableIdx) ->
      (forall tableidx, i = TableSize tableidx ->
        tableidx < space_count_of_module m TableIdx) ->
      (forall tableidx, i = TableGrow tableidx ->
        tableidx < space_count_of_module m TableIdx) ->
      (forall tableidx, i = TableFill tableidx ->
        tableidx < space_count_of_module m TableIdx) ->
      (forall dst srct, i = TableCopy dst srct ->
        dst < space_count_of_module m TableIdx /\
        srct < space_count_of_module m TableIdx) ->
      (forall tableidx elemidx, i = TableInit tableidx elemidx ->
        tableidx < space_count_of_module m TableIdx /\
        elemidx < space_count_of_module m ElemIdx) ->
      (forall elemidx, i = ElemDrop elemidx ->
        elemidx < space_count_of_module m ElemIdx) ->
      (* Memory instructions with memidx *)
      (forall memidx, i = MemorySize memidx ->
        memidx < space_count_of_module m MemIdx) ->
      (forall memidx, i = MemoryGrow memidx ->
        memidx < space_count_of_module m MemIdx) ->
      (forall vt memidx off align, i = Load vt memidx off align ->
        memidx < space_count_of_module m MemIdx) ->
      (forall vt memidx off align, i = Store vt memidx off align ->
        memidx < space_count_of_module m MemIdx) ->
      (forall dst_mem src_mem, i = MemoryCopy dst_mem src_mem ->
        dst_mem < space_count_of_module m MemIdx /\
        src_mem < space_count_of_module m MemIdx) ->
      (forall memidx, i = MemoryFill memidx ->
        memidx < space_count_of_module m MemIdx) ->
      (forall dataidx memidx, i = MemoryInit dataidx memidx ->
        dataidx < space_count_of_module m DataIdx /\
        memidx < space_count_of_module m MemIdx) ->
      (forall dataidx, i = DataDrop dataidx ->
        dataidx < space_count_of_module m DataIdx) ->
      (* Nested bodies must be recursively well-formed *)
      (forall bt body, i = Block bt body -> Forall (instr_wf m) body) ->
      (forall bt body, i = Loop bt body -> Forall (instr_wf m) body) ->
      (forall bt t e, i = If bt t e ->
        Forall (instr_wf m) t /\ Forall (instr_wf m) e) ->
      instr_wf m i.

(* A module is well-formed if all function bodies contain well-formed instrs *)
Definition module_wf (m : module) : Prop :=
  forall f, In f (mod_funcs m) -> Forall (instr_wf m) (func_body f).

(* -------------------------------------------------------------------------
   Instruction Size Measure

   Used for well-founded induction over nested instruction lists.
   Block/Loop/If have size > the sum of their bodies, enabling the
   strong induction step.
   ------------------------------------------------------------------------- *)

Fixpoint instr_size (i : instr) : nat :=
  let fix list_size (l : list instr) : nat :=
    match l with
    | [] => 0
    | h :: t => instr_size h + list_size t
    end
  in match i with
  | Block _ body => S (list_size body)
  | Loop _ body => S (list_size body)
  | If _ t e => S (list_size t + list_size e)
  | _ => 1
  end.

Definition instr_list_size (l : list instr) : nat :=
  fold_left (fun acc i => acc + instr_size i) l 0.

(* Every instruction has positive size *)
Lemma instr_size_pos : forall i, 1 <= instr_size i.
Proof.
  destruct i; simpl; lia.
Qed.

(* fold_left add with nonneg terms is >= base *)
Lemma fold_left_add_ge_base :
  forall {A : Type} (f : A -> nat) (l : list A) base,
    base <= fold_left (fun acc x => acc + f x) l base.
Proof.
  intros A f l. induction l as [|h t IH]; intro base; simpl.
  - lia.
  - specialize (IH (base + f h)). lia.
Qed.

(* instr_list_size of cons is at least the head's size *)
Lemma instr_list_size_cons :
  forall i rest,
    instr_size i + instr_list_size rest <= instr_list_size (i :: rest).
Proof.
  intros i rest. unfold instr_list_size. simpl.
  pose proof (fold_left_add_ge_base instr_size rest (0 + instr_size i)).
  pose proof (fold_left_add_ge_base instr_size rest 0).
  lia.
Qed.

(* instr_list_size matches the nested fix used in instr_size *)
Lemma instr_list_size_eq :
  forall l,
    instr_list_size l =
    (fix list_size (l : list instr) : nat :=
      match l with [] => 0 | h :: t => instr_size h + list_size t end) l.
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - unfold instr_list_size. simpl.
    rewrite <- IH. unfold instr_list_size.
    pose proof (fold_left_add_ge_base instr_size t 0) as Hge.
    (* Show fold_left (fun acc x => acc + f x) l (0 + n) =
       n + fold_left (fun acc x => acc + f x) l 0 *)
    assert (Hshift: forall (l : list instr) n,
      fold_left (fun acc x => acc + instr_size x) l (0 + n) =
      n + fold_left (fun acc x => acc + instr_size x) l 0).
    { clear. intros l. induction l as [|a r IHr]; intro n; simpl.
      - lia.
      - replace (0 + n + instr_size a) with (0 + (n + instr_size a)) by lia.
        replace (0 + instr_size a) with (0 + (instr_size a)) by lia.
        rewrite IHr. rewrite (IHr (instr_size a)). lia. }
    rewrite Hshift. lia.
Qed.

(* Helper: for a single index-referencing instruction, if all relevant
   index lookups succeed in the remap table, the instruction can be rewritten. *)
Lemma single_instr_rewritable :
  forall remaps src i,
    (* For each index space referenced by i, lookup succeeds *)
    (forall funcidx, i = Call funcidx ->
      exists idx', lookup_remap remaps FuncIdx src funcidx = Some idx') ->
    (forall tableidx typeidx, i = CallIndirect tableidx typeidx ->
      exists t' ty', lookup_remap remaps TableIdx src tableidx = Some t' /\
                     lookup_remap remaps TypeIdx src typeidx = Some ty') ->
    (forall globalidx, i = GlobalGet globalidx ->
      exists idx', lookup_remap remaps GlobalIdx src globalidx = Some idx') ->
    (forall globalidx, i = GlobalSet globalidx ->
      exists idx', lookup_remap remaps GlobalIdx src globalidx = Some idx') ->
    (forall funcidx, i = RefFunc funcidx ->
      exists idx', lookup_remap remaps FuncIdx src funcidx = Some idx') ->
    (forall tableidx, i = TableGet tableidx ->
      exists idx', lookup_remap remaps TableIdx src tableidx = Some idx') ->
    (forall tableidx, i = TableSet tableidx ->
      exists idx', lookup_remap remaps TableIdx src tableidx = Some idx') ->
    (forall tableidx, i = TableSize tableidx ->
      exists idx', lookup_remap remaps TableIdx src tableidx = Some idx') ->
    (forall tableidx, i = TableGrow tableidx ->
      exists idx', lookup_remap remaps TableIdx src tableidx = Some idx') ->
    (forall tableidx, i = TableFill tableidx ->
      exists idx', lookup_remap remaps TableIdx src tableidx = Some idx') ->
    (forall dst srct, i = TableCopy dst srct ->
      exists d' s', lookup_remap remaps TableIdx src dst = Some d' /\
                    lookup_remap remaps TableIdx src srct = Some s') ->
    (forall tableidx elemidx, i = TableInit tableidx elemidx ->
      exists t' e', lookup_remap remaps TableIdx src tableidx = Some t' /\
                    lookup_remap remaps ElemIdx src elemidx = Some e') ->
    (forall elemidx, i = ElemDrop elemidx ->
      exists idx', lookup_remap remaps ElemIdx src elemidx = Some idx') ->
    (* Memory instructions with memidx *)
    (forall memidx, i = MemorySize memidx ->
      exists idx', lookup_remap remaps MemIdx src memidx = Some idx') ->
    (forall memidx, i = MemoryGrow memidx ->
      exists idx', lookup_remap remaps MemIdx src memidx = Some idx') ->
    (forall vt memidx off align, i = Load vt memidx off align ->
      exists idx', lookup_remap remaps MemIdx src memidx = Some idx') ->
    (forall vt memidx off align, i = Store vt memidx off align ->
      exists idx', lookup_remap remaps MemIdx src memidx = Some idx') ->
    (forall dst_mem src_mem, i = MemoryCopy dst_mem src_mem ->
      exists d' s', lookup_remap remaps MemIdx src dst_mem = Some d' /\
                    lookup_remap remaps MemIdx src src_mem = Some s') ->
    (forall memidx, i = MemoryFill memidx ->
      exists idx', lookup_remap remaps MemIdx src memidx = Some idx') ->
    (forall dataidx memidx, i = MemoryInit dataidx memidx ->
      exists d' m', lookup_remap remaps DataIdx src dataidx = Some d' /\
                    lookup_remap remaps MemIdx src memidx = Some m') ->
    (forall dataidx, i = DataDrop dataidx ->
      exists idx', lookup_remap remaps DataIdx src dataidx = Some idx') ->
    (* Nested blocks: assume bodies are already rewritable *)
    (forall bt body, i = Block bt body ->
      exists body', Forall2 (instr_rewrites remaps src) body body') ->
    (forall bt body, i = Loop bt body ->
      exists body', Forall2 (instr_rewrites remaps src) body body') ->
    (forall bt then_ else_, i = If bt then_ else_ ->
      exists then_' else_',
        Forall2 (instr_rewrites remaps src) then_ then_' /\
        Forall2 (instr_rewrites remaps src) else_ else_') ->
    exists i', instr_rewrites remaps src i i'.
Proof.
  intros remaps src i
    Hcall Hcall_ind Hgget Hgset Hreffunc
    Htget Htset Htsize Htgrow Htfill Htcopy Htinit
    Hedrop
    Hmemsize Hmemgrow Hload Hstore Hmemcopy Hmemfill Hminit
    Hddrop
    Hblock Hloop Hif.
  destruct i.
  (* Control flow — pass through unchanged *)
  - exists Nop. apply RW_Nop.
  - exists Unreachable. apply RW_Unreachable.
  - (* Block *) destruct (Hblock _ _ eq_refl) as [body' Hbody'].
    exists (Block bt body'). apply RW_Block. exact Hbody'.
  - (* Loop *) destruct (Hloop _ _ eq_refl) as [body' Hbody'].
    exists (Loop bt body'). apply RW_Loop. exact Hbody'.
  - (* If *) destruct (Hif _ _ _ eq_refl) as [then_' [else_' [Ht He]]].
    exists (If bt then_' else_'). apply RW_If; assumption.
  - exists (Br labelidx). apply RW_Br.
  - exists (BrIf labelidx). apply RW_BrIf.
  - exists (BrTable labels default). apply RW_BrTable.
  - exists Return. apply RW_Return.
  (* Call *)
  - destruct (Hcall _ eq_refl) as [idx' Hlookup].
    exists (Call idx'). apply RW_Call. exact Hlookup.
  (* CallIndirect *)
  - destruct (Hcall_ind _ _ eq_refl) as [t' [ty' [Ht Hty]]].
    exists (CallIndirect t' ty'). apply RW_CallIndirect; assumption.
  (* Parametric *)
  - exists Drop. apply RW_Drop.
  - exists (Select ts). apply RW_Select.
  (* Locals *)
  - exists (LocalGet localidx). apply RW_LocalGet.
  - exists (LocalSet localidx). apply RW_LocalSet.
  - exists (LocalTee localidx). apply RW_LocalTee.
  (* Globals *)
  - destruct (Hgget _ eq_refl) as [idx' Hlookup].
    exists (GlobalGet idx'). apply RW_GlobalGet. exact Hlookup.
  - destruct (Hgset _ eq_refl) as [idx' Hlookup].
    exists (GlobalSet idx'). apply RW_GlobalSet. exact Hlookup.
  (* Memory *)
  - destruct (Hmemsize _ eq_refl) as [idx' Hlookup].
    exists (MemorySize idx'). apply RW_MemorySize. exact Hlookup.
  - destruct (Hmemgrow _ eq_refl) as [idx' Hlookup].
    exists (MemoryGrow idx'). apply RW_MemoryGrow. exact Hlookup.
  - destruct (Hload _ _ _ _ eq_refl) as [idx' Hlookup].
    exists (Load vt idx' memarg_offset memarg_align). apply RW_Load. exact Hlookup.
  - destruct (Hstore _ _ _ _ eq_refl) as [idx' Hlookup].
    exists (Store vt idx' memarg_offset memarg_align). apply RW_Store. exact Hlookup.
  (* Numeric *)
  - exists (NumericOp op). apply RW_NumericOp.
  (* Reference *)
  - exists (RefNull rt). apply RW_RefNull.
  - exists RefIsNull. apply RW_RefIsNull.
  - destruct (Hreffunc _ eq_refl) as [idx' Hlookup].
    exists (RefFunc idx'). apply RW_RefFunc. exact Hlookup.
  (* Table *)
  - destruct (Htget _ eq_refl) as [idx' Hlookup].
    exists (TableGet idx'). apply RW_TableGet. exact Hlookup.
  - destruct (Htset _ eq_refl) as [idx' Hlookup].
    exists (TableSet idx'). apply RW_TableSet. exact Hlookup.
  - destruct (Htsize _ eq_refl) as [idx' Hlookup].
    exists (TableSize idx'). apply RW_TableSize. exact Hlookup.
  - destruct (Htgrow _ eq_refl) as [idx' Hlookup].
    exists (TableGrow idx'). apply RW_TableGrow. exact Hlookup.
  - destruct (Htfill _ eq_refl) as [idx' Hlookup].
    exists (TableFill idx'). apply RW_TableFill. exact Hlookup.
  - destruct (Htcopy _ _ eq_refl) as [d' [s' [Hd Hs]]].
    exists (TableCopy d' s'). apply RW_TableCopy; assumption.
  - destruct (Htinit _ _ eq_refl) as [t' [e' [Ht He]]].
    exists (TableInit t' e'). apply RW_TableInit; assumption.
  - destruct (Hedrop _ eq_refl) as [idx' Hlookup].
    exists (ElemDrop idx'). apply RW_ElemDrop. exact Hlookup.
  (* Memory bulk *)
  - destruct (Hmemcopy _ _ eq_refl) as [d' [s' [Hd Hs]]].
    exists (MemoryCopy d' s'). apply RW_MemoryCopy; assumption.
  - destruct (Hmemfill _ eq_refl) as [idx' Hlookup].
    exists (MemoryFill idx'). apply RW_MemoryFill. exact Hlookup.
  - destruct (Hminit _ _ eq_refl) as [d' [m' [Hd Hm]]].
    exists (MemoryInit d' m'). apply RW_MemoryInit; assumption.
  - destruct (Hddrop _ eq_refl) as [idx' Hlookup].
    exists (DataDrop idx'). apply RW_DataDrop. exact Hlookup.
Qed.

(* -------------------------------------------------------------------------
   Core Workhorse: instr_list_rewritable

   By strong induction on the size bound n, every well-formed instruction
   list whose total size <= n can be rewritten using gen_all_remaps.

   The key insight: for nested Block/Loop/If, the body's instr_list_size
   is strictly less than the enclosing instruction's instr_size, which
   lets the strong IH apply.
   ------------------------------------------------------------------------- *)

Lemma instr_list_rewritable :
  forall n input strategy,
    unique_sources input ->
    forall src m,
      In (src, m) input ->
      forall instrs,
        Forall (instr_wf m) instrs ->
        instr_list_size instrs <= n ->
        exists instrs',
          Forall2 (instr_rewrites (gen_all_remaps input strategy) src) instrs instrs'.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros input strategy Huniq src m Hin instrs Hwf Hsize.
  (* Get completeness of gen_all_remaps *)
  assert (Hcomplete: remaps_complete input (gen_all_remaps input strategy)).
  { apply gen_all_remaps_complete. exact Huniq. }
  unfold remaps_complete in Hcomplete.
  destruct instrs as [|i rest].
  - (* nil: trivial *)
    exists []. constructor.
  - (* cons i rest *)
    (* Split well-formedness *)
    inversion Hwf as [|? ? Hwf_i Hwf_rest]. subst.
    (* Size bound: instr_size i + instr_list_size rest <= n *)
    assert (Hsize_split: instr_size i + instr_list_size rest <= n).
    { pose proof (instr_list_size_cons i rest). lia. }
    (* instr_size is always >= 1, needed for size arithmetic *)
    pose proof (instr_size_pos i) as Hi_pos.
    (* Rewrite the rest by IH (size of rest < n since head has size >= 1) *)
    assert (Hrest: exists rest',
      Forall2 (instr_rewrites (gen_all_remaps input strategy) src) rest rest').
    { apply (IHn (instr_list_size rest)); try assumption; try lia. }
    destruct Hrest as [rest' Hrest'].
    (* Rewrite the head instruction i using single_instr_rewritable *)
    inversion Hwf_i as [? Hcall Hcall_ind Hgget Hgset Hreffunc
      Htget Htset Htsize Htgrow Htfill Htcopy Htinit
      Hedrop
      Hmemsize Hmemgrow Hload Hstore Hmemcopy Hmemfill Hminit
      Hddrop Hblock Hloop Hif]. subst.
    assert (Hi: exists i',
      instr_rewrites (gen_all_remaps input strategy) src i i').
    { apply single_instr_rewritable.
      (* Index-bound hypotheses: combine instr_wf bounds with Hcomplete *)
      - (* Call *) intros funcidx Heq.
        apply (Hcomplete src m FuncIdx funcidx Hin).
        specialize (Hcall funcidx Heq).
        unfold space_count_of_module in Hcall. exact Hcall.
      - (* CallIndirect *) intros tableidx typeidx Heq.
        specialize (Hcall_ind tableidx typeidx Heq).
        destruct Hcall_ind as [Htbl Htyp].
        destruct (Hcomplete src m TableIdx tableidx Hin) as [t' Ht'].
        { unfold space_count_of_module in Htbl. exact Htbl. }
        destruct (Hcomplete src m TypeIdx typeidx Hin) as [ty' Hty'].
        { unfold space_count_of_module in Htyp. exact Htyp. }
        exists t', ty'. auto.
      - (* GlobalGet *) intros gidx Heq.
        apply (Hcomplete src m GlobalIdx gidx Hin).
        specialize (Hgget gidx Heq).
        unfold space_count_of_module in Hgget. exact Hgget.
      - (* GlobalSet *) intros gidx Heq.
        apply (Hcomplete src m GlobalIdx gidx Hin).
        specialize (Hgset gidx Heq).
        unfold space_count_of_module in Hgset. exact Hgset.
      - (* RefFunc *) intros funcidx Heq.
        apply (Hcomplete src m FuncIdx funcidx Hin).
        specialize (Hreffunc funcidx Heq).
        unfold space_count_of_module in Hreffunc. exact Hreffunc.
      - (* TableGet *) intros tidx Heq.
        apply (Hcomplete src m TableIdx tidx Hin).
        specialize (Htget tidx Heq).
        unfold space_count_of_module in Htget. exact Htget.
      - (* TableSet *) intros tidx Heq.
        apply (Hcomplete src m TableIdx tidx Hin).
        specialize (Htset tidx Heq).
        unfold space_count_of_module in Htset. exact Htset.
      - (* TableSize *) intros tidx Heq.
        apply (Hcomplete src m TableIdx tidx Hin).
        specialize (Htsize tidx Heq).
        unfold space_count_of_module in Htsize. exact Htsize.
      - (* TableGrow *) intros tidx Heq.
        apply (Hcomplete src m TableIdx tidx Hin).
        specialize (Htgrow tidx Heq).
        unfold space_count_of_module in Htgrow. exact Htgrow.
      - (* TableFill *) intros tidx Heq.
        apply (Hcomplete src m TableIdx tidx Hin).
        specialize (Htfill tidx Heq).
        unfold space_count_of_module in Htfill. exact Htfill.
      - (* TableCopy *) intros dst srct Heq.
        specialize (Htcopy dst srct Heq). destruct Htcopy as [Hd Hs].
        destruct (Hcomplete src m TableIdx dst Hin) as [d' Hd'].
        { unfold space_count_of_module in Hd. exact Hd. }
        destruct (Hcomplete src m TableIdx srct Hin) as [s' Hs'].
        { unfold space_count_of_module in Hs. exact Hs. }
        exists d', s'. auto.
      - (* TableInit *) intros tidx eidx Heq.
        specialize (Htinit tidx eidx Heq). destruct Htinit as [Ht He].
        destruct (Hcomplete src m TableIdx tidx Hin) as [t' Ht'].
        { unfold space_count_of_module in Ht. exact Ht. }
        destruct (Hcomplete src m ElemIdx eidx Hin) as [e' He'].
        { unfold space_count_of_module in He. exact He. }
        exists t', e'. auto.
      - (* ElemDrop *) intros eidx Heq.
        apply (Hcomplete src m ElemIdx eidx Hin).
        specialize (Hedrop eidx Heq).
        unfold space_count_of_module in Hedrop. exact Hedrop.
      - (* MemorySize *) intros midx Heq.
        apply (Hcomplete src m MemIdx midx Hin).
        specialize (Hmemsize midx Heq).
        unfold space_count_of_module in Hmemsize. exact Hmemsize.
      - (* MemoryGrow *) intros midx Heq.
        apply (Hcomplete src m MemIdx midx Hin).
        specialize (Hmemgrow midx Heq).
        unfold space_count_of_module in Hmemgrow. exact Hmemgrow.
      - (* Load *) intros vt midx off align Heq.
        apply (Hcomplete src m MemIdx midx Hin).
        specialize (Hload vt midx off align Heq).
        unfold space_count_of_module in Hload. exact Hload.
      - (* Store *) intros vt midx off align Heq.
        apply (Hcomplete src m MemIdx midx Hin).
        specialize (Hstore vt midx off align Heq).
        unfold space_count_of_module in Hstore. exact Hstore.
      - (* MemoryCopy *) intros dst_mem src_mem Heq.
        specialize (Hmemcopy dst_mem src_mem Heq). destruct Hmemcopy as [Hd Hs].
        destruct (Hcomplete src m MemIdx dst_mem Hin) as [d' Hd'].
        { unfold space_count_of_module in Hd. exact Hd. }
        destruct (Hcomplete src m MemIdx src_mem Hin) as [s' Hs'].
        { unfold space_count_of_module in Hs. exact Hs. }
        exists d', s'. auto.
      - (* MemoryFill *) intros midx Heq.
        apply (Hcomplete src m MemIdx midx Hin).
        specialize (Hmemfill midx Heq).
        unfold space_count_of_module in Hmemfill. exact Hmemfill.
      - (* MemoryInit *) intros didx midx Heq.
        specialize (Hminit didx midx Heq). destruct Hminit as [Hd Hm].
        destruct (Hcomplete src m DataIdx didx Hin) as [d' Hd'].
        { unfold space_count_of_module in Hd. exact Hd. }
        destruct (Hcomplete src m MemIdx midx Hin) as [m' Hm'].
        { unfold space_count_of_module in Hm. exact Hm. }
        exists d', m'. auto.
      - (* DataDrop *) intros didx Heq.
        apply (Hcomplete src m DataIdx didx Hin).
        specialize (Hddrop didx Heq).
        unfold space_count_of_module in Hddrop. exact Hddrop.
      - (* Block: apply IH on body, size strictly less *)
        intros bt body Heq.
        specialize (Hblock bt body Heq).
        assert (Hbody_size: instr_list_size body < instr_size i).
        { subst i. simpl. rewrite instr_list_size_eq. lia. }
        apply (IHn (instr_list_size body)); try assumption; try lia.
      - (* Loop: apply IH on body, size strictly less *)
        intros bt body Heq.
        specialize (Hloop bt body Heq).
        assert (Hbody_size: instr_list_size body < instr_size i).
        { subst i. simpl. rewrite instr_list_size_eq. lia. }
        apply (IHn (instr_list_size body)); try assumption; try lia.
      - (* If: apply IH on both branches *)
        intros bt then_ else_ Heq.
        specialize (Hif bt then_ else_ Heq).
        destruct Hif as [Hwf_then Hwf_else].
        assert (Hthen_size: instr_list_size then_ < instr_size i).
        { subst i. simpl. rewrite !instr_list_size_eq. lia. }
        assert (Helse_size: instr_list_size else_ < instr_size i).
        { subst i. simpl. rewrite !instr_list_size_eq. lia. }
        destruct (IHn (instr_list_size then_) ltac:(lia)
                      input strategy Huniq src m Hin then_ Hwf_then ltac:(lia))
          as [then_' Hthen'].
        destruct (IHn (instr_list_size else_) ltac:(lia)
                      input strategy Huniq src m Hin else_ Hwf_else ltac:(lia))
          as [else_' Helse'].
        exists then_', else_'. auto.
    }
    destruct Hi as [i' Hi'].
    exists (i' :: rest'). constructor; assumption.
Qed.

(* -------------------------------------------------------------------------
   Main Bridge Theorem

   gen_all_remaps is sufficient for rewriting all instructions in all
   function bodies, given unique sources and well-formed modules.

   The module_wf hypothesis is safe: WASM validation guarantees all
   indices in instruction bodies are within bounds (analogous to
   CompCert's wt_program assumption).
   ------------------------------------------------------------------------- *)

Theorem gen_all_remaps_enables_rewriting :
  forall input strategy,
    unique_sources input ->
    forall src m f,
      In (src, m) input ->
      module_wf m ->
      In f (mod_funcs m) ->
      exists body',
        Forall2 (instr_rewrites (gen_all_remaps input strategy) src)
                (func_body f) body'.
Proof.
  intros input strategy Huniq src m f Hin Hwf Hf_in.
  apply (instr_list_rewritable (instr_list_size (func_body f))); auto.
  - apply Hwf. exact Hf_in.
Qed.

(* End of merge_bridge *)
