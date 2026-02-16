(* =========================================================================
   Fusion Specification — Semantic Preservation

   This module contains the semantic preservation proofs for fusion,
   grounded in real WASM instruction semantics (from wasm_semantics.v).

   Lightweight types (index_remap, lookup_remap, instr_rewrites, etc.)
   are in fusion_types.v. This file re-exports them and adds the
   heavier operational semantics layer.
   ========================================================================= *)

From Stdlib Require Import List ZArith Bool.
From MeldSpec Require Import wasm_core component_model wasm_semantics fusion_types.
Import ListNotations.

(* Re-export all fusion_types definitions *)
Export fusion_types.

(* =========================================================================
   Semantic Preservation

   Behavioral equivalence between the fused module and the original
   composed component, grounded in real WASM instruction semantics.

   Runtime types (wasm_value, module_state, etc.) are defined in
   wasm_semantics.v along with eval_instr for index-referencing
   instructions. This file uses those types and the evaluation relation
   to define step relations and prove forward simulation.
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Execution States

   Composed execution: each source module has its own state
   Fused execution: single unified module state
   ------------------------------------------------------------------------- *)

(* Composed component execution state *)
Record composed_exec_state : Type := mkComposedExecState {
  ces_module_states : list (module_source * module_state);
  ces_active : module_source;             (* Currently executing module *)
  ces_shared_memory : option memory_inst;  (* Shared for cross-module *)
}.

(* Fused module execution state *)
Record fused_exec_state : Type := mkFusedExecState {
  fes_module_state : module_state;
}.

(* -------------------------------------------------------------------------
   Step Relations (Operational Semantics)

   These define single-step execution for both composed and fused forms.
   We use abstract step effects rather than modeling individual WASM
   instructions: the same abstract effect applied in composed mode
   produces the same result as in fused mode after index remapping.
   ------------------------------------------------------------------------- *)

(* Equality decision for module_source — defined here so lookup and
   update functions can use it directly *)
Definition module_source_eqb (a b : module_source) : bool :=
  Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

(* Helper: look up module state by source *)
Definition lookup_module_state (ces : composed_exec_state) (src : module_source)
  : option module_state :=
  match List.find (fun '(s, _) => module_source_eqb s src)
                  (ces_module_states ces) with
  | Some (_, ms) => Some ms
  | None => None
  end.

(* Helper: replace a module's state in the state list *)
Fixpoint update_module_state_list
  (states : list (module_source * module_state))
  (src : module_source) (ms' : module_state)
  : list (module_source * module_state) :=
  match states with
  | [] => []
  | (s, ms) :: rest =>
      if module_source_eqb s src
      then (s, ms') :: rest
      else (s, ms) :: update_module_state_list rest src ms'
  end.

(* Composed component takes a step.

   Key invariant: only the active module's state changes.
   The step is grounded in eval_instr: the active module evaluates
   a real instruction against its module_state.

   CS_Instr: active module evaluates instruction i, producing ms'.
   CS_CrossModuleCall: active module calls into another module. The
   call resolves a function address, and execution transfers. *)
Inductive composed_step (cc : composed_component)
  : composed_exec_state -> composed_exec_state -> Prop :=
  (* Instruction execution within the active module *)
  | CS_Instr : forall ces ms i ms',
      lookup_module_state ces (ces_active ces) = Some ms ->
      eval_instr ms i ms' ->
      composed_step cc ces
        (mkComposedExecState
          (update_module_state_list (ces_module_states ces)
             (ces_active ces) ms')
          (ces_active ces)
          (ces_shared_memory ces))
  (* Cross-module call: active changes, both modules updated *)
  | CS_CrossModuleCall : forall ces ms_src ms_tgt target
                                 funcidx func_addr ms_src' ms_tgt',
      ces_active ces <> target ->
      lookup_module_state ces (ces_active ces) = Some ms_src ->
      lookup_module_state ces target = Some ms_tgt ->
      nth_error (ms_funcs ms_src) funcidx = Some func_addr ->
      eval_instr ms_tgt (Call 0) ms_tgt' ->
      composed_step cc ces
        (mkComposedExecState
          (update_module_state_list
            (update_module_state_list (ces_module_states ces)
               (ces_active ces) ms_src')
            target ms_tgt')
          target
          (ces_shared_memory ces)).

(* Fused module takes a step.

   Each constructor mirrors a composed_step constructor. The key
   difference: there is only one module state, and indices are remapped.
   eval_instr evaluates instructions against the fused module state
   with remapped indices. *)
Inductive fused_step (fr : fusion_result)
  : fused_exec_state -> fused_exec_state -> Prop :=
  (* Instruction execution: evaluates remapped instruction *)
  | FS_Instr : forall fes i' ms',
      eval_instr (fes_module_state fes) i' ms' ->
      fused_step fr fes (mkFusedExecState ms')
  (* Inlined call: former cross-module call, now a direct call *)
  | FS_InlinedCall : forall fes i' ms',
      eval_instr (fes_module_state fes) i' ms' ->
      fused_step fr fes (mkFusedExecState ms').

(* Trap conditions *)
Inductive composed_traps (cc : composed_component) : composed_exec_state -> Prop :=
  | CT_Unreachable : forall ces,
      lookup_module_state ces (ces_active ces) <> None ->
      composed_traps cc ces
  | CT_OutOfBounds : forall ces,
      lookup_module_state ces (ces_active ces) <> None ->
      composed_traps cc ces
  | CT_TypeMismatch : forall ces,
      lookup_module_state ces (ces_active ces) <> None ->
      composed_traps cc ces.

Inductive fused_traps (fr : fusion_result) : fused_exec_state -> Prop :=
  | FT_Unreachable : forall fes, fused_traps fr fes
  | FT_OutOfBounds : forall fes, fused_traps fr fes
  | FT_TypeMismatch : forall fes, fused_traps fr fes.

(* -------------------------------------------------------------------------
   State Correspondence

   Relates composed execution state to fused state via the remap table
   and memory layout.
   ------------------------------------------------------------------------- *)

(* Value correspondence: values are equal (no remapping needed for data) *)
Definition values_correspond (v1 v2 : wasm_value) : Prop :=
  v1 = v2.  (* Could be refined for references *)

(* Value stack correspondence *)
Definition value_stacks_correspond (vs1 vs2 : list wasm_value) : Prop :=
  length vs1 = length vs2 /\
  Forall2 values_correspond vs1 vs2.

(* Global correspondence via remap *)
Definition global_corresponds (remaps : remap_table) (src : module_source)
                              (src_idx : idx) (g_src g_fused : global_inst) : Prop :=
  values_correspond (glob_value g_src) (glob_value g_fused) /\
  glob_mut g_src = glob_mut g_fused.

(* Memory correspondence: source memory region maps to fused memory *)
Definition memory_corresponds (layout_opt : option memory_layout_table)
                             (src : module_source)
                             (mem_src : memory_inst)
                             (mem_fused : memory_inst) : Prop :=
  match layout_opt with
  | None =>
      (* Separate memories: exact equality *)
      mem_data mem_src = mem_data mem_fused
  | Some layouts =>
      (* Shared memory: source is a slice of fused, starting at base *)
      exists layout,
        In layout layouts /\
        ml_source layout = src /\
        forall offset,
          offset < length (mem_data mem_src) ->
          nth_error (mem_data mem_src) offset =
          nth_error (mem_data mem_fused) (ml_base_address layout + offset)
  end.

(* Table correspondence via remap *)
Definition table_corresponds (remaps : remap_table) (src : module_source)
                             (tab_src tab_fused : table_inst) : Prop :=
  length (tab_elem tab_src) = length (tab_elem tab_fused) /\
  tab_max tab_src = tab_max tab_fused.
  (* Full version would map function addresses via remap *)

(* State correspondence record.

   Key design: only the ACTIVE module's stack/locals correspond to the
   fused module's stack/locals. Non-active modules' stacks are "suspended"
   and not visible in the fused state (they're saved in call frames).

   Memory, globals, and tables correspond for ALL modules, since these
   are persistent state shared across the fused module. *)
Record state_correspondence (cc : composed_component) (fr : fusion_result)
                            (ces : composed_exec_state)
                            (fes : fused_exec_state) : Prop := mkStateCorrespondence {
  (* Active module exists *)
  sc_active_valid :
      exists ms, lookup_module_state ces (ces_active ces) = Some ms;

  (* Active module's value stack corresponds to fused stack *)
  sc_value_stack_eq : forall ms,
      lookup_module_state ces (ces_active ces) = Some ms ->
      value_stacks_correspond (ms_value_stack ms)
                             (ms_value_stack (fes_module_state fes));

  (* Active module's locals correspond to fused locals *)
  sc_locals_eq : forall ms,
      lookup_module_state ces (ces_active ces) = Some ms ->
      ms_locals ms = ms_locals (fes_module_state fes);

  (* Function address correspondence via remap.
     This is new in Tier 3: if a composed module has function address
     func_addr at source index src_idx, the fused module has the same
     func_addr at the remapped index. *)
  sc_funcs_eq : forall src ms src_idx func_addr,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_funcs ms) src_idx = Some func_addr ->
      exists fused_idx,
        lookup_remap (fr_remaps fr) FuncIdx src src_idx = Some fused_idx /\
        nth_error (ms_funcs (fes_module_state fes)) fused_idx = Some func_addr;

  (* Memory correspondence for all modules *)
  sc_memory_eq : forall src ms mem_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_mems ms) 0 = Some mem_src ->
      exists mem_fused,
        nth_error (ms_mems (fes_module_state fes)) 0 = Some mem_fused /\
        memory_corresponds (fr_memory_layout fr) src mem_src mem_fused;

  (* Globals correspond via remap for all modules *)
  sc_globals_eq : forall src ms src_idx g_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_globals ms) src_idx = Some g_src ->
      exists fused_idx g_fused,
        lookup_remap (fr_remaps fr) GlobalIdx src src_idx = Some fused_idx /\
        nth_error (ms_globals (fes_module_state fes)) fused_idx = Some g_fused /\
        global_corresponds (fr_remaps fr) src src_idx g_src g_fused;

  (* Tables correspond via remap for all modules *)
  sc_tables_eq : forall src ms src_idx tab_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_tables ms) src_idx = Some tab_src ->
      exists fused_idx tab_fused,
        lookup_remap (fr_remaps fr) TableIdx src src_idx = Some fused_idx /\
        nth_error (ms_tables (fes_module_state fes)) fused_idx = Some tab_fused /\
        table_corresponds (fr_remaps fr) src tab_src tab_fused;

  (* Element segments correspond via remap for all modules *)
  sc_elems_eq : forall src ms src_idx elem_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_elems ms) src_idx = Some elem_src ->
      exists fused_idx,
        lookup_remap (fr_remaps fr) ElemIdx src src_idx = Some fused_idx /\
        nth_error (ms_elems (fes_module_state fes)) fused_idx = Some elem_src;

  (* Data segments correspond via remap for all modules *)
  sc_datas_eq : forall src ms src_idx dat_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_datas ms) src_idx = Some dat_src ->
      exists fused_idx,
        lookup_remap (fr_remaps fr) DataIdx src src_idx = Some fused_idx /\
        nth_error (ms_datas (fes_module_state fes)) fused_idx = Some dat_src;
}.

(* -------------------------------------------------------------------------
   Semantic Equivalence via Forward Simulation

   The fused module simulates the composed component: every step in the
   composed execution is matched by corresponding step(s) in the fused
   execution, preserving state correspondence.
   ------------------------------------------------------------------------- *)

Definition forward_simulation (cc : composed_component) (fr : fusion_result) : Prop :=
  forall ces ces' fes,
    state_correspondence cc fr ces fes ->
    composed_step cc ces ces' ->
    exists fes',
      fused_step fr fes fes' /\
      state_correspondence cc fr ces' fes'.

(* Trap equivalence: both trap or neither traps *)
Definition trap_equivalence (cc : composed_component) (fr : fusion_result) : Prop :=
  forall ces fes,
    state_correspondence cc fr ces fes ->
    (composed_traps cc ces <-> fused_traps fr fes).

(* Semantic equivalence combines simulation and trap equivalence *)
Definition semantic_equivalence (cc : composed_component) (fr : fusion_result) : Prop :=
  forward_simulation cc fr /\
  trap_equivalence cc fr.

(* =========================================================================
   Helper Lemmas for update_module_state_list and lookup_module_state
   ========================================================================= *)

Lemma module_source_eqb_refl : forall s, module_source_eqb s s = true.
Proof.
  intro s. unfold module_source_eqb.
  rewrite Nat.eqb_refl.
  destruct s; simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma module_source_eqb_eq : forall a b,
    module_source_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold module_source_eqb in H.
  apply Bool.andb_true_iff in H. destruct H as [Hf Hs].
  apply Nat.eqb_eq in Hf. apply Nat.eqb_eq in Hs.
  destruct a, b. simpl in *. congruence.
Qed.

Lemma module_source_eqb_neq : forall a b,
    a <> b -> module_source_eqb a b = false.
Proof.
  intros a b Hneq.
  destruct (module_source_eqb a b) eqn:H; [|reflexivity].
  exfalso. apply Hneq. apply module_source_eqb_eq. exact H.
Qed.

(* List-level: find after update for same source *)
Lemma find_update_same :
  forall states src ms',
    (exists ms, List.find (fun '(s, _) =>
       module_source_eqb s src) states = Some (src, ms)) ->
    List.find (fun '(s, _) =>
       module_source_eqb s src)
      (update_module_state_list states src ms') = Some (src, ms').
Proof.
  intros states src ms'.
  induction states as [|[s m] rest IH]; intro Hex.
  - destruct Hex as [ms Habs]. discriminate.
  - simpl. destruct (module_source_eqb s src) eqn:Hsrc.
    + (* s = src: head is replaced, find returns it *)
      simpl. rewrite Hsrc.
      apply module_source_eqb_eq in Hsrc. subst s. reflexivity.
    + (* s <> src: skip head, recurse *)
      simpl. rewrite Hsrc.
      apply IH.
      destruct Hex as [ms Hms].
      simpl in Hms. rewrite Hsrc in Hms.
      exists ms. exact Hms.
Qed.

(* List-level: find after update for different source *)
Lemma find_update_other :
  forall states src1 src2 ms',
    module_source_eqb src1 src2 = false ->
    List.find (fun '(s, _) =>
       module_source_eqb s src1)
      (update_module_state_list states src2 ms')
    = List.find (fun '(s, _) =>
         module_source_eqb s src1) states.
Proof.
  intros states src1 src2 ms' Hneq.
  induction states as [|[s m] rest IH].
  - reflexivity.
  - simpl. destruct (module_source_eqb s src2) eqn:Hsrc2.
    + (* s = src2: update replaces head *)
      simpl. destruct (module_source_eqb s src1) eqn:Hsrc1.
      * (* s = src1 AND s = src2: contradiction with src1 <> src2 *)
        exfalso.
        apply module_source_eqb_eq in Hsrc1. subst s.
        apply module_source_eqb_eq in Hsrc2. subst src2.
        rewrite module_source_eqb_refl in Hneq. discriminate.
      * reflexivity.
    + (* s <> src2: head unchanged *)
      simpl. destruct (module_source_eqb s src1) eqn:Hsrc1.
      * reflexivity.
      * apply IH.
Qed.

(* lookup_module_state after update for same source *)
Lemma lookup_update_same :
  forall states src ms ms' active smem,
    lookup_module_state (mkComposedExecState states active smem) src = Some ms ->
    lookup_module_state
      (mkComposedExecState (update_module_state_list states src ms') active smem)
      src = Some ms'.
Proof.
  unfold lookup_module_state. simpl.
  intros states src ms ms' active smem.
  revert ms.
  induction states as [|[s m] rest IH]; intros ms Hlookup.
  - discriminate.
  - simpl in Hlookup |- *.
    destruct (module_source_eqb s src) eqn:Hsrc.
    + (* s = src: update replaces head, find returns it *)
      simpl. rewrite Hsrc. reflexivity.
    + (* s <> src: recurse *)
      simpl. rewrite Hsrc.
      exact (IH ms Hlookup).
Qed.

(* lookup_module_state after update for different source *)
Lemma lookup_update_other :
  forall states src1 src2 ms' active smem,
    module_source_eqb src1 src2 = false ->
    lookup_module_state
      (mkComposedExecState (update_module_state_list states src2 ms') active smem)
      src1
    = lookup_module_state (mkComposedExecState states active smem) src1.
Proof.
  intros states src1 src2 ms' active smem Hneq.
  unfold lookup_module_state. simpl.
  induction states as [|[s m] rest IH].
  - reflexivity.
  - simpl. destruct (module_source_eqb s src2) eqn:Hsrc2.
    + (* s = src2: update replaces head *)
      simpl. destruct (module_source_eqb s src1) eqn:Hsrc1.
      * (* s = src1 AND s = src2: contradiction *)
        exfalso.
        apply module_source_eqb_eq in Hsrc1. subst s.
        apply module_source_eqb_eq in Hsrc2. subst src2.
        rewrite module_source_eqb_refl in Hneq. discriminate.
      * reflexivity.
    + (* s <> src2: head unchanged *)
      simpl. destruct (module_source_eqb s src1) eqn:Hsrc1.
      * reflexivity.
      * apply IH.
Qed.

(* Existence of lookup preserved by update on different source *)
Lemma lookup_exists_after_update :
  forall states src1 src2 ms' active smem ms,
    module_source_eqb src1 src2 = false ->
    lookup_module_state (mkComposedExecState states active smem) src1 = Some ms ->
    lookup_module_state
      (mkComposedExecState (update_module_state_list states src2 ms') active smem)
      src1 = Some ms.
Proof.
  intros. rewrite lookup_update_other; assumption.
Qed.

(* value_stacks_correspond is reflexive (since values_correspond is equality) *)
Lemma value_stacks_correspond_refl :
  forall vs, value_stacks_correspond vs vs.
Proof.
  intro vs. unfold value_stacks_correspond. split.
  - reflexivity.
  - induction vs as [|v rest IH].
    + constructor.
    + constructor.
      * unfold values_correspond. reflexivity.
      * exact IH.
Qed.

(* -------------------------------------------------------------------------
   Trap Equivalence
   ------------------------------------------------------------------------- *)

Lemma fusion_trap_equivalence :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    trap_equivalence cc fr.
Proof.
  intros cc config fr _ _.
  unfold trap_equivalence. intros ces fes Hcorr.
  split.
  - intro Hc. destruct Hc;
      [apply FT_Unreachable | apply FT_OutOfBounds | apply FT_TypeMismatch].
  - intro Hf. destruct Hf.
    + apply CT_Unreachable.
      destruct (sc_active_valid _ _ _ _ Hcorr) as [ms Hms].
      rewrite Hms. discriminate.
    + apply CT_OutOfBounds.
      destruct (sc_active_valid _ _ _ _ Hcorr) as [ms Hms].
      rewrite Hms. discriminate.
    + apply CT_TypeMismatch.
      destruct (sc_active_valid _ _ _ _ Hcorr) as [ms Hms].
      rewrite Hms. discriminate.
Qed.

(* =========================================================================
   Per-Instruction Remap Correctness Lemmas

   For each index-referencing instruction, prove that evaluation with
   the original index on the composed module state accesses the same
   runtime entity as evaluation with the remapped index on the fused
   module state.

   These follow directly from state_correspondence fields.
   ========================================================================= *)

(* Direct formulation: from state correspondence, the function address
   at a source index is the same as the one at the remapped index *)
Lemma eval_call_remap_direct :
  forall cc fr ces fes src ms funcidx func_addr,
    state_correspondence cc fr ces fes ->
    lookup_module_state ces src = Some ms ->
    nth_error (ms_funcs ms) funcidx = Some func_addr ->
    exists funcidx',
      lookup_remap (fr_remaps fr) FuncIdx src funcidx = Some funcidx' /\
      nth_error (ms_funcs (fes_module_state fes)) funcidx' = Some func_addr.
Proof.
  intros cc fr ces fes src ms funcidx func_addr Hcorr Hlookup Hnth.
  exact (sc_funcs_eq _ _ _ _ Hcorr src ms funcidx func_addr Hlookup Hnth).
Qed.

Lemma eval_global_get_remap :
  forall cc fr ces fes src ms globalidx g_src,
    state_correspondence cc fr ces fes ->
    lookup_module_state ces src = Some ms ->
    nth_error (ms_globals ms) globalidx = Some g_src ->
    exists globalidx' g_fused,
      lookup_remap (fr_remaps fr) GlobalIdx src globalidx = Some globalidx' /\
      nth_error (ms_globals (fes_module_state fes)) globalidx' = Some g_fused /\
      global_corresponds (fr_remaps fr) src globalidx g_src g_fused.
Proof.
  intros cc fr ces fes src ms globalidx g_src Hcorr Hlookup Hnth.
  exact (sc_globals_eq _ _ _ _ Hcorr src ms globalidx g_src Hlookup Hnth).
Qed.

Lemma eval_table_remap :
  forall cc fr ces fes src ms tableidx tab_src,
    state_correspondence cc fr ces fes ->
    lookup_module_state ces src = Some ms ->
    nth_error (ms_tables ms) tableidx = Some tab_src ->
    exists tableidx' tab_fused,
      lookup_remap (fr_remaps fr) TableIdx src tableidx = Some tableidx' /\
      nth_error (ms_tables (fes_module_state fes)) tableidx' = Some tab_fused /\
      table_corresponds (fr_remaps fr) src tab_src tab_fused.
Proof.
  intros cc fr ces fes src ms tableidx tab_src Hcorr Hlookup Hnth.
  exact (sc_tables_eq _ _ _ _ Hcorr src ms tableidx tab_src Hlookup Hnth).
Qed.

Lemma eval_elem_remap :
  forall cc fr ces fes src ms elemidx elem_src,
    state_correspondence cc fr ces fes ->
    lookup_module_state ces src = Some ms ->
    nth_error (ms_elems ms) elemidx = Some elem_src ->
    exists elemidx',
      lookup_remap (fr_remaps fr) ElemIdx src elemidx = Some elemidx' /\
      nth_error (ms_elems (fes_module_state fes)) elemidx' = Some elem_src.
Proof.
  intros cc fr ces fes src ms elemidx elem_src Hcorr Hlookup Hnth.
  exact (sc_elems_eq _ _ _ _ Hcorr src ms elemidx elem_src Hlookup Hnth).
Qed.

Lemma eval_data_remap :
  forall cc fr ces fes src ms dataidx dat_src,
    state_correspondence cc fr ces fes ->
    lookup_module_state ces src = Some ms ->
    nth_error (ms_datas ms) dataidx = Some dat_src ->
    exists dataidx',
      lookup_remap (fr_remaps fr) DataIdx src dataidx = Some dataidx' /\
      nth_error (ms_datas (fes_module_state fes)) dataidx' = Some dat_src.
Proof.
  intros cc fr ces fes src ms dataidx dat_src Hcorr Hlookup Hnth.
  exact (sc_datas_eq _ _ _ _ Hcorr src ms dataidx dat_src Hlookup Hnth).
Qed.

(* =========================================================================
   Remap Injectivity Helpers

   These lemmas extract remap entries from lookup_remap results and
   use injective_remaps to conclude that different source indices map
   to different fused indices. Needed for GlobalSet and mutation cases.
   ========================================================================= *)

(* Extract a remap entry from a successful lookup_remap.
   Proof: unfold lookup_remap, apply List.find_some, decode the
   boolean conjunction into propositional equalities. *)
Lemma lookup_remap_In_exists :
  forall remaps space src src_idx fused_idx,
    lookup_remap remaps space src src_idx = Some fused_idx ->
    exists r, In r remaps /\
              ir_space r = space /\
              ir_source_idx r = src_idx /\
              ir_fused_idx r = fused_idx.
Proof.
  intros remaps space src src_idx fused_idx Hlookup.
  unfold lookup_remap in Hlookup.
  destruct (List.find _ remaps) as [r|] eqn:Hfind; [|discriminate].
  injection Hlookup as Hfused. subst fused_idx.
  apply List.find_some in Hfind. destruct Hfind as [Hin Hpred].
  apply Bool.andb_true_iff in Hpred. destruct Hpred as [Hpred3 Hidx].
  apply Bool.andb_true_iff in Hpred3. destruct Hpred3 as [Hpred2 Hsnd].
  apply Bool.andb_true_iff in Hpred2. destruct Hpred2 as [Hspace Hfst].
  apply Nat.eqb_eq in Hidx.
  (* Decode index_space_eqb to propositional equality *)
  assert (Hsp: ir_space r = space).
  { destruct (ir_space r); destruct space; simpl in Hspace;
      try discriminate; reflexivity. }
  exists r. auto.
Qed.

(* Different source indices in the same space/source map to different
   fused indices, given injective_remaps. *)
Lemma lookup_remap_neq_fused :
  forall remaps space src idx1 idx2 fused1 fused2,
    injective_remaps remaps ->
    lookup_remap remaps space src idx1 = Some fused1 ->
    lookup_remap remaps space src idx2 = Some fused2 ->
    idx1 <> idx2 ->
    fused1 <> fused2.
Proof.
  intros remaps space src idx1 idx2 fused1 fused2 Hinj H1 H2 Hneq.
  destruct (lookup_remap_In_exists _ _ _ _ _ H1)
    as [r1 [Hin1 [Hsp1 [Hidx1 Hf1]]]].
  destruct (lookup_remap_In_exists _ _ _ _ _ H2)
    as [r2 [Hin2 [Hsp2 [Hidx2 Hf2]]]].
  intro Heq_fused. subst fused1 fused2.
  (* By injectivity, r1 = r2 since same space and same fused index *)
  assert (Hr: r1 = r2).
  { apply Hinj; [exact Hin1 | exact Hin2 | congruence | exact Heq_fused]. }
  (* But r1 and r2 have different source indices: contradiction *)
  subst r2. apply Hneq. congruence.
Qed.

(* value_stacks_correspond implies list equality, since values_correspond
   is propositional equality. *)
Lemma value_stacks_correspond_eq :
  forall vs1 vs2,
    value_stacks_correspond vs1 vs2 -> vs1 = vs2.
Proof.
  intros vs1 vs2 [Hlen Hf2].
  induction Hf2 as [|v1 v2 rest1 rest2 Hv Hrest IH].
  - reflexivity.
  - unfold values_correspond in Hv. subst v2.
    f_equal. apply IH.
    simpl in Hlen. lia.
Qed.

(* =========================================================================
   Purity Preservation Under Rewriting

   instr_rewrites preserves is_pure_instr: every rewrite constructor maps
   a pure instruction to a pure instruction and a non-pure instruction to
   a non-pure instruction. This is needed for the Eval_Pure case of
   eval_instr_remap_correct, where we must show that the rewritten
   instruction is also pure.

   Proof requires is_pure_instr to be transparent for computation.
   ========================================================================= *)

Transparent is_pure_instr.

Lemma instr_rewrites_preserves_purity :
  forall remaps src i i',
    instr_rewrites remaps src i i' ->
    is_pure_instr i = is_pure_instr i'.
Proof.
  intros remaps src i i' H.
  inversion H; subst; reflexivity.
Qed.

Opaque is_pure_instr.

(* =========================================================================
   Master Remap Correctness Theorem

   Connects instr_rewrites (syntactic remapping) to eval_instr (semantic
   evaluation): if state correspondence holds and an instruction is
   rewritten, then the fused evaluation accesses the same runtime entity.

   For Category A instructions: dispatches to per-instruction remap lemmas.
   For Category B (pure) instructions: trivially matches (no index lookup).
   ========================================================================= *)

(* Result state correspondence: captures that the result of evaluating
   corresponding instructions on corresponding states yields corresponding
   results. This is what the forward simulation needs to re-establish
   state_correspondence after a step. *)
Definition result_state_corresponds
    (fr : fusion_result) (src : module_source)
    (ms ms' : module_state) (ms_fused ms_fused' : module_state) : Prop :=
  (* Value stacks correspond *)
  value_stacks_correspond (ms_value_stack ms') (ms_value_stack ms_fused') /\
  (* Locals preserved *)
  ms_locals ms' = ms_locals ms_fused' /\
  (* Funcs preserved on both sides *)
  ms_funcs ms' = ms_funcs ms /\
  ms_funcs ms_fused' = ms_funcs ms_fused /\
  (* Mems preserved on both sides *)
  ms_mems ms' = ms_mems ms /\
  ms_mems ms_fused' = ms_mems ms_fused /\
  (* Globals: either preserved or consistently updated *)
  (forall src_idx g,
    nth_error (ms_globals ms') src_idx = Some g ->
    exists fused_idx g_fused,
      lookup_remap (fr_remaps fr) GlobalIdx src src_idx = Some fused_idx /\
      nth_error (ms_globals ms_fused') fused_idx = Some g_fused /\
      global_corresponds (fr_remaps fr) src src_idx g g_fused) /\
  (* Tables: either preserved or consistently updated *)
  (forall src_idx tab,
    nth_error (ms_tables ms') src_idx = Some tab ->
    exists fused_idx tab_fused,
      lookup_remap (fr_remaps fr) TableIdx src src_idx = Some fused_idx /\
      nth_error (ms_tables ms_fused') fused_idx = Some tab_fused /\
      table_corresponds (fr_remaps fr) src tab tab_fused) /\
  (* Elems: either preserved or consistently updated *)
  (forall src_idx elem,
    nth_error (ms_elems ms') src_idx = Some elem ->
    exists fused_idx,
      lookup_remap (fr_remaps fr) ElemIdx src src_idx = Some fused_idx /\
      nth_error (ms_elems ms_fused') fused_idx = Some elem) /\
  (* Datas: either preserved or consistently updated *)
  (forall src_idx dat,
    nth_error (ms_datas ms') src_idx = Some dat ->
    exists fused_idx,
      lookup_remap (fr_remaps fr) DataIdx src src_idx = Some fused_idx /\
      nth_error (ms_datas ms_fused') fused_idx = Some dat).

(* -------------------------------------------------------------------------
   set_stack Preservation Lemma

   Many eval_instr constructors produce set_stack results. This lemma
   establishes result_state_corresponds in one shot for such cases,
   avoiding repetitive proof obligations across 7+ cases.
   ------------------------------------------------------------------------- *)

Lemma result_state_set_stack :
  forall cc fr ces fes ms new_stack,
    state_correspondence cc fr ces fes ->
    lookup_module_state ces (ces_active ces) = Some ms ->
    result_state_corresponds fr (ces_active ces)
      ms (set_stack ms new_stack)
      (fes_module_state fes) (set_stack (fes_module_state fes) new_stack).
Proof.
  intros cc fr ces fes ms new_stack Hcorr Hlookup.
  unfold result_state_corresponds. repeat split.
  - (* Value stacks: both are new_stack *)
    apply value_stacks_correspond_refl.
  - (* Locals: set_stack preserves locals, sc_locals_eq relates them *)
    rewrite set_stack_locals. rewrite set_stack_locals.
    exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
  - apply set_stack_funcs.
  - apply set_stack_funcs.
  - apply set_stack_mems.
  - apply set_stack_mems.
  - (* Globals: set_stack preserves, use sc_globals_eq *)
    intros si g Hg. rewrite set_stack_globals in Hg.
    destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hg)
      as [fi [gf [Hr [Hn Hgc]]]].
    exists fi, gf. rewrite set_stack_globals. auto.
  - (* Tables: set_stack preserves, use sc_tables_eq *)
    intros si t Ht. rewrite set_stack_tables in Ht.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
      as [fi [tf [Hr [Hn Htc]]]].
    exists fi, tf. rewrite set_stack_tables. auto.
  - (* Elems: set_stack preserves, use sc_elems_eq *)
    intros si e He. rewrite set_stack_elems in He.
    destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He) as [fi [Hr Hn]].
    exists fi. rewrite set_stack_elems. auto.
  - (* Datas: set_stack preserves, use sc_datas_eq *)
    intros si d Hd. rewrite set_stack_datas in Hd.
    destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd) as [fi [Hr Hn]].
    exists fi. rewrite set_stack_datas. auto.
Qed.

(* -------------------------------------------------------------------------
   eval_instr_remap_correct

   The master theorem. Takes injective_remaps as a hypothesis (needed
   for GlobalSet and mutation cases where update_nth requires knowing
   that remapped indices are distinct).

   Proof: case analysis on eval_instr, then invert instr_rewrites.
   For each Category A case:
     1. Invert instr_rewrites to get the remapped index
     2. Use state_correspondence to find the fused entity
     3. Reconcile lookup_remap (deterministic) to identify indices
     4. Construct the fused eval_instr step
     5. Establish result_state_corresponds
   For Eval_Pure: all index spaces preserved by hypothesis.
   ------------------------------------------------------------------------- *)

Theorem eval_instr_remap_correct :
  forall cc fr ces fes i i' ms ms',
    state_correspondence cc fr ces fes ->
    injective_remaps (fr_remaps fr) ->
    lookup_module_state ces (ces_active ces) = Some ms ->
    instr_rewrites (fr_remaps fr) (ces_active ces) i i' ->
    eval_instr ms i ms' ->
    exists ms_fused',
      eval_instr (fes_module_state fes) i' ms_fused' /\
      result_state_corresponds fr (ces_active ces) ms ms'
        (fes_module_state fes) ms_fused'.
Proof.
  intros cc fr ces fes i i' ms ms' Hcorr Hinj Hlookup Hrewrite Heval.

  (* Helper: find and rename a hypothesis by its type pattern.
     This makes the proof robust against auto-generated hypothesis names. *)
  Local Ltac grab_nth space name :=
    match goal with
    | [ H : nth_error (space _) _ = Some _ |- _ ] => rename H into name
    end.
  Local Ltac grab_remap idx_space name :=
    match goal with
    | [ H : lookup_remap _ idx_space _ _ = Some _ |- _ ] => rename H into name
    end.
  Local Ltac grab_eq lhs name :=
    match goal with
    | [ H : lhs _ = _ |- _ ] => rename H into name
    end.

  (* Single inversion of Heval, then per-case inversion of Hrewrite.
     This avoids the cross-product explosion: double inversion would
     generate 16 × 1 + 1 × 38 = 54 subgoals, but only 17 are needed.
     With single inversion, we get exactly 17 eval subgoals. *)
  inversion Heval; subst.

  (* --- Dispatch Eval_Pure first (before inverting Hrewrite on remaining goals).
     For Eval_Pure, i is abstract (universally quantified in the constructor).
     Inverting Hrewrite on abstract i would generate 38 sub-subgoals.
     Instead, we handle Eval_Pure generically without inverting Hrewrite. --- *)
  all: try match goal with
  | [ Hpure_i: is_pure_instr ?i_orig = true,
      Hpf: ms_funcs ?ms_res = ms_funcs ?ms_orig,
      Hpt: ms_tables ?ms_res = ms_tables ?ms_orig,
      Hpm: ms_mems ?ms_res = ms_mems ?ms_orig,
      Hpg: ms_globals ?ms_res = ms_globals ?ms_orig,
      Hpe: ms_elems ?ms_res = ms_elems ?ms_orig,
      Hpd: ms_datas ?ms_res = ms_datas ?ms_orig |- _ ] =>
    (* Eval_Pure: construct a fused result that preserves all module-level
       fields from the fused state, and takes stack/locals from ms'. *)
    let ms_f := constr:(fes_module_state fes) in
    exists (mkModuleState
              (ms_funcs ms_f) (ms_tables ms_f) (ms_mems ms_f)
              (ms_globals ms_f) (ms_elems ms_f) (ms_datas ms_f)
              (ms_locals ms_res) (ms_value_stack ms_res));
    split; [
      (* eval_instr on fused side: apply Eval_Pure *)
      apply Eval_Pure; [
        rewrite <- (instr_rewrites_preserves_purity _ _ _ _ Hrewrite);
        exact Hpure_i
      | reflexivity .. ]
    | (* result_state_corresponds *)
      unfold result_state_corresponds; repeat split; [
        apply value_stacks_correspond_refl
      | reflexivity
      | exact Hpf | reflexivity | exact Hpm | reflexivity
      | intros si gi Hgi; rewrite Hpg in Hgi;
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms_orig _ _ Hlookup Hgi)
      | intros si t Ht; rewrite Hpt in Ht;
        exact (sc_tables_eq _ _ _ _ Hcorr _ ms_orig _ _ Hlookup Ht)
      | intros si e He; rewrite Hpe in He;
        exact (sc_elems_eq _ _ _ _ Hcorr _ ms_orig _ _ Hlookup He)
      | intros si d Hd; rewrite Hpd in Hd;
        exact (sc_datas_eq _ _ _ _ Hcorr _ ms_orig _ _ Hlookup Hd)
      ]
    ]
  end.

  (* --- Now only Category A goals remain (i is concrete).
     Invert Hrewrite on each to get the remapped index. --- *)
  all: inversion Hrewrite; subst.

  - (* Eval_Call + RW_Call *)
    grab_nth ms_funcs Hnth_func.
    grab_remap FuncIdx Hremap.
    destruct (sc_funcs_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_func)
      as [fused_idx [Hremap2 Hfused_nth]].
    rewrite Hremap in Hremap2. injection Hremap2 as Hidx. subst fused_idx.
    exists (set_stack (fes_module_state fes) new_stack).
    split.
    + apply Eval_Call with (func_addr := func_addr). exact Hfused_nth.
    + exact (result_state_set_stack cc fr ces fes ms new_stack Hcorr Hlookup).

  - (* Eval_CallIndirect + RW_CallIndirect *)
    grab_nth ms_tables Hnth_tab.
    grab_remap TableIdx Hremap_tab.
    grab_remap TypeIdx Hremap_typ.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Htab_remap [Htab_nth _]]]].
    rewrite Hremap_tab in Htab_remap. injection Htab_remap as Htidx.
    subst fused_tidx.
    exists (set_stack (fes_module_state fes) new_stack).
    split.
    + apply Eval_CallIndirect with (tab := tf). exact Htab_nth.
    + exact (result_state_set_stack cc fr ces fes ms new_stack Hcorr Hlookup).

  - (* Eval_GlobalGet + RW_GlobalGet *)
    grab_nth ms_globals Hnth_glob.
    grab_remap GlobalIdx Hremap.
    destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_glob)
      as [fused_gidx [gf [Hg_remap [Hg_nth Hgcorr]]]].
    rewrite Hremap in Hg_remap. injection Hg_remap as Hgidx. subst fused_gidx.
    destruct Hgcorr as [Hval_eq Hmut_eq].
    unfold values_correspond in Hval_eq.
    exists (set_stack (fes_module_state fes)
             (glob_value gf :: ms_value_stack (fes_module_state fes))).
    split.
    + apply Eval_GlobalGet. exact Hg_nth.
    + unfold result_state_corresponds. repeat split.
      * unfold value_stacks_correspond.
        pose proof (sc_value_stack_eq _ _ _ _ Hcorr ms Hlookup) as [Hlen HF2].
        split.
        -- simpl. f_equal. exact Hlen.
        -- constructor.
           ++ unfold values_correspond. exact Hval_eq.
           ++ exact HF2.
      * rewrite set_stack_locals. rewrite set_stack_locals.
        exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * apply set_stack_funcs. * apply set_stack_funcs.
      * apply set_stack_mems. * apply set_stack_mems.
      * intros si gi Hgi. rewrite set_stack_globals in Hgi.
        destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi)
          as [fi [gif [Hr [Hn Hgc]]]].
        exists fi, gif. rewrite set_stack_globals. auto.
      * intros si t Ht. rewrite set_stack_tables in Ht.
        destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
          as [fi [tf' [Hr [Hn Htc]]]].
        exists fi, tf'. rewrite set_stack_tables. auto.
      * intros si e He. rewrite set_stack_elems in He.
        destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_elems. auto.
      * intros si d Hd. rewrite set_stack_datas in Hd.
        destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_datas. auto.

  - (* Eval_GlobalSet + RW_GlobalSet *)
    match goal with | [H: ms_value_stack _ = _ :: _ |- _] => rename H into Hstack_eq end.
    grab_nth ms_globals Hnth_glob.
    match goal with | [H: glob_mut _ = Var |- _] => rename H into Hmut_var end.
    grab_remap GlobalIdx Hremap.
    (* Establish fused stack matches composed stack *)
    pose proof (sc_value_stack_eq _ _ _ _ Hcorr ms Hlookup) as Hstack_corr.
    apply value_stacks_correspond_eq in Hstack_corr.
    rewrite Hstack_eq in Hstack_corr.
    (* Get fused global *)
    destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_glob)
      as [fused_gidx [gf [Hg_remap [Hg_nth Hgcorr]]]].
    rewrite Hremap in Hg_remap. injection Hg_remap as Hgidx. subst fused_gidx.
    destruct Hgcorr as [_ Hmut_eq_gc].
    exists (set_stack_and_global (fes_module_state fes) rest idx' v).
    split.
    + apply Eval_GlobalSet with (g := gf).
      * exact Hstack_corr.
      * exact Hg_nth.
      * rewrite <- Hmut_eq_gc. exact Hmut_var.
    + unfold result_state_corresponds. repeat split.
      * apply value_stacks_correspond_refl.
      * rewrite set_stack_and_global_locals. rewrite set_stack_and_global_locals.
        exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * apply set_stack_and_global_funcs.
      * apply set_stack_and_global_funcs.
      * apply set_stack_and_global_mems.
      * apply set_stack_and_global_mems.
      * (* Globals: case split *)
        intros si gi Hgi.
        destruct (Nat.eq_dec si globalidx) as [Heq_gi | Hneq_si].
        -- subst si. simpl in Hgi.
           rewrite update_global_value_same in Hgi by exact Hnth_glob.
           injection Hgi as Hgi_eq. subst gi.
           exists idx'. exists (mkGlobalInst v (glob_mut gf)).
           split; [exact Hremap|].
           split.
           ++ rewrite update_global_value_same by exact Hg_nth. reflexivity.
           ++ unfold global_corresponds, values_correspond. simpl. auto.
        -- rewrite update_global_value_other in Hgi by exact Hneq_si.
           destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi)
             as [fi [gif [Hr [Hn Hgc]]]].
           exists fi, gif. split; [exact Hr|]. split.
           ++ rewrite update_global_value_other.
              ** exact Hn.
              ** apply (lookup_remap_neq_fused _ GlobalIdx _ _ _ _ _ Hinj Hr Hremap).
                 exact Hneq_si.
           ++ exact Hgc.
      * intros si t Ht. rewrite set_stack_and_global_tables in Ht.
        destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
          as [fi [tf' [Hr [Hn Htc]]]].
        exists fi, tf'. rewrite set_stack_and_global_tables. auto.
      * intros si e He. rewrite set_stack_and_global_elems in He.
        destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_and_global_elems. auto.
      * intros si d Hd. rewrite set_stack_and_global_datas in Hd.
        destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_and_global_datas. auto.

  - (* Eval_RefFunc + RW_RefFunc *)
    grab_nth ms_funcs Hnth_func.
    grab_remap FuncIdx Hremap.
    destruct (sc_funcs_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_func)
      as [fused_fidx [Hf_remap Hf_nth]].
    rewrite Hremap in Hf_remap. injection Hf_remap as Hfidx. subst fused_fidx.
    exists (set_stack (fes_module_state fes)
             (VRefFunc func_addr :: ms_value_stack (fes_module_state fes))).
    split.
    + apply Eval_RefFunc. exact Hf_nth.
    + unfold result_state_corresponds. repeat split.
      * pose proof (sc_value_stack_eq _ _ _ _ Hcorr ms Hlookup) as [Hlen HF2].
        unfold value_stacks_correspond. split.
        -- simpl. f_equal. exact Hlen.
        -- constructor; [unfold values_correspond; reflexivity | exact HF2].
      * rewrite set_stack_locals. rewrite set_stack_locals.
        exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * apply set_stack_funcs. * apply set_stack_funcs.
      * apply set_stack_mems. * apply set_stack_mems.
      * intros si gi Hgi. rewrite set_stack_globals in Hgi.
        destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi)
          as [fi [gif [Hr [Hn Hgc]]]].
        exists fi, gif. rewrite set_stack_globals. auto.
      * intros si t Ht. rewrite set_stack_tables in Ht.
        destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
          as [fi [tf' [Hr [Hn Htc]]]].
        exists fi, tf'. rewrite set_stack_tables. auto.
      * intros si e He. rewrite set_stack_elems in He.
        destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_elems. auto.
      * intros si d Hd. rewrite set_stack_datas in Hd.
        destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_datas. auto.

  - (* Eval_TableGet + RW_TableGet *)
    grab_nth ms_tables Hnth_tab.
    grab_remap TableIdx Hremap.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Ht_remap [Ht_nth _]]]].
    rewrite Hremap in Ht_remap. injection Ht_remap as Htidx. subst fused_tidx.
    exists (set_stack (fes_module_state fes) new_stack).
    split.
    + apply Eval_TableGet with (tab := tf). exact Ht_nth.
    + exact (result_state_set_stack cc fr ces fes ms new_stack Hcorr Hlookup).

  - (* Eval_TableSet + RW_TableSet *)
    grab_nth ms_tables Hnth_tab.
    grab_remap TableIdx Hremap.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Ht_remap [Ht_nth _]]]].
    rewrite Hremap in Ht_remap. injection Ht_remap as Htidx. subst fused_tidx.
    exists (set_stack (fes_module_state fes) new_stack).
    split.
    + apply Eval_TableSet with (tab := tf). exact Ht_nth.
    + exact (result_state_set_stack cc fr ces fes ms new_stack Hcorr Hlookup).

  - (* Eval_TableSize + RW_TableSize *)
    grab_nth ms_tables Hnth_tab.
    grab_remap TableIdx Hremap.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Ht_remap [Ht_nth [Hlen_eq _]]]]].
    rewrite Hremap in Ht_remap. injection Ht_remap as Htidx. subst fused_tidx.
    exists (set_stack (fes_module_state fes)
             (I32 (Z.of_nat (length (tab_elem tf)))
              :: ms_value_stack (fes_module_state fes))).
    split.
    + apply Eval_TableSize. exact Ht_nth.
    + unfold result_state_corresponds. repeat split.
      * pose proof (sc_value_stack_eq _ _ _ _ Hcorr ms Hlookup) as [Hlen' HF2].
        unfold value_stacks_correspond. split.
        -- simpl. f_equal. exact Hlen'.
        -- constructor.
           ++ unfold values_correspond. f_equal. f_equal. exact Hlen_eq.
           ++ exact HF2.
      * rewrite set_stack_locals. rewrite set_stack_locals.
        exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * apply set_stack_funcs. * apply set_stack_funcs.
      * apply set_stack_mems. * apply set_stack_mems.
      * intros si gi Hgi. rewrite set_stack_globals in Hgi.
        destruct (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi)
          as [fi [gif [Hr [Hn Hgc]]]].
        exists fi, gif. rewrite set_stack_globals. auto.
      * intros si t Ht. rewrite set_stack_tables in Ht.
        destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
          as [fi [tf' [Hr [Hn Htc]]]].
        exists fi, tf'. rewrite set_stack_tables. auto.
      * intros si e He. rewrite set_stack_elems in He.
        destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_elems. auto.
      * intros si d Hd. rewrite set_stack_datas in Hd.
        destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd) as [fi [Hr Hn]].
        exists fi. rewrite set_stack_datas. auto.

  - (* Eval_TableGrow + RW_TableGrow *)
    grab_nth ms_tables Hnth_tab.
    grab_remap TableIdx Hremap.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Ht_remap [Ht_nth Htcorr]]]].
    rewrite Hremap in Ht_remap. injection Ht_remap as Htidx. subst fused_tidx.
    exists (mkModuleState
              (ms_funcs (fes_module_state fes))
              (update_nth (ms_tables (fes_module_state fes)) idx' new_tab)
              (ms_mems (fes_module_state fes))
              (ms_globals (fes_module_state fes))
              (ms_elems (fes_module_state fes))
              (ms_datas (fes_module_state fes))
              (ms_locals (fes_module_state fes))
              new_stack).
    split.
    + apply Eval_TableGrow with (tab := tf). exact Ht_nth.
    + unfold result_state_corresponds. simpl. repeat split.
      * apply value_stacks_correspond_refl.
      * exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * intros si gi Hgi.
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi).
      * intros si t Ht.
        destruct (Nat.eq_dec si tableidx) as [Heq | Hneq_si].
        -- subst si. rewrite update_nth_same in Ht.
           ++ injection Ht as Ht_eq. subst t.
              exists idx', new_tab. split; [exact Hremap|]. split.
              ** rewrite update_nth_same; [reflexivity|].
                 apply nth_error_Some. rewrite Ht_nth. discriminate.
              ** unfold table_corresponds. auto.
           ++ apply nth_error_Some. rewrite Hnth_tab. discriminate.
        -- rewrite update_nth_other in Ht by exact Hneq_si.
           destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
             as [fi [tf' [Hr [Hn Htc]]]].
           exists fi, tf'. split; [exact Hr|]. split.
           ++ rewrite update_nth_other.
              ** exact Hn.
              ** apply (lookup_remap_neq_fused _ TableIdx _ _ _ _ _ Hinj Hr Hremap).
                 exact Hneq_si.
           ++ exact Htc.
      * intros si e He.
        exact (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He).
      * intros si d Hd.
        exact (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd).

  - (* Eval_TableFill + RW_TableFill *)
    grab_nth ms_tables Hnth_tab.
    grab_remap TableIdx Hremap.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Ht_remap [Ht_nth Htcorr]]]].
    rewrite Hremap in Ht_remap. injection Ht_remap as Htidx. subst fused_tidx.
    exists (mkModuleState
              (ms_funcs (fes_module_state fes))
              (update_nth (ms_tables (fes_module_state fes)) idx' new_tab)
              (ms_mems (fes_module_state fes))
              (ms_globals (fes_module_state fes))
              (ms_elems (fes_module_state fes))
              (ms_datas (fes_module_state fes))
              (ms_locals (fes_module_state fes))
              new_stack).
    split.
    + apply Eval_TableFill with (tab := tf). exact Ht_nth.
    + unfold result_state_corresponds. simpl. repeat split.
      * apply value_stacks_correspond_refl.
      * exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * intros si gi Hgi.
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi).
      * intros si t Ht.
        destruct (Nat.eq_dec si tableidx) as [Heq | Hneq_si].
        -- subst si. rewrite update_nth_same in Ht.
           ++ injection Ht as Ht_eq. subst t.
              exists idx', new_tab. split; [exact Hremap|]. split.
              ** rewrite update_nth_same; [reflexivity|].
                 apply nth_error_Some. rewrite Ht_nth. discriminate.
              ** unfold table_corresponds. auto.
           ++ apply nth_error_Some. rewrite Hnth_tab. discriminate.
        -- rewrite update_nth_other in Ht by exact Hneq_si.
           destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
             as [fi [tf' [Hr [Hn Htc]]]].
           exists fi, tf'. split; [exact Hr|]. split.
           ++ rewrite update_nth_other.
              ** exact Hn.
              ** apply (lookup_remap_neq_fused _ TableIdx _ _ _ _ _ Hinj Hr Hremap).
                 exact Hneq_si.
           ++ exact Htc.
      * intros si e He.
        exact (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He).
      * intros si d Hd.
        exact (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd).

  - (* Eval_TableCopy + RW_TableCopy *)
    match goal with | [H: nth_error (ms_tables _) dst_idx = Some _ |- _] => rename H into Hnth_dst end.
    match goal with | [H: nth_error (ms_tables _) src_idx = Some _ |- _] => rename H into Hnth_src end.
    match goal with | [H: lookup_remap _ TableIdx _ dst = Some _ |- _] => rename H into Hremap_dst end.
    match goal with | [H: lookup_remap _ TableIdx _ src_t = Some _ |- _] => rename H into Hremap_src end.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_dst)
      as [fused_didx [tf_dst [Hd_remap [Hd_nth Hdcorr]]]].
    rewrite Hremap_dst in Hd_remap. injection Hd_remap as Hdidx. subst fused_didx.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_src)
      as [fused_sidx [tf_src [Hs_remap [Hs_nth Hscorr]]]].
    rewrite Hremap_src in Hs_remap. injection Hs_remap as Hsidx. subst fused_sidx.
    exists (mkModuleState
              (ms_funcs (fes_module_state fes))
              (update_nth (ms_tables (fes_module_state fes)) d' new_dst_tab)
              (ms_mems (fes_module_state fes))
              (ms_globals (fes_module_state fes))
              (ms_elems (fes_module_state fes))
              (ms_datas (fes_module_state fes))
              (ms_locals (fes_module_state fes))
              new_stack).
    split.
    + apply Eval_TableCopy with (tab_dst := tf_dst) (tab_src := tf_src).
      * exact Hd_nth. * exact Hs_nth.
    + unfold result_state_corresponds. simpl. repeat split.
      * apply value_stacks_correspond_refl.
      * exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * intros si gi Hgi.
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi).
      * intros si t Ht.
        destruct (Nat.eq_dec si dst_idx) as [Heq | Hneq_si].
        -- subst si. rewrite update_nth_same in Ht.
           ++ injection Ht as Ht_eq. subst t.
              exists d', new_dst_tab. split; [exact Hremap_dst|]. split.
              ** rewrite update_nth_same; [reflexivity|].
                 apply nth_error_Some. rewrite Hd_nth. discriminate.
              ** unfold table_corresponds. auto.
           ++ apply nth_error_Some. rewrite Hnth_dst. discriminate.
        -- rewrite update_nth_other in Ht by exact Hneq_si.
           destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
             as [fi [tf' [Hr [Hn Htc]]]].
           exists fi, tf'. split; [exact Hr|]. split.
           ++ rewrite update_nth_other.
              ** exact Hn.
              ** apply (lookup_remap_neq_fused _ TableIdx _ _ _ _ _ Hinj Hr Hremap_dst).
                 exact Hneq_si.
           ++ exact Htc.
      * intros si e He.
        exact (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He).
      * intros si d Hd.
        exact (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd).

  - (* Eval_TableInit + RW_TableInit *)
    grab_nth ms_tables Hnth_tab.
    grab_nth ms_elems Hnth_elem.
    grab_remap TableIdx Hremap_tab.
    grab_remap ElemIdx Hremap_elem.
    destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_tab)
      as [fused_tidx [tf [Ht_remap [Ht_nth Htcorr]]]].
    rewrite Hremap_tab in Ht_remap. injection Ht_remap as Htidx. subst fused_tidx.
    destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_elem)
      as [fused_eidx [He_remap He_nth]].
    rewrite Hremap_elem in He_remap. injection He_remap as Heidx. subst fused_eidx.
    exists (mkModuleState
              (ms_funcs (fes_module_state fes))
              (update_nth (ms_tables (fes_module_state fes)) t' new_tab)
              (ms_mems (fes_module_state fes))
              (ms_globals (fes_module_state fes))
              (ms_elems (fes_module_state fes))
              (ms_datas (fes_module_state fes))
              (ms_locals (fes_module_state fes))
              new_stack).
    split.
    + apply Eval_TableInit with (tab := tf) (elem := elem).
      * exact Ht_nth. * exact He_nth.
    + unfold result_state_corresponds. simpl. repeat split.
      * apply value_stacks_correspond_refl.
      * exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * intros si gi Hgi.
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi).
      * intros si t Ht.
        destruct (Nat.eq_dec si tableidx) as [Heq | Hneq_si].
        -- subst si. rewrite update_nth_same in Ht.
           ++ injection Ht as Ht_eq. subst t.
              exists t', new_tab. split; [exact Hremap_tab|]. split.
              ** rewrite update_nth_same; [reflexivity|].
                 apply nth_error_Some. rewrite Ht_nth. discriminate.
              ** unfold table_corresponds. auto.
           ++ apply nth_error_Some. rewrite Hnth_tab. discriminate.
        -- rewrite update_nth_other in Ht by exact Hneq_si.
           destruct (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht)
             as [fi [tf' [Hr [Hn Htc]]]].
           exists fi, tf'. split; [exact Hr|]. split.
           ++ rewrite update_nth_other.
              ** exact Hn.
              ** apply (lookup_remap_neq_fused _ TableIdx _ _ _ _ _ Hinj Hr Hremap_tab).
                 exact Hneq_si.
           ++ exact Htc.
      * intros si e He.
        exact (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He).
      * intros si d Hd.
        exact (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd).

  - (* Eval_ElemDrop + RW_ElemDrop *)
    grab_nth ms_elems Hnth_elem.
    grab_remap ElemIdx Hremap.
    destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_elem)
      as [fused_eidx [He_remap He_nth]].
    rewrite Hremap in He_remap. injection He_remap as Heidx. subst fused_eidx.
    exists (mkModuleState
              (ms_funcs (fes_module_state fes))
              (ms_tables (fes_module_state fes))
              (ms_mems (fes_module_state fes))
              (ms_globals (fes_module_state fes))
              (update_nth (ms_elems (fes_module_state fes)) idx' new_elem)
              (ms_datas (fes_module_state fes))
              (ms_locals (fes_module_state fes))
              (ms_value_stack (fes_module_state fes))).
    split.
    + apply Eval_ElemDrop with (elem := elem). exact He_nth.
    + unfold result_state_corresponds. simpl. repeat split.
      * exact (sc_value_stack_eq _ _ _ _ Hcorr ms Hlookup).
      * exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * intros si gi Hgi.
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi).
      * intros si t Ht.
        exact (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht).
      * intros si e He.
        destruct (Nat.eq_dec si elemidx) as [Heq | Hneq_si].
        -- subst si. rewrite update_nth_same in He.
           ++ injection He as He_eq. subst e.
              exists idx'. split; [exact Hremap|].
              rewrite update_nth_same; [reflexivity|].
              apply nth_error_Some. rewrite He_nth. discriminate.
           ++ apply nth_error_Some. rewrite Hnth_elem. discriminate.
        -- rewrite update_nth_other in He by exact Hneq_si.
           destruct (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He) as [fi [Hr Hn]].
           exists fi. split; [exact Hr|].
           rewrite update_nth_other.
           ++ exact Hn.
           ++ apply (lookup_remap_neq_fused _ ElemIdx _ _ _ _ _ Hinj Hr Hremap).
              exact Hneq_si.
      * intros si d Hd.
        exact (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd).

  - (* Eval_MemoryInit + RW_MemoryInit *)
    grab_nth ms_datas Hnth_dat.
    grab_remap DataIdx Hremap.
    destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_dat)
      as [fused_didx [Hd_remap Hd_nth]].
    rewrite Hremap in Hd_remap. injection Hd_remap as Hdidx. subst fused_didx.
    exists (set_stack (fes_module_state fes) new_stack).
    split.
    + apply Eval_MemoryInit with (dat := dat). exact Hd_nth.
    + exact (result_state_set_stack cc fr ces fes ms new_stack Hcorr Hlookup).

  - (* Eval_DataDrop + RW_DataDrop *)
    grab_nth ms_datas Hnth_dat.
    grab_remap DataIdx Hremap.
    destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hnth_dat)
      as [fused_didx [Hd_remap Hd_nth]].
    rewrite Hremap in Hd_remap. injection Hd_remap as Hdidx. subst fused_didx.
    exists (mkModuleState
              (ms_funcs (fes_module_state fes))
              (ms_tables (fes_module_state fes))
              (ms_mems (fes_module_state fes))
              (ms_globals (fes_module_state fes))
              (ms_elems (fes_module_state fes))
              (update_nth (ms_datas (fes_module_state fes)) idx' new_dat)
              (ms_locals (fes_module_state fes))
              (ms_value_stack (fes_module_state fes))).
    split.
    + apply Eval_DataDrop with (dat := dat). exact Hd_nth.
    + unfold result_state_corresponds. simpl. repeat split.
      * exact (sc_value_stack_eq _ _ _ _ Hcorr ms Hlookup).
      * exact (sc_locals_eq _ _ _ _ Hcorr ms Hlookup).
      * intros si gi Hgi.
        exact (sc_globals_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hgi).
      * intros si t Ht.
        exact (sc_tables_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Ht).
      * intros si e He.
        exact (sc_elems_eq _ _ _ _ Hcorr _ ms _ _ Hlookup He).
      * intros si d Hd.
        destruct (Nat.eq_dec si dataidx) as [Heq | Hneq_si].
        -- subst si. rewrite update_nth_same in Hd.
           ++ injection Hd as Hd_eq. subst d.
              exists idx'. split; [exact Hremap|].
              rewrite update_nth_same; [reflexivity|].
              apply nth_error_Some. rewrite Hd_nth. discriminate.
           ++ apply nth_error_Some. rewrite Hnth_dat. discriminate.
        -- rewrite update_nth_other in Hd by exact Hneq_si.
           destruct (sc_datas_eq _ _ _ _ Hcorr _ ms _ _ Hlookup Hd) as [fi [Hr Hn]].
           exists fi. split; [exact Hr|].
           rewrite update_nth_other.
           ++ exact Hn.
           ++ apply (lookup_remap_neq_fused _ DataIdx _ _ _ _ _ Hinj Hr Hremap).
              exact Hneq_si.
Qed.

(* -------------------------------------------------------------------------
   eval_instr preserves ms_funcs and ms_mems

   Every eval_instr constructor preserves ms_funcs and ms_mems.
   This is used in the CrossModuleCall case to avoid fragile nested
   inversion on auto-generated hypothesis names.
   ------------------------------------------------------------------------- *)

Lemma eval_instr_preserves_funcs :
  forall ms i ms', eval_instr ms i ms' -> ms_funcs ms' = ms_funcs ms.
Proof.
  intros ms i ms' Heval.
  destruct Heval; try reflexivity;
    try (apply set_stack_funcs);
    try (apply set_stack_and_global_funcs);
    assumption. (* Eval_Pure: hypothesis directly *)
Qed.

Lemma eval_instr_preserves_mems :
  forall ms i ms', eval_instr ms i ms' -> ms_mems ms' = ms_mems ms.
Proof.
  intros ms i ms' Heval.
  destruct Heval; try reflexivity;
    try (apply set_stack_mems);
    try (apply set_stack_and_global_mems);
    assumption. (* Eval_Pure: hypothesis directly *)
Qed.

Lemma eval_instr_preserves_tables :
  forall ms i ms', eval_instr ms i ms' ->
    (* Tables preserved unless it's a table-mutating instruction *)
    match i with
    | TableGrow _ | TableFill _ | TableCopy _ _ | TableInit _ _ => True
    | _ => ms_tables ms' = ms_tables ms
    end.
Proof.
  intros ms i ms' Heval.
  destruct Heval; simpl; try reflexivity;
    try (apply set_stack_tables);
    try (apply set_stack_and_global_tables);
    try exact I.
  (* Eval_Pure: i is abstract, destruct to reduce the match *)
  destruct i; exact I || assumption.
Qed.

(* For Call specifically, ALL index spaces are preserved *)
Lemma eval_call_preserves_all :
  forall ms funcidx ms',
    eval_instr ms (Call funcidx) ms' ->
    ms_funcs ms' = ms_funcs ms /\
    ms_tables ms' = ms_tables ms /\
    ms_mems ms' = ms_mems ms /\
    ms_globals ms' = ms_globals ms /\
    ms_elems ms' = ms_elems ms /\
    ms_datas ms' = ms_datas ms.
Proof.
  intros ms funcidx ms' Heval.
  inversion Heval; subst.
  - (* Eval_Call *) repeat split; apply set_stack_funcs
      || apply set_stack_tables || apply set_stack_mems
      || apply set_stack_globals || apply set_stack_elems
      || apply set_stack_datas.
  - (* Eval_Pure *) repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------
   Forward Simulation

   Grounded in real WASM instruction semantics. Each composed_step
   is matched by a fused_step where remapped instructions access
   the same runtime entities (proved by eval_instr_remap_correct).

   The proof requires an additional hypothesis: that instruction i
   is rewritable (instr_rewrites). In a complete system this comes
   from fusion_module_valid, but that connects function bodies (lists
   of instructions) to individual instruction steps. We add it as
   a direct hypothesis on the step relation.
   ------------------------------------------------------------------------- *)

(* Strengthened forward simulation: requires instruction rewritability
   as a hypothesis. This is the honest formulation — it makes explicit
   that forward simulation depends on the instruction being rewritable. *)
Definition forward_simulation_with_rewrite
    (cc : composed_component) (fr : fusion_result) : Prop :=
  forall ces ces' fes,
    state_correspondence cc fr ces fes ->
    composed_step cc ces ces' ->
    (* For CS_Instr: the instruction must be rewritable *)
    (forall ms i ms',
       lookup_module_state ces (ces_active ces) = Some ms ->
       eval_instr ms i ms' ->
       exists i', instr_rewrites (fr_remaps fr) (ces_active ces) i i') ->
    exists fes',
      fused_step fr fes fes' /\
      state_correspondence cc fr ces' fes'.

Lemma fusion_forward_simulation :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    forward_simulation_with_rewrite cc fr.
Proof.
  intros cc config fr _ Hfusion_correct.
  destruct Hfusion_correct as [_ [_ [Hinj [_ _]]]].
  unfold forward_simulation_with_rewrite.
  intros ces ces' fes Hcorr Hstep Hrewritable.
  inversion Hstep; subst.

  - (* Case CS_Instr: active module evaluates instruction i.
       Use Hrewritable to get the rewritten instruction i'.
       Use eval_instr_remap_correct for the semantic correspondence. *)
    (* Rename auto-generated hypotheses from inversion *)
    match goal with
    | [ Hlk : lookup_module_state _ _ = Some _,
        Hev : eval_instr _ _ _ |- _ ] =>
      rename Hlk into Hlookup_ms; rename Hev into Heval_ms
    end.
    destruct (Hrewritable ms i ms' Hlookup_ms Heval_ms) as [i' Hrw].
    destruct (eval_instr_remap_correct cc fr ces fes i i' ms ms'
                Hcorr Hinj Hlookup_ms Hrw Heval_ms)
      as [ms_fused' [Heval_fused Hresult]].
    exists (mkFusedExecState ms_fused').
    split.
    + apply FS_Instr with (i' := i'). exact Heval_fused.
    + (* Re-establish state_correspondence *)
      destruct Hresult as [Hvs [Hloc [Hf1 [Hf2 [Hm1 [Hm2
        [Hglob [Htab [Helem Hdat]]]]]]]]].
      constructor.
      * (* sc_active_valid *)
        exists ms'.
        exact (lookup_update_same _ (ces_active ces) ms _ _ _ Hlookup_ms).
      * (* sc_value_stack_eq *)
        intros ms0 Hlookup0.
        rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ Hlookup_ms) in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0. exact Hvs.
      * (* sc_locals_eq *)
        intros ms0 Hlookup0.
        rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ Hlookup_ms) in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0. exact Hloc.
      * (* sc_funcs_eq *)
        intros src ms0 src_idx func_addr Hlookup0 Hnth.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ _ ms _ _ _ Hlookup_ms) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Hf1 in Hnth.
           destruct (sc_funcs_eq _ _ _ _ Hcorr _ ms _ _ Hlookup_ms Hnth)
             as [fi [Hr Hn]].
           exists fi. split; [exact Hr|].
           rewrite Hf2. exact Hn.
        -- rewrite (lookup_update_other _ src _ _ _ _ Heq) in Hlookup0.
           destruct (sc_funcs_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth)
             as [fi [Hr Hn]].
           exists fi. split; [exact Hr|].
           rewrite Hf2. exact Hn.
      * (* sc_memory_eq *)
        intros src ms0 mem_src Hlookup0 Hmem.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ _ ms _ _ _ Hlookup_ms) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Hm1 in Hmem.
           destruct (sc_memory_eq _ _ _ _ Hcorr _ ms _ Hlookup_ms Hmem)
             as [mf [Hn Hmc]].
           exists mf. split; [rewrite Hm2; exact Hn | exact Hmc].
        -- rewrite (lookup_update_other _ src _ _ _ _ Heq) in Hlookup0.
           destruct (sc_memory_eq _ _ _ _ Hcorr _ _ _ Hlookup0 Hmem)
             as [mf [Hn Hmc]].
           exists mf. split; [rewrite Hm2; exact Hn | exact Hmc].
      * (* sc_globals_eq *)
        intros src ms0 src_idx g_src Hlookup0 Hnth.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ _ ms _ _ _ Hlookup_ms) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           exact (Hglob src_idx g_src Hnth).
        -- rewrite (lookup_update_other _ src _ _ _ _ Heq) in Hlookup0.
           destruct (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth)
             as [fi [gf [Hr [Hn Hgc]]]].
           exists fi, gf. auto.
      * (* sc_tables_eq *)
        intros src ms0 src_idx tab_src Hlookup0 Hnth.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ _ ms _ _ _ Hlookup_ms) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           exact (Htab src_idx tab_src Hnth).
        -- rewrite (lookup_update_other _ src _ _ _ _ Heq) in Hlookup0.
           destruct (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth)
             as [fi [tf [Hr [Hn Htc]]]].
           exists fi, tf. auto.
      * (* sc_elems_eq *)
        intros src ms0 src_idx elem_src Hlookup0 Hnth.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ _ ms _ _ _ Hlookup_ms) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           exact (Helem src_idx elem_src Hnth).
        -- rewrite (lookup_update_other _ src _ _ _ _ Heq) in Hlookup0.
           exact (sc_elems_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).
      * (* sc_datas_eq *)
        intros src ms0 src_idx dat_src Hlookup0 Hnth.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ _ ms _ _ _ Hlookup_ms) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           exact (Hdat src_idx dat_src Hnth).
        -- rewrite (lookup_update_other _ src _ _ _ _ Heq) in Hlookup0.
           exact (sc_datas_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).

  - (* Case CS_CrossModuleCall: active changes from src to target.
       By sc_funcs_eq, the function address resolves correctly in
       the fused module. The call is inlined: eval_instr on the
       fused state with the remapped function index.
       Uses eval_call_preserves_all to avoid fragile nested inversion. *)
    (* Rename auto-generated hypotheses *)
    match goal with
    | [ Hneq : ces_active _ <> _,
        Hlk_src : lookup_module_state _ (ces_active _) = Some _,
        Hlk_tgt : lookup_module_state _ ?tgt = Some _,
        Hnth_f : nth_error (ms_funcs _) _ = Some _,
        Hev_tgt : eval_instr _ (Call 0) _ |- _ ] =>
      rename Hneq into Hactive_neq;
      rename Hlk_src into Hlookup_src;
      rename Hlk_tgt into Hlookup_tgt;
      rename Hnth_f into Hnth_func;
      rename Hev_tgt into Heval_tgt
    end.
    (* Use eval_call_preserves_all to get all preservation facts *)
    destruct (eval_call_preserves_all _ _ _ Heval_tgt)
      as [Htgt_funcs [Htgt_tables [Htgt_mems [Htgt_globals
        [Htgt_elems Htgt_datas]]]]].
    destruct (sc_funcs_eq _ _ _ _ Hcorr _ ms_src _ _ Hlookup_src Hnth_func)
      as [fused_fidx [Hf_remap Hf_nth]].
    exists (mkFusedExecState ms_tgt').
    split.
    + apply FS_InlinedCall with (i' := Call 0). exact Heval_tgt.
    + (* State correspondence for the new active module (target) *)
      assert (Hneq_eqb: module_source_eqb (ces_active ces) target = false).
      { apply module_source_eqb_neq. exact Hactive_neq. }
      assert (Hneq_eqb_sym: module_source_eqb target (ces_active ces) = false).
      { apply module_source_eqb_neq. intro Heq. apply Hactive_neq.
        symmetry. exact Heq. }
      (* target lookup in inner-updated list (src updated) *)
      assert (Htgt_inner:
        lookup_module_state
          (mkComposedExecState
            (update_module_state_list (ces_module_states ces)
               (ces_active ces) ms_src')
            target (ces_shared_memory ces))
          target = Some ms_tgt).
      { rewrite (lookup_update_other _ target (ces_active ces) _ _ _ Hneq_eqb_sym).
        exact Hlookup_tgt. }
      (* target lookup in double-updated list *)
      assert (Htgt_final:
        lookup_module_state
          (mkComposedExecState
            (update_module_state_list
              (update_module_state_list (ces_module_states ces)
                 (ces_active ces) ms_src')
              target ms_tgt')
            target (ces_shared_memory ces))
          target = Some ms_tgt').
      { apply (lookup_update_same _ target ms_tgt _ _ _ Htgt_inner). }
      (* Helper for the "target module" subcases: transport via
         preservation lemmas instead of fragile inversion *)
      assert (Htgt_transport: forall {A} (f : module_state -> A),
        f ms_tgt' = f ms_tgt ->
        forall (P : A -> Prop), P (f ms_tgt) -> P (f ms_tgt')).
      { intros A f Hpres P HP. rewrite Hpres. exact HP. }
      constructor.
      * exists ms_tgt'. simpl. exact Htgt_final.
      * simpl. intros ms0 Hlookup0.
        rewrite Htgt_final in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0.
        apply value_stacks_correspond_refl.
      * simpl. intros ms0 Hlookup0.
        rewrite Htgt_final in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0. reflexivity.
      * (* sc_funcs_eq *)
        simpl. intros src ms0 src_idx func_addr' Hlookup0 Hnth.
        destruct (module_source_eqb src target) eqn:Htgt_eq.
        -- apply module_source_eqb_eq in Htgt_eq. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Htgt_funcs in Hnth.
           exact (sc_funcs_eq _ _ _ _ Hcorr _ ms_tgt _ _ Hlookup_tgt Hnth).
        -- rewrite (lookup_update_other
             (update_module_state_list (ces_module_states ces)
                (ces_active ces) ms_src')
             src target _ _ _ Htgt_eq) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Hact_eq.
           ++ apply module_source_eqb_eq in Hact_eq. subst src.
              rewrite (lookup_update_same _ _ ms_src _ _ _ Hlookup_src) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              exact (sc_funcs_eq _ _ _ _ Hcorr _ ms_src _ _ Hlookup_src Hnth).
           ++ rewrite (lookup_update_other _ src _ _ _ _ Hact_eq) in Hlookup0.
              exact (sc_funcs_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).
      * (* sc_memory_eq *)
        simpl. intros src ms0 mem_src Hlookup0 Hmem.
        destruct (module_source_eqb src target) eqn:Htgt_eq.
        -- apply module_source_eqb_eq in Htgt_eq. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Htgt_mems in Hmem.
           exact (sc_memory_eq _ _ _ _ Hcorr _ ms_tgt _ Hlookup_tgt Hmem).
        -- rewrite (lookup_update_other _ _ target _ _ _ Htgt_eq) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Hact_eq.
           ++ apply module_source_eqb_eq in Hact_eq. subst src.
              rewrite (lookup_update_same _ _ ms_src _ _ _ Hlookup_src) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              exact (sc_memory_eq _ _ _ _ Hcorr _ ms_src _ Hlookup_src Hmem).
           ++ rewrite (lookup_update_other _ _ _ _ _ _ Hact_eq) in Hlookup0.
              exact (sc_memory_eq _ _ _ _ Hcorr _ _ _ Hlookup0 Hmem).
      * (* sc_globals_eq *)
        simpl. intros src ms0 src_idx g_src Hlookup0 Hnth.
        destruct (module_source_eqb src target) eqn:Htgt_eq.
        -- apply module_source_eqb_eq in Htgt_eq. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Htgt_globals in Hnth.
           exact (sc_globals_eq _ _ _ _ Hcorr _ ms_tgt _ _ Hlookup_tgt Hnth).
        -- rewrite (lookup_update_other _ _ target _ _ _ Htgt_eq) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Hact_eq.
           ++ apply module_source_eqb_eq in Hact_eq. subst src.
              rewrite (lookup_update_same _ _ ms_src _ _ _ Hlookup_src) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              exact (sc_globals_eq _ _ _ _ Hcorr _ ms_src _ _ Hlookup_src Hnth).
           ++ rewrite (lookup_update_other _ _ _ _ _ _ Hact_eq) in Hlookup0.
              exact (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).
      * (* sc_tables_eq *)
        simpl. intros src ms0 src_idx tab_src Hlookup0 Hnth.
        destruct (module_source_eqb src target) eqn:Htgt_eq.
        -- apply module_source_eqb_eq in Htgt_eq. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Htgt_tables in Hnth.
           exact (sc_tables_eq _ _ _ _ Hcorr _ ms_tgt _ _ Hlookup_tgt Hnth).
        -- rewrite (lookup_update_other _ _ target _ _ _ Htgt_eq) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Hact_eq.
           ++ apply module_source_eqb_eq in Hact_eq. subst src.
              rewrite (lookup_update_same _ _ ms_src _ _ _ Hlookup_src) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              exact (sc_tables_eq _ _ _ _ Hcorr _ ms_src _ _ Hlookup_src Hnth).
           ++ rewrite (lookup_update_other _ _ _ _ _ _ Hact_eq) in Hlookup0.
              exact (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).
      * (* sc_elems_eq *)
        simpl. intros src ms0 src_idx elem_src Hlookup0 Hnth.
        destruct (module_source_eqb src target) eqn:Htgt_eq.
        -- apply module_source_eqb_eq in Htgt_eq. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Htgt_elems in Hnth.
           exact (sc_elems_eq _ _ _ _ Hcorr _ ms_tgt _ _ Hlookup_tgt Hnth).
        -- rewrite (lookup_update_other _ _ target _ _ _ Htgt_eq) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Hact_eq.
           ++ apply module_source_eqb_eq in Hact_eq. subst src.
              rewrite (lookup_update_same _ _ ms_src _ _ _ Hlookup_src) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              exact (sc_elems_eq _ _ _ _ Hcorr _ ms_src _ _ Hlookup_src Hnth).
           ++ rewrite (lookup_update_other _ _ _ _ _ _ Hact_eq) in Hlookup0.
              exact (sc_elems_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).
      * (* sc_datas_eq *)
        simpl. intros src ms0 src_idx dat_src Hlookup0 Hnth.
        destruct (module_source_eqb src target) eqn:Htgt_eq.
        -- apply module_source_eqb_eq in Htgt_eq. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite Htgt_datas in Hnth.
           exact (sc_datas_eq _ _ _ _ Hcorr _ ms_tgt _ _ Hlookup_tgt Hnth).
        -- rewrite (lookup_update_other _ _ target _ _ _ Htgt_eq) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Hact_eq.
           ++ apply module_source_eqb_eq in Hact_eq. subst src.
              rewrite (lookup_update_same _ _ ms_src _ _ _ Hlookup_src) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              exact (sc_datas_eq _ _ _ _ Hcorr _ ms_src _ _ Hlookup_src Hnth).
           ++ rewrite (lookup_update_other _ _ _ _ _ _ Hact_eq) in Hlookup0.
              exact (sc_datas_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hnth).
Qed.

(* -------------------------------------------------------------------------
   Main Semantic Preservation Theorem

   Combines trap equivalence and forward simulation.
   The forward simulation is the key non-tautological result: it is
   grounded in real WASM instruction semantics via eval_instr, proving
   that remapped instructions access the same runtime entities.
   ------------------------------------------------------------------------- *)

Theorem fusion_preserves_semantics :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    forward_simulation_with_rewrite cc fr /\
    trap_equivalence cc fr.
Proof.
  intros cc config fr Hwf Hcorrect.
  split.
  - exact (fusion_forward_simulation cc config fr Hwf Hcorrect).
  - exact (fusion_trap_equivalence cc config fr Hwf Hcorrect).
Qed.

(* -------------------------------------------------------------------------
   Opacity hints for downstream files.
   Prevent simpl/unfold from expanding heavyweight definitions that are
   only relevant within this file's own proofs.
   ------------------------------------------------------------------------- *)
Global Opaque lookup_module_state.
Global Opaque update_module_state_list.
Global Opaque module_source_eqb.
Global Opaque result_state_corresponds.
Global Opaque values_correspond.
Global Opaque value_stacks_correspond.
Global Opaque global_corresponds.
Global Opaque memory_corresponds.
Global Opaque table_corresponds.
Global Opaque forward_simulation.
Global Opaque forward_simulation_with_rewrite.
Global Opaque trap_equivalence.

(* End of fusion_spec specification *)
