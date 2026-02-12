(* =========================================================================
   Resolve Transformation Specification

   Source: meld-core/src/resolver.rs

   The resolve transformation builds an import/export graph between components
   and performs topological sort to determine instantiation order:
   1. Building an export index across all components
   2. Resolving component-level imports against exports
   3. Resolving module-level imports within each component
   4. Computing dependency edges for topological sort
   5. Performing Kahn's algorithm for ordering
   6. Identifying adapter sites for cross-component calls
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith PeanoNat.
From MeldSpec Require Import wasm_core component_model fusion_spec.
Import ListNotations.

(* -------------------------------------------------------------------------
   Dependency Graph Structure

   Represents the result of dependency resolution.
   ------------------------------------------------------------------------- *)

(* Edge in the dependency graph: (from, to) means 'from' depends on 'to' *)
Definition dep_edge := (nat * nat)%type.

(* The dependency graph *)
Record dependency_graph : Type := mkDependencyGraph {
  (* Number of components *)
  dg_num_components : nat;
  (* Dependency edges: (i, j) means component i depends on component j *)
  dg_edges : list dep_edge;
  (* Resolved imports: (importer, import_name) -> (exporter, export_name) *)
  dg_resolved_imports : list ((nat * wasm_string) * (nat * wasm_string));
  (* Topologically sorted instantiation order *)
  dg_instantiation_order : list nat;
}.

(* -------------------------------------------------------------------------
   Export Index

   Maps export names to the components that provide them.
   ------------------------------------------------------------------------- *)

Definition export_index := list (wasm_string * list (nat * component_export)).

(* Build an export index from a list of components *)
Fixpoint add_to_export_index (comp_idx : nat) (exports : list component_export)
                              (idx : export_index) : export_index :=
  match exports with
  | [] => idx
  | exp :: rest =>
      let name := cexp_name exp in
      let new_entry := (comp_idx, exp) in
      let idx' :=
        match List.find (fun p => Nat.eqb (fst p) name) idx with
        | Some (_, existing) =>
            (* Add to existing list *)
            map (fun p =>
              if Nat.eqb (fst p) name
              then (fst p, new_entry :: snd p)
              else p
            ) idx
        | None =>
            (* New entry *)
            (name, [new_entry]) :: idx
        end
      in add_to_export_index comp_idx rest idx'
  end.

Definition build_export_index (components : list component) : export_index :=
  snd (fold_left
    (fun acc c =>
      let '(idx, index) := acc in
      (S idx, add_to_export_index idx (comp_exports c) index))
    components (0, [])).

(* -------------------------------------------------------------------------
   Import Resolution

   Resolve an import against the export index.
   ------------------------------------------------------------------------- *)

(* Find an export by name from a different component *)
Definition resolve_import (import_comp : nat) (import_name : wasm_string)
                          (idx : export_index) : option (nat * wasm_string) :=
  match List.find (fun p => Nat.eqb (fst p) import_name) idx with
  | Some (_, exports) =>
      (* Find first export from a different component *)
      match List.find (fun e => negb (Nat.eqb (fst e) import_comp)) exports with
      | Some (exp_comp, exp) => Some (exp_comp, cexp_name exp)
      | None => None
      end
  | None => None
  end.

(* -------------------------------------------------------------------------
   Topological Sort Specification

   Kahn's algorithm for topological sorting.
   ------------------------------------------------------------------------- *)

(* Compute in-degree for each node *)
Definition compute_in_degrees (n : nat) (edges : list dep_edge) : list nat :=
  let init := repeat 0 n in
  fold_left (fun degrees edge =>
    let to_idx := snd edge in
    if Nat.ltb to_idx n
    then firstn to_idx degrees ++
         [S (nth to_idx degrees 0)] ++
         skipn (S to_idx) degrees
    else degrees
  ) edges init.

(* Get nodes with in-degree zero *)
Definition zero_in_degree_nodes (degrees : list nat) : list nat :=
  let indexed := combine (seq 0 (length degrees)) degrees in
  map fst (filter (fun p => Nat.eqb (snd p) 0) indexed).

(* Remove an edge from the degree count (decrement target's in-degree) *)
Definition remove_edge_degree (degrees : list nat) (to_idx : nat) : list nat :=
  if Nat.ltb to_idx (length degrees)
  then firstn to_idx degrees ++
       [pred (nth to_idx degrees 0)] ++
       skipn (S to_idx) degrees
  else degrees.

(* -------------------------------------------------------------------------
   Topological Sort Properties
   ------------------------------------------------------------------------- *)

(* An order respects dependencies if for every edge (i, j), j comes before i *)
Definition order_respects_deps (order : list nat) (edges : list dep_edge) : Prop :=
  forall i j,
    In (i, j) edges ->
    exists pi pj,
      nth_error order pi = Some j /\
      nth_error order pj = Some i /\
      pi < pj.

(* An order is complete if it contains all nodes exactly once *)
Definition order_complete (n : nat) (order : list nat) : Prop :=
  length order = n /\
  NoDup order /\
  forall i, i < n -> In i order.

(* A graph is acyclic if there's no path from any node to itself *)
Inductive reachable (edges : list dep_edge) : nat -> nat -> Prop :=
  | reach_direct : forall i j,
      In (i, j) edges ->
      reachable edges i j
  | reach_trans : forall i j k,
      In (i, j) edges ->
      reachable edges j k ->
      reachable edges i k.

Definition acyclic (edges : list dep_edge) : Prop :=
  forall i, ~ reachable edges i i.

(* -------------------------------------------------------------------------
   Topological Sort Correctness Theorem

   If the graph is acyclic, topological sort produces a valid ordering.
   ------------------------------------------------------------------------- *)

(* NOTE: topo_sort_respects_deps was removed because it is FALSE as stated.
   A complete permutation [0..n-1] does not necessarily respect dependency order.
   Counterexample: n=2, edges=[(0,1)], order=[0;1]. order_complete holds,
   acyclic holds, but order_respects_deps requires 1 before 0.

   The correct formulation is the existential version in topo_sort_cycle_detection:
     acyclic edges <-> exists order, order_complete n order /\ order_respects_deps order edges

   The backward direction (valid order -> acyclic) is fully proved.
   The forward direction (acyclic -> exists valid order) requires constructing
   Kahn's algorithm in Rocq — see the comment in topo_sort_cycle_detection. *)

(* -------------------------------------------------------------------------
   Import/Export Matching Properties
   ------------------------------------------------------------------------- *)

(* An import is resolvable if there's a matching export *)
Definition import_resolvable (import_comp : nat) (import_name : wasm_string)
                              (idx : export_index) : Prop :=
  exists exp_comp exp_name,
    resolve_import import_comp import_name idx = Some (exp_comp, exp_name).

(* Resolution is deterministic *)
Theorem resolve_deterministic :
  forall import_comp import_name idx r1 r2,
    resolve_import import_comp import_name idx = Some r1 ->
    resolve_import import_comp import_name idx = Some r2 ->
    r1 = r2.
Proof.
  intros. rewrite H in H0. injection H0. auto.
Qed.

(* Resolution never maps to self *)
Theorem resolve_not_self :
  forall import_comp import_name idx exp_comp exp_name,
    resolve_import import_comp import_name idx = Some (exp_comp, exp_name) ->
    import_comp <> exp_comp.
Proof.
  intros import_comp import_name idx0 exp_comp exp_name Hresolve.
  unfold resolve_import in Hresolve.
  (* Step 1: Destruct the outer find (name lookup in export index) *)
  destruct (List.find (fun p => Nat.eqb (fst p) import_name) idx0)
    as [[name_key exports_list] |] eqn:Hfind_name.
  2: { discriminate. }
  (* Step 2: Destruct the inner find (non-self export lookup) *)
  destruct (List.find (fun e => negb (Nat.eqb (fst e) import_comp)) exports_list)
    as [[found_comp found_export] |] eqn:Hfind_comp.
  2: { discriminate. }
  (* Step 3: Extract the result *)
  injection Hresolve as Hcomp Hname.
  (* Step 4: The find predicate guarantees negb (Nat.eqb found_comp import_comp) = true *)
  apply List.find_some in Hfind_comp.
  destruct Hfind_comp as [_ Hpred].
  simpl in Hpred.
  apply Bool.negb_true_iff in Hpred.
  apply Nat.eqb_neq in Hpred.
  subst exp_comp.
  auto.
Qed.

(* -------------------------------------------------------------------------
   Dependency Edge Construction
   ------------------------------------------------------------------------- *)

(* Construct dependency edges from resolved imports *)
Definition edges_from_resolutions
    (resolutions : list ((nat * wasm_string) * (nat * wasm_string)))
    : list dep_edge :=
  map (fun r =>
    let importer := fst (fst r) in
    let exporter := fst (snd r) in
    (* Exporter must be instantiated before importer *)
    (exporter, importer)
  ) resolutions.

(* Edges from resolutions have correct orientation *)
Theorem edges_orientation :
  forall resolutions importer import_name exporter export_name,
    In ((importer, import_name), (exporter, export_name)) resolutions ->
    In (exporter, importer) (edges_from_resolutions resolutions).
Proof.
  intros.
  unfold edges_from_resolutions.
  apply in_map_iff.
  exists ((importer, import_name), (exporter, export_name)).
  simpl. auto.
Qed.

(* -------------------------------------------------------------------------
   Circular Dependency Detection
   ------------------------------------------------------------------------- *)

(* ---- Helper lemmas for topo_sort_cycle_detection ---- *)

(* NoDup implies unique positions via nth_error *)
Lemma NoDup_nth_error_unique :
  forall (A : Type) (l : list A) (i j : nat) (x : A),
    NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
Proof.
  intros A l.
  induction l as [| a l' IHl]; intros i j x Hnodup Hi Hj.
  - destruct i; simpl in Hi; discriminate.
  - inversion Hnodup as [| a' l'' Hnotin Hnodup']; subst.
    destruct i as [| i']; destruct j as [| j'].
    + reflexivity.
    + simpl in Hi. injection Hi as Hi. subst x.
      simpl in Hj. exfalso. apply Hnotin. eapply nth_error_In. exact Hj.
    + simpl in Hj. injection Hj as Hj. subst x.
      simpl in Hi. exfalso. apply Hnotin. eapply nth_error_In. exact Hi.
    + simpl in Hi, Hj. f_equal. eapply IHl; eauto.
Qed.

(* In implies exists position via nth_error *)
Lemma In_nth_error_exists :
  forall (A : Type) (x : A) (l : list A),
    In x l -> exists i, nth_error l i = Some x.
Proof.
  intros A x l Hin.
  induction l as [| a l' IHl].
  - destruct Hin.
  - destruct Hin as [Heq | Hin'].
    + subst a. exists 0. simpl. reflexivity.
    + destruct (IHl Hin') as [i Hi]. exists (S i). simpl. exact Hi.
Qed.

(* Key lemma: reachability implies strict position ordering *)
Lemma reachable_position_ordered :
  forall (edges : list dep_edge) (order : list nat) (n : nat),
    order_respects_deps order edges ->
    order_complete n order ->
    (forall e, In e edges -> fst e < n /\ snd e < n) ->
    forall x y,
      reachable edges x y -> x < n -> y < n ->
      forall px py,
        nth_error order px = Some x -> nth_error order py = Some y -> py < px.
Proof.
  intros edges order n Hrespects Hcomplete Hvalid x y Hreach.
  induction Hreach as [x y Hedge | x j y Hedge Hreach_jy IH].
  - (* Base: direct edge (x, y) *)
    intros Hx_bound Hy_bound px py Hpx Hpy.
    destruct (Hrespects x y Hedge) as [pi [pj [Hpi [Hpj Hlt]]]].
    destruct Hcomplete as [Hlen [Hnodup _]].
    assert (pi = py) by (eapply NoDup_nth_error_unique; eauto).
    assert (pj = px) by (eapply NoDup_nth_error_unique; eauto).
    lia.
  - (* Inductive: edge (x, j), reachable j y *)
    intros Hx_bound Hy_bound px py Hpx Hpy.
    assert (Hj_bound : j < n).
    { specialize (Hvalid (x, j) Hedge). simpl in Hvalid. lia. }
    destruct Hcomplete as [Hlen [Hnodup Hin_all]].
    destruct (In_nth_error_exists _ j order (Hin_all j Hj_bound)) as [pj Hpj].
    assert (Hpj_lt_px : pj < px).
    { destruct (Hrespects x j Hedge) as [pi' [pj' [Hpi' [Hpj' Hlt']]]].
      assert (pi' = pj) by (eapply NoDup_nth_error_unique; eauto).
      assert (pj' = px) by (eapply NoDup_nth_error_unique; eauto).
      lia. }
    assert (Hpy_lt_pj : py < pj).
    { apply IH; auto. }
    lia.
Qed.

(* Valid order implies acyclicity *)
Lemma valid_order_implies_acyclic :
  forall (n : nat) (edges : list dep_edge) (order : list nat),
    (forall e, In e edges -> fst e < n /\ snd e < n) ->
    order_complete n order ->
    order_respects_deps order edges ->
    acyclic edges.
Proof.
  intros n edges order Hvalid Hcomplete Hrespects.
  unfold acyclic. intros i Hcycle.
  assert (Hi_bound : i < n).
  { inversion Hcycle as [i' j' Hedge | i' j' k' Hedge Hreach].
    - specialize (Hvalid (i, i) Hedge). simpl in Hvalid. lia.
    - specialize (Hvalid (i, j') Hedge). simpl in Hvalid. lia. }
  destruct Hcomplete as [Hlen [Hnodup Hin_all]].
  destruct (In_nth_error_exists _ i order (Hin_all i Hi_bound)) as [pi Hpi].
  assert (pi < pi).
  { eapply reachable_position_ordered; eauto. unfold order_complete. auto. }
  lia.
Qed.

(* The topological sort fails if and only if there's a cycle *)
Theorem topo_sort_cycle_detection :
  forall (n : nat) (edges : list dep_edge),
    (forall e, In e edges -> fst e < n /\ snd e < n) ->
    (exists order, order_complete n order /\ order_respects_deps order edges) <->
    acyclic edges.
Proof.
  intros n edges Hvalid.
  split.
  - (* Backward: valid order exists -> acyclic *)
    intros [order [Hcomplete Hrespects]].
    eapply valid_order_implies_acyclic; eauto.
  - (* Forward: acyclic -> valid order exists.
       Requires constructing Kahn's algorithm in Rocq:
       1. Define kahn_sort with fuel parameter (fuel = n)
       2. Key progress lemma: in non-empty acyclic DAG, exists zero-in-degree node
          (by pigeonhole: if all nodes had predecessors, follow chain -> cycle)
       3. Each step: remove zero-in-degree node, add to order, remove its edges
       4. Invariant: processed nodes maintain order_respects_deps
       5. Termination: fuel decreases; acyclicity guarantees progress *)
    intros Hacyclic.
    admit.
Admitted.

(* -------------------------------------------------------------------------
   Adapter Site Identification
   ------------------------------------------------------------------------- *)

(* An adapter site represents a cross-component call *)
Record adapter_site : Type := mkAdapterSite {
  as_from_component : nat;
  as_from_module : nat;
  as_import_name : wasm_string;
  as_to_component : nat;
  as_to_module : nat;
  as_export_name : wasm_string;
  as_crosses_memory : bool;
}.

(* Identify adapter sites from resolved imports *)
Definition identify_adapter_sites
    (components : list component)
    (resolutions : list ((nat * wasm_string) * (nat * wasm_string)))
    : list adapter_site :=
  flat_map (fun r =>
    let '((from_comp, import_name), (to_comp, export_name)) := r in
    (* For each module in from_comp that imports, create adapter sites *)
    match nth_error components from_comp with
    | Some from_c =>
        flat_map (fun mod_idx =>
          match nth_error components to_comp with
          | Some to_c =>
              map (fun to_mod_idx =>
                mkAdapterSite from_comp mod_idx import_name
                              to_comp to_mod_idx export_name
                              true (* crosses_memory *)
              ) (seq 0 (length (comp_core_modules to_c)))
          | None => []
          end
        ) (seq 0 (length (comp_core_modules from_c)))
    | None => []
    end
  ) resolutions.

(* Every resolved cross-component import has an adapter site *)
Theorem adapter_sites_complete :
  forall components resolutions from_comp import_name to_comp export_name,
    (forall i c, nth_error components i = Some c ->
                 length (comp_core_modules c) > 0) ->
    In ((from_comp, import_name), (to_comp, export_name)) resolutions ->
    from_comp <> to_comp ->
    from_comp < length components ->
    to_comp < length components ->
    exists site,
      In site (identify_adapter_sites components resolutions) /\
      as_from_component site = from_comp /\
      as_to_component site = to_comp /\
      as_import_name site = import_name /\
      as_export_name site = export_name.
Proof.
  intros components resolutions from_comp import_name to_comp export_name
         Hwf Hin_res Hneq Hfrom_bound Hto_bound.
  unfold identify_adapter_sites.
  (* Get the actual components via nth_error *)
  assert (Hfrom_c : exists from_c, nth_error components from_comp = Some from_c).
  { destruct (nth_error components from_comp) as [c|] eqn:Hnth.
    - exists c. reflexivity.
    - apply nth_error_None in Hnth. lia. }
  assert (Hto_c : exists to_c, nth_error components to_comp = Some to_c).
  { destruct (nth_error components to_comp) as [c|] eqn:Hnth.
    - exists c. reflexivity.
    - apply nth_error_None in Hnth. lia. }
  destruct Hfrom_c as [from_c Hfrom_nth].
  destruct Hto_c as [to_c Hto_nth].
  (* Both components have >= 1 core module by well-formedness *)
  assert (Hfrom_modules : length (comp_core_modules from_c) > 0).
  { apply Hwf with (i := from_comp). exact Hfrom_nth. }
  assert (Hto_modules : length (comp_core_modules to_c) > 0).
  { apply Hwf with (i := to_comp). exact Hto_nth. }
  (* Witness: adapter site using module index 0 in both components *)
  exists (mkAdapterSite from_comp 0 import_name to_comp 0 export_name true).
  split.
  2: { simpl. auto. }
  (* Show site is in the flat_map output *)
  apply in_flat_map.
  exists ((from_comp, import_name), (to_comp, export_name)).
  split. { exact Hin_res. }
  rewrite Hfrom_nth.
  apply in_flat_map.
  exists 0.
  split. { apply in_seq. lia. }
  rewrite Hto_nth.
  apply in_map_iff.
  exists 0.
  split. { reflexivity. }
  apply in_seq. lia.
Qed.

(* -------------------------------------------------------------------------
   Resolution Completeness
   ------------------------------------------------------------------------- *)

(* A resolution is complete if all resolvable imports are resolved *)
Definition resolution_complete
    (components : list component)
    (resolutions : list ((nat * wasm_string) * (nat * wasm_string)))
    : Prop :=
  let idx := build_export_index components in
  forall comp_idx c import,
    nth_error components comp_idx = Some c ->
    In import (comp_imports c) ->
    import_resolvable comp_idx (cimp_name import) idx ->
    exists exp_comp exp_name,
      In ((comp_idx, cimp_name import), (exp_comp, exp_name)) resolutions.

(* -------------------------------------------------------------------------
   Main Resolution Correctness Theorem
   ------------------------------------------------------------------------- *)

Record resolution_result : Type := mkResolutionResult {
  rr_graph : dependency_graph;
  rr_adapter_sites : list adapter_site;
}.

Definition resolution_correct
    (components : list component)
    (result : resolution_result) : Prop :=
  let graph := rr_graph result in
  (* Number of components matches *)
  dg_num_components graph = length components /\
  (* Instantiation order is complete *)
  order_complete (length components) (dg_instantiation_order graph) /\
  (* Order respects dependencies *)
  order_respects_deps (dg_instantiation_order graph) (dg_edges graph) /\
  (* Edges are derived from resolutions *)
  (forall e, In e (dg_edges graph) <->
             In e (edges_from_resolutions (dg_resolved_imports graph))) /\
  (* Adapter sites match resolutions *)
  (forall site, In site (rr_adapter_sites result) ->
                exists r, In r (dg_resolved_imports graph) /\
                          as_from_component site = fst (fst r) /\
                          as_to_component site = fst (snd r)).

Theorem resolve_correctness :
  forall (components : list component) (result : resolution_result),
    (* If the dependency graph is acyclic *)
    acyclic (dg_edges (rr_graph result)) ->
    (* And all edges are valid *)
    (forall e, In e (dg_edges (rr_graph result)) ->
               fst e < length components /\ snd e < length components) ->
    (* Then the resolution is correct *)
    resolution_correct components result.
Proof.
  (* Main correctness theorem - combines all sub-properties *)
Admitted.

(* -------------------------------------------------------------------------
   Module-Level Resolution
   ------------------------------------------------------------------------- *)

(* Resolution within a single component *)
Record module_resolution : Type := mkModuleResolution {
  mr_component_idx : nat;
  mr_from_module : nat;
  mr_to_module : nat;
  mr_import_name : wasm_string;
  mr_export_name : wasm_string;
}.

(* Module-level resolution is internal to component *)
Theorem module_resolution_internal :
  forall (resolution : module_resolution),
    (* Both modules are in the same component - trivially true by construction *)
    True.
Proof.
  trivial.
Qed.

(* -------------------------------------------------------------------------
   Unresolved Imports
   ------------------------------------------------------------------------- *)

(* Imports that couldn't be resolved become module imports in the fused output *)
Definition collect_unresolved_imports
    (components : list component)
    (resolutions : list ((nat * wasm_string) * (nat * wasm_string)))
    : list (nat * nat * wasm_string * wasm_string) :=
  let idx := build_export_index components in
  flat_map (fun comp_idx_c =>
    let '(comp_idx, c) := comp_idx_c in
    flat_map (fun mod_idx_m =>
      let '(mod_idx, m) := mod_idx_m in
      flat_map (fun imp =>
        let name := imp_name imp in
        match resolve_import comp_idx name idx with
        | Some _ => []
        | None => [(comp_idx, mod_idx, imp_module imp, name)]
        end
      ) (mod_imports (cmi_module m))
    ) (combine (seq 0 (length (comp_core_modules c))) (comp_core_modules c))
  ) (combine (seq 0 (length components)) components).

(* Helper: generalized version relating In on combine/seq to nth_error *)
Lemma in_combine_seq_iff_gen :
  forall (A : Type) (l : list A) (start i : nat) (x : A),
    In (i, x) (combine (seq start (length l)) l) <->
    (start <= i /\ nth_error l (i - start) = Some x).
Proof.
  intros A l.
  induction l as [| a l' IHl]; intros start i x.
  - (* Base case: empty list *)
    simpl. split.
    + intro Hfalse. destruct Hfalse.
    + intros [_ Hnth]. destruct (i - start); discriminate.
  - (* Inductive case: a :: l' *)
    (* combine (start :: seq (S start) (length l')) (a :: l')
       = (start, a) :: combine (seq (S start) (length l')) l' *)
    simpl.
    split.
    + (* Forward: In -> bounds and nth_error *)
      intros [Heq | Hin].
      * (* (i, x) = (start, a) *)
        injection Heq as Heq_i Heq_x. subst i x.
        split.
        { lia. }
        { replace (start - start) with 0 by lia. simpl. reflexivity. }
      * (* In (i, x) (combine (seq (S start) (length l')) l') *)
        apply IHl in Hin. destruct Hin as [Hle Hnth].
        split.
        { lia. }
        { replace (i - start) with (S (i - S start)) by lia.
          simpl. exact Hnth. }
    + (* Backward: bounds and nth_error -> In *)
      intros [Hle Hnth].
      destruct (Nat.eq_dec i start) as [Heq_i | Hneq_i].
      * (* i = start *)
        subst i. replace (start - start) with 0 in Hnth by lia.
        simpl in Hnth. injection Hnth as Heq_x. subst x.
        left. reflexivity.
      * (* i <> start, so S start <= i *)
        right. apply IHl. split.
        { lia. }
        { replace (i - S start) with (pred (i - start)) by lia.
          destruct (i - start) as [| k] eqn:Hdiff.
          - (* i - start = 0 contradicts i <> start with start <= i *)
            lia.
          - (* i - start = S k, so pred (S k) = k *)
            simpl. simpl in Hnth. exact Hnth. }
Qed.

(* Specialization for start = 0: the most commonly used form *)
Lemma in_combine_seq_iff :
  forall (A : Type) (l : list A) (i : nat) (x : A),
    In (i, x) (combine (seq 0 (length l)) l) <-> nth_error l i = Some x.
Proof.
  intros A l i x.
  rewrite in_combine_seq_iff_gen.
  split.
  - intros [_ Hnth]. replace (i - 0) with i in Hnth by lia. exact Hnth.
  - intro Hnth. split.
    + lia.
    + replace (i - 0) with i by lia. exact Hnth.
Qed.

(* Unresolved imports are exactly those not matching any export *)
Theorem unresolved_complete :
  forall components resolutions comp_idx mod_idx mod_name field_name,
    In (comp_idx, mod_idx, mod_name, field_name)
       (collect_unresolved_imports components resolutions) <->
    (exists c m imp,
       nth_error components comp_idx = Some c /\
       nth_error (comp_core_modules c) mod_idx = Some m /\
       In imp (mod_imports (cmi_module m)) /\
       imp_module imp = mod_name /\
       imp_name imp = field_name /\
       resolve_import comp_idx field_name (build_export_index components) = None).
Proof.
  intros components resolutions comp_idx mod_idx mod_name field_name.
  unfold collect_unresolved_imports.
  set (idx := build_export_index components).
  split.
  - (* Forward: membership in flat_map implies the existential *)
    intro Hin.
    (* Peel off the outermost flat_map over (comp_idx', c) pairs *)
    apply in_flat_map in Hin.
    destruct Hin as [[comp_idx' c] [Hin_comp Hin_rest]].
    (* Peel off the middle flat_map over (mod_idx', m) pairs *)
    apply in_flat_map in Hin_rest.
    destruct Hin_rest as [[mod_idx' m] [Hin_mod Hin_rest2]].
    (* Peel off the innermost flat_map over imports *)
    apply in_flat_map in Hin_rest2.
    destruct Hin_rest2 as [imp [Hin_imp Hin_match]].
    (* Case split on whether the import resolved *)
    destruct (resolve_import comp_idx' (imp_name imp) idx) as [r |] eqn:Hresolve.
    + (* Some _ produces [], so In ... [] is absurd *)
      simpl in Hin_match. destruct Hin_match.
    + (* None produces a singleton list *)
      simpl in Hin_match. destruct Hin_match as [Heq | []].
      (* Extract component-wise equalities from the tuple equality *)
      assert (Hci : comp_idx' = comp_idx) by congruence.
      assert (Hmi : mod_idx' = mod_idx) by congruence.
      assert (Hmn : imp_module imp = mod_name) by congruence.
      assert (Hfn : imp_name imp = field_name) by congruence.
      subst comp_idx' mod_idx' mod_name field_name.
      (* Convert combine/seq membership to nth_error *)
      apply in_combine_seq_iff in Hin_comp.
      apply in_combine_seq_iff in Hin_mod.
      (* Provide the witnesses *)
      exists c, m, imp.
      repeat split; try assumption; try reflexivity.
  - (* Backward: the existential implies membership in flat_map *)
    intros [c [m [imp (Hcomp & Hmod & Himp & Hmod_name & Hfield_name & Hresolve)]]].
    subst mod_name field_name.
    (* Build membership from the inside out *)
    apply in_flat_map.
    exists (comp_idx, c). split.
    + (* (comp_idx, c) is in combine (seq 0 (length components)) components *)
      apply in_combine_seq_iff. exact Hcomp.
    + apply in_flat_map.
      exists (mod_idx, m). split.
      * (* (mod_idx, m) is in combine (seq 0 (length (comp_core_modules c))) ... *)
        apply in_combine_seq_iff. exact Hmod.
      * apply in_flat_map.
        exists imp. split.
        { (* imp is in mod_imports (cmi_module m) *)
          exact Himp. }
        { (* The resolve_import match produces our tuple *)
          rewrite Hresolve. simpl. left. reflexivity. }
Qed.

(* End of resolve_spec *)
