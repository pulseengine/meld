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

(* =========================================================================
   Forward Direction: Acyclic -> Valid Topological Order Exists

   Proof strategy:
   1. Progress lemma: in a non-empty acyclic DAG, a source node exists
      (node with no outgoing edges). Proved by contradiction using a
      walk + pigeonhole argument.
   2. Main construction: strong induction on the number of nodes.
      Remove a source, recurse on the remaining nodes, prepend the source.
   ========================================================================= *)

(* ---- Definitions ---- *)

(* Iterate a function k times *)
Fixpoint nat_iter (k : nat) (f : nat -> nat) (x : nat) : nat :=
  match k with
  | 0 => x
  | S k' => f (nat_iter k' f x)
  end.

(* Find the target of the first outgoing edge from node v *)
Definition find_dep (v : nat) (edges : list dep_edge) : option nat :=
  match List.find (fun e => Nat.eqb (fst e) v) edges with
  | Some e => Some (snd e)
  | None => None
  end.

(* Build a walk by iterating a successor function *)
Fixpoint dep_walk (next : nat -> nat) (start fuel : nat) : list nat :=
  match fuel with
  | 0 => [start]
  | S fuel' => start :: dep_walk next (next start) fuel'
  end.

(* Remove a node from a list *)
Definition remove_node (v : nat) (l : list nat) : list nat :=
  filter (fun x => negb (Nat.eqb x v)) l.

(* Restrict edges to those with both endpoints in a given node set *)
Definition restrict_edges_to (nodes : list nat) (edges : list dep_edge)
    : list dep_edge :=
  filter (fun e =>
    existsb (Nat.eqb (fst e)) nodes &&
    existsb (Nat.eqb (snd e)) nodes
  ) edges.

(* ---- nat_iter lemmas ---- *)

Lemma nat_iter_succ : forall k (f : nat -> nat) x,
  nat_iter k f (f x) = nat_iter (S k) f x.
Proof.
  induction k as [|k' IH]; intros f x; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma nat_iter_add : forall a b (f : nat -> nat) x,
  nat_iter a f (nat_iter b f x) = nat_iter (a + b) f x.
Proof.
  induction a as [|a' IH]; intros b f x; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(* ---- find_dep lemmas ---- *)

Lemma find_dep_Some_In : forall v edges j,
  find_dep v edges = Some j -> In (v, j) edges.
Proof.
  unfold find_dep. intros v edges j Hfind.
  destruct (List.find _ edges) as [e|] eqn:Hf; [| discriminate].
  apply List.find_some in Hf. destruct Hf as [Hin Hpred].
  injection Hfind as Hj. subst j.
  simpl in Hpred. apply Nat.eqb_eq in Hpred.
  destruct e as [a b]. simpl in *. subst a. exact Hin.
Qed.

Lemma find_dep_None_no_edge : forall v edges,
  find_dep v edges = None -> forall j, ~ In (v, j) edges.
Proof.
  unfold find_dep. intros v edges Hfind j Hin.
  destruct (List.find _ edges) as [e|] eqn:Hf; [discriminate |].
  apply (List.find_none _ _ Hf) in Hin.
  simpl in Hin. rewrite Nat.eqb_refl in Hin. discriminate.
Qed.

(* ---- dep_walk lemmas ---- *)

Lemma dep_walk_length : forall next start fuel,
  length (dep_walk next start fuel) = S fuel.
Proof.
  intros next start fuel. revert start.
  induction fuel as [|fuel' IH]; intros start; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma dep_walk_nth : forall next start fuel k,
  k <= fuel ->
  nth_error (dep_walk next start fuel) k = Some (nat_iter k next start).
Proof.
  intros next start fuel. revert start.
  induction fuel as [|fuel' IH]; intros start k Hk.
  - replace k with 0 by lia. simpl. reflexivity.
  - destruct k as [|k'].
    + simpl. reflexivity.
    + simpl. rewrite IH by lia. f_equal. symmetry. apply nat_iter_succ.
Qed.

(* All elements of a walk satisfy a property preserved by the step function *)
Lemma dep_walk_all : forall next start fuel (P : nat -> Prop),
  P start ->
  (forall v, P v -> P (next v)) ->
  forall x, In x (dep_walk next start fuel) -> P x.
Proof.
  intros next start fuel P Hstart Hstep.
  revert start Hstart.
  induction fuel as [|fuel' IH]; intros start Hstart x Hx; simpl in Hx.
  - destruct Hx as [<- | []]. exact Hstart.
  - destruct Hx as [<- | Hx'].
    + exact Hstart.
    + exact (IH (next start) (Hstep start Hstart) x Hx').
Qed.

(* ---- Pigeonhole and NoDup extraction ---- *)

(* NoDup is preserved by filter *)
Lemma NoDup_filter_nat : forall (f : nat -> bool) (l : list nat),
  NoDup l -> NoDup (filter f l).
Proof.
  intros f l Hnd. induction l as [|a l' IH].
  - simpl. constructor.
  - inversion Hnd as [| ? ? Hnotin Hnd']. subst.
    simpl. destruct (f a) eqn:Hfa.
    + constructor.
      * intro Habs. apply filter_In in Habs. tauto.
      * apply IH. exact Hnd'.
    + apply IH. exact Hnd'.
Qed.

(* filter never increases length *)
Lemma filter_length_le : forall (A : Type) (f : A -> bool) (l : list A),
  length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [|a l' IH]; simpl.
  - lia.
  - destruct (f a); simpl; lia.
Qed.

(* A NoDup list with all elements < n has length at most n *)
Lemma NoDup_bounded_length : forall n (l : list nat),
  NoDup l -> (forall x, In x l -> x < n) -> length l <= n.
Proof.
  induction n as [|n' IH]; intros l Hnd Hbound.
  - (* n = 0: no elements possible *)
    destruct l as [|a l'].
    + simpl. lia.
    + exfalso. specialize (Hbound a (or_introl eq_refl)). lia.
  - (* n = S n' *)
    destruct (In_dec Nat.eq_dec n' l) as [Hin | Hnotin].
    + (* n' in l: remove it and apply IH *)
      set (l' := remove_node n' l).
      assert (Hnd' : NoDup l') by (apply remove_node_NoDup; exact Hnd).
      assert (Hbound' : forall x, In x l' -> x < n').
      { intros x Hx. apply remove_node_In_iff in Hx. destruct Hx as [Hx Hneq].
        specialize (Hbound x Hx). lia. }
      specialize (IH l' Hnd' Hbound').
      assert (Hlen_eq : length l' = pred (length l)).
      { apply remove_node_length_pred; assumption. }
      destruct l as [|a0 l0]; [destruct Hin |]. simpl in Hlen_eq |- *. lia.
    + (* n' not in l: all elements < n' *)
      assert (Hbound' : forall x, In x l -> x < n').
      { intros x Hx. specialize (Hbound x Hx).
        assert (x <> n') by (intro; subst; contradiction). lia. }
      specialize (IH l Hnd Hbound'). lia.
Qed.

(* NoDup sublist has length <= superlist *)
Lemma NoDup_incl_NoDup_length : forall (l l' : list nat),
  NoDup l -> NoDup l' -> incl l l' -> length l <= length l'.
Proof.
  intros l l' Hnd Hnd' Hincl.
  revert l Hnd Hincl.
  induction l' as [|a l'' IH]; intros l Hnd Hincl.
  - destruct l as [|b ?].
    + simpl. lia.
    + exfalso. specialize (Hincl b (or_introl eq_refl)). destruct Hincl.
  - inversion Hnd' as [| ? ? Hnotin Hnd'']. subst.
    destruct (In_dec Nat.eq_dec a l) as [Hin | Hnotin_l].
    + (* a in l: remove a from l, recurse *)
      set (l_rem := remove_node a l).
      assert (Hnd_rem : NoDup l_rem) by (apply remove_node_NoDup; exact Hnd).
      assert (Hincl_rem : incl l_rem l'').
      { intros x Hx. apply remove_node_In_iff in Hx. destruct Hx as [Hx Hneq].
        specialize (Hincl x Hx). simpl in Hincl. destruct Hincl as [<- | Hx'].
        - exfalso. apply Hneq. reflexivity.
        - exact Hx'. }
      specialize (IH Hnd'' l_rem Hnd_rem Hincl_rem).
      assert (Hlen_rem : length l_rem = pred (length l)).
      { apply remove_node_length_pred; assumption. }
      destruct l as [|b ?]; [destruct Hin |]. simpl in *. lia.
    + (* a not in l: all elements go to l'' *)
      assert (Hincl' : incl l l'').
      { intros x Hx. specialize (Hincl x Hx). simpl in Hincl.
        destruct Hincl as [<- | Hx']; [exfalso; apply Hnotin_l; exact Hx | exact Hx']. }
      specialize (IH Hnd'' l Hnd Hincl'). simpl. lia.
Qed.

(* A list longer than n with elements < n cannot be NoDup *)
Lemma too_long_not_NoDup : forall (l : list nat) n,
  (forall x, In x l -> x < n) -> length l > n -> ~ NoDup l.
Proof.
  intros l n Hbound Hlen Hnd.
  assert (length l <= n) by (apply NoDup_bounded_length; assumption).
  lia.
Qed.

(* Extract a repeated element from a non-NoDup list *)
Lemma not_NoDup_has_repeat : forall (l : list nat),
  ~ NoDup l ->
  exists x i j, i < j /\ j < length l /\
    nth_error l i = Some x /\ nth_error l j = Some x.
Proof.
  induction l as [|a l' IH].
  - intro H. exfalso. apply H. constructor.
  - intro Hnodup.
    destruct (In_dec Nat.eq_dec a l') as [Hin | Hnotin].
    + (* a appears again in l' *)
      apply In_nth_error_exists in Hin. destruct Hin as [k Hk].
      exists a, 0, (S k). repeat split.
      * lia.
      * simpl. enough (k < length l') by lia.
        apply nth_error_Some. rewrite Hk. discriminate.
      * simpl. reflexivity.
      * simpl. exact Hk.
    + (* a not in l', so l' itself is not NoDup *)
      assert (Hnd' : ~ NoDup l').
      { intro Hnd. apply Hnodup. constructor; assumption. }
      destruct (IH Hnd') as [x [i [j [Hij [Hj_bound [Hi_eq Hj_eq]]]]]].
      exists x, (S i), (S j). repeat split.
      * lia.
      * simpl. lia.
      * simpl. exact Hi_eq.
      * simpl. exact Hj_eq.
Qed.

(* ---- Reachability helpers ---- *)

(* Reachability is monotone: more edges means more reachability *)
Lemma reachable_subset : forall edges edges' x y,
  (forall e, In e edges' -> In e edges) ->
  reachable edges' x y -> reachable edges x y.
Proof.
  intros edges edges' x y Hsub Hreach.
  induction Hreach as [i j Hin | i j k Hin _ IH].
  - apply reach_direct. apply Hsub. exact Hin.
  - apply reach_trans with (j := j); [apply Hsub; exact Hin | exact IH].
Qed.

(* Iterating a successor function produces a reachable chain *)
Lemma reachable_chain : forall edges (f : nat -> nat) (P : nat -> Prop)
    start steps,
  steps > 0 ->
  (forall v, P v -> In (v, f v) edges) ->
  (forall v, P v -> P (f v)) ->
  P start ->
  reachable edges start (nat_iter steps f start).
Proof.
  intros edges f P start steps Hsteps Hedge Hpres Hstart.
  revert start Hstart.
  induction steps as [|s' IH]; intros start Hstart.
  - lia.
  - destruct s'.
    + (* steps = 1 *)
      simpl. apply reach_direct. apply Hedge. exact Hstart.
    + (* steps >= 2 *)
      simpl. apply reach_trans with (j := f start).
      * apply Hedge. exact Hstart.
      * rewrite <- nat_iter_succ. apply IH; [lia | apply Hpres; exact Hstart].
Qed.

(* ---- Progress lemma ---- *)

(* In any non-empty acyclic graph on {0..n-1}, there exists a source node
   (one with no outgoing edges).

   Proof by contradiction: if every node had a successor, build a walk of
   length n+1 through n nodes. By pigeonhole, some node repeats. The path
   between the two visits to that node forms a cycle, contradicting acyclicity. *)
Lemma acyclic_has_source : forall n edges,
  n > 0 ->
  (forall e, In e edges -> fst e < n /\ snd e < n) ->
  acyclic edges ->
  exists v, v < n /\ forall j, ~ In (v, j) edges.
Proof.
  intros n edges Hn Hvalid Hacyclic.
  (* Check whether any node in {0..n-1} is a source *)
  destruct (existsb
    (fun v => match find_dep v edges with None => true | Some _ => false end)
    (seq 0 n)) eqn:Hcheck.
  - (* Found a source *)
    apply existsb_exists in Hcheck.
    destruct Hcheck as [v [Hv_in Hv_src]].
    apply in_seq in Hv_in.
    exists v. split; [lia |].
    destruct (find_dep v edges) as [j|] eqn:Hfd; [discriminate |].
    exact (find_dep_None_no_edge v edges Hfd).
  - (* No source exists: derive contradiction *)
    exfalso.
    (* Every node has a successor via find_dep *)
    assert (Hall : forall v, v < n -> exists j, find_dep v edges = Some j).
    { intros v Hv.
      destruct (find_dep v edges) as [j|] eqn:Hfd.
      - exists j. reflexivity.
      - exfalso.
        assert (Htrue : existsb
          (fun v0 => match find_dep v0 edges with None => true | Some _ => false end)
          (seq 0 n) = true).
        { apply existsb_exists. exists v.
          split; [apply in_seq; lia | rewrite Hfd; reflexivity]. }
        rewrite Htrue in Hcheck. discriminate. }
    (* Define total successor function with arbitrary default *)
    set (next := fun v =>
      match find_dep v edges with Some j => j | None => 0 end).
    (* Properties of next on {0..n-1} *)
    assert (Hnext_edge : forall v, v < n -> In (v, next v) edges).
    { intros v Hv. unfold next.
      destruct (Hall v Hv) as [j Hj]. rewrite Hj.
      exact (find_dep_Some_In v edges j Hj). }
    assert (Hnext_bound : forall v, v < n -> next v < n).
    { intros v Hv.
      specialize (Hvalid _ (Hnext_edge v Hv)). simpl in Hvalid. lia. }
    (* Build walk of length n+1 starting from 0 *)
    set (w := dep_walk next 0 n).
    assert (Hw_len : length w = S n) by apply dep_walk_length.
    assert (Hw_bound : forall x, In x w -> x < n).
    { apply dep_walk_all with (P := fun x => x < n); [lia | exact Hnext_bound]. }
    (* Pigeonhole: n+1 values in {0..n-1} cannot all be distinct *)
    assert (Hw_not_nodup : ~ NoDup w).
    { apply too_long_not_NoDup with (n := n); [exact Hw_bound | lia]. }
    (* Extract the repeated element *)
    destruct (not_NoDup_has_repeat w Hw_not_nodup)
      as [x [i [j [Hij [Hj_len [Hi_eq Hj_eq]]]]]].
    (* Relate walk positions to nat_iter *)
    assert (Hi_le : i <= n) by lia.
    assert (Hj_le : j <= n) by lia.
    pose proof (dep_walk_nth next 0 n i Hi_le) as Hi_nth.
    pose proof (dep_walk_nth next 0 n j Hj_le) as Hj_nth.
    (* Both positions hold the same value x *)
    assert (Hi_val : nat_iter i next 0 = x).
    { rewrite Hi_nth in Hi_eq. congruence. }
    assert (Hj_val : nat_iter j next 0 = x).
    { rewrite Hj_nth in Hj_eq. congruence. }
    (* Build reachable path from position i to position j *)
    assert (Hreach : reachable edges x x).
    { rewrite <- Hi_val, <- Hj_val.
      replace j with (i + (j - i)) by lia.
      rewrite <- nat_iter_add.
      apply reachable_chain with (P := fun v => v < n).
      - lia.
      - exact Hnext_edge.
      - exact Hnext_bound.
      - rewrite Hi_val. apply Hw_bound.
        eapply nth_error_In. exact Hi_eq. }
    (* Contradicts acyclicity *)
    exact (Hacyclic x Hreach).
Qed.

(* ---- Node removal and edge restriction lemmas ---- *)

Lemma mem_nat_In : forall x l,
  existsb (Nat.eqb x) l = true <-> In x l.
Proof.
  intros x l. split.
  - intro H. apply existsb_exists in H.
    destruct H as [y [Hy Heqb]].
    apply Nat.eqb_eq in Heqb. subst. exact Hy.
  - intro H. apply existsb_exists.
    exists x. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma remove_node_not_In : forall v l, ~ In v (remove_node v l).
Proof.
  intros v l Hin. unfold remove_node in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hpred].
  simpl in Hpred. rewrite Nat.eqb_refl in Hpred. discriminate.
Qed.

Lemma remove_node_In_iff : forall v x l,
  In x (remove_node v l) <-> In x l /\ x <> v.
Proof.
  intros v x l. unfold remove_node. rewrite filter_In. simpl.
  rewrite Bool.negb_true_iff, Nat.eqb_neq. tauto.
Qed.

Lemma remove_node_NoDup : forall v l, NoDup l -> NoDup (remove_node v l).
Proof.
  intros v l Hnd. unfold remove_node. apply NoDup_filter_nat. exact Hnd.
Qed.

(* filter that preserves all elements when predicate is always true *)
Lemma filter_id : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros A f l Hf. induction l as [|a l' IH]; simpl.
  - reflexivity.
  - rewrite (Hf a (or_introl eq_refl)). f_equal.
    apply IH. intros x Hx. apply Hf. right. exact Hx.
Qed.

Lemma remove_node_length_lt : forall v l,
  In v l -> length (remove_node v l) < length l.
Proof.
  intros v l Hin. unfold remove_node.
  induction l as [|a l' IH].
  - destruct Hin.
  - simpl. destruct (negb (Nat.eqb a v)) eqn:Hpred.
    + (* a <> v: keep a *)
      apply Bool.negb_true_iff in Hpred. apply Nat.eqb_neq in Hpred.
      simpl. destruct Hin as [<- | Hin']; [exfalso; apply Hpred; reflexivity |].
      assert (IH' := IH Hin'). lia.
    + (* a = v: skip a *)
      apply Bool.negb_false_iff in Hpred. apply Nat.eqb_eq in Hpred. subst a.
      enough (length (filter (fun x => negb (Nat.eqb x v)) l') <= length l') by lia.
      apply filter_length_le.
Qed.

(* Exact length after removing one element from a NoDup list *)
Lemma remove_node_length_pred : forall v l,
  NoDup l -> In v l -> length (remove_node v l) = pred (length l).
Proof.
  intros v l Hnd Hin. unfold remove_node.
  induction l as [|a l' IH].
  - destruct Hin.
  - inversion Hnd as [| ? ? Hnotin Hnd']. subst.
    simpl. destruct (Nat.eqb a v) eqn:Heqb.
    + (* a = v *)
      apply Nat.eqb_eq in Heqb. subst a. simpl.
      (* v not in l', so filter doesn't remove anything *)
      apply filter_id. intros x Hx. simpl.
      apply Bool.negb_true_iff, Nat.eqb_neq.
      intro Heq. subst x. contradiction.
    + (* a <> v *)
      apply Nat.eqb_neq in Heqb. simpl.
      destruct Hin as [Heq | Hin']; [subst a; exfalso; apply Heqb; reflexivity |].
      rewrite (IH Hnd' Hin').
      (* length l' > 0 since In v l' *)
      destruct l' as [| b l'']; [destruct Hin' |]. simpl. lia.
Qed.

Lemma restrict_edges_In_iff : forall nodes edges e,
  In e (restrict_edges_to nodes edges) <->
    In e edges /\ In (fst e) nodes /\ In (snd e) nodes.
Proof.
  intros nodes edges e. unfold restrict_edges_to. rewrite filter_In.
  rewrite Bool.andb_true_iff, mem_nat_In, mem_nat_In. tauto.
Qed.

Lemma restrict_edges_acyclic : forall nodes edges,
  acyclic edges -> acyclic (restrict_edges_to nodes edges).
Proof.
  intros nodes edges Hac v Hreach. apply (Hac v).
  apply reachable_subset with (edges' := restrict_edges_to nodes edges).
  - intros e He. apply restrict_edges_In_iff in He. tauto.
  - exact Hreach.
Qed.

(* ---- Main construction: topological order from acyclicity ---- *)

(* Generalized topological sort for an arbitrary finite node set.
   By strong induction on the number of nodes: find a source, place it first,
   recurse on the remaining nodes with restricted edges. *)
Lemma topo_sort_of_nodes :
  forall (k : nat) (nodes : list nat) (edges : list dep_edge),
    length nodes = k ->
    NoDup nodes ->
    (forall e, In e edges -> In (fst e) nodes /\ In (snd e) nodes) ->
    acyclic edges ->
    exists order,
      length order = k /\
      NoDup order /\
      (forall x, In x nodes <-> In x order) /\
      order_respects_deps order edges.
Proof.
  induction k as [k IH] using lt_wf_ind.
  intros nodes edges Hlen Hnodup Hvalid Hacyclic.
  destruct nodes as [| v0 rest] eqn:Hnodes_eq.
  - (* Base case: no nodes, empty order *)
    exists []. simpl in Hlen. subst k. repeat split.
    + constructor.
    + intro x. simpl. tauto.
    + intros i j Hedge. destruct (Hvalid _ Hedge) as [H _]. destruct H.
  - (* Inductive case: find a source node *)
    simpl in Hlen.
    (* Every node has an outgoing edge, or some node is a source *)
    assert (Hsource : exists v, In v (v0 :: rest) /\ forall j, ~ In (v, j) edges).
    { (* Check each node for outgoing edges *)
      destruct (existsb
        (fun v => match find_dep v edges with None => true | Some _ => false end)
        (v0 :: rest)) eqn:Hcheck.
      - (* Found a source *)
        apply existsb_exists in Hcheck.
        destruct Hcheck as [v [Hv_in Hv_src]].
        exists v. split; [exact Hv_in |].
        destruct (find_dep v edges) as [j|] eqn:Hfd; [discriminate |].
        exact (find_dep_None_no_edge v edges Hfd).
      - (* No source: derive contradiction via walk + pigeonhole *)
        exfalso.
        (* Every node in our list has a successor *)
        assert (Hall : forall v, In v (v0 :: rest) ->
                        exists j, find_dep v edges = Some j /\ In j (v0 :: rest)).
        { intros v Hv.
          destruct (find_dep v edges) as [j|] eqn:Hfd.
          - exists j. split; [reflexivity |].
            apply find_dep_Some_In in Hfd.
            specialize (Hvalid _ Hfd). simpl in Hvalid. tauto.
          - exfalso.
            assert (Htrue : existsb
              (fun v1 => match find_dep v1 edges with
                         None => true | Some _ => false end)
              (v0 :: rest) = true).
            { apply existsb_exists. exists v.
              split; [exact Hv | rewrite Hfd; reflexivity]. }
            rewrite Htrue in Hcheck. discriminate. }
        (* Define total successor function *)
        set (next := fun v =>
          match find_dep v edges with Some j => j | None => v end).
        assert (Hnext_in : forall v, In v (v0 :: rest) -> In (next v) (v0 :: rest)).
        { intros v Hv. unfold next.
          destruct (Hall v Hv) as [j [Hj Hj_in]]. rewrite Hj. exact Hj_in. }
        assert (Hnext_edge : forall v, In v (v0 :: rest) -> In (v, next v) edges).
        { intros v Hv. unfold next.
          destruct (Hall v Hv) as [j [Hj _]]. rewrite Hj.
          exact (find_dep_Some_In v edges j Hj). }
        (* Build walk of length k+1 starting from v0 *)
        set (w := dep_walk next v0 k).
        assert (Hw_len : length w = S k) by apply dep_walk_length.
        assert (Hw_in : forall x, In x w -> In x (v0 :: rest)).
        { apply dep_walk_all with (P := fun x => In x (v0 :: rest)).
          - left. reflexivity.
          - exact Hnext_in. }
        (* Pigeonhole: k+1 values in a set of k distinct elements *)
        assert (Hw_not_nodup : ~ NoDup w).
        { intro Hnd.
          assert (Hle : length w <= length (v0 :: rest)).
          { apply NoDup_incl_NoDup_length; assumption. }
          simpl in Hle. lia. }
        (* Extract repeated element *)
        destruct (not_NoDup_has_repeat w Hw_not_nodup)
          as [x [i [j [Hij [Hj_len [Hi_eq Hj_eq]]]]]].
        (* Build cycle from the repeat *)
        assert (Hi_le : i <= k) by lia.
        assert (Hj_le : j <= k) by lia.
        pose proof (dep_walk_nth next v0 k i Hi_le) as Hi_nth.
        pose proof (dep_walk_nth next v0 k j Hj_le) as Hj_nth.
        assert (Hi_val : nat_iter i next v0 = x).
        { rewrite Hi_nth in Hi_eq. congruence. }
        assert (Hj_val : nat_iter j next v0 = x).
        { rewrite Hj_nth in Hj_eq. congruence. }
        assert (Hreach : reachable edges x x).
        { rewrite <- Hi_val, <- Hj_val.
          replace j with (i + (j - i)) by lia.
          rewrite <- nat_iter_add.
          apply reachable_chain with (P := fun v => In v (v0 :: rest)).
          - lia.
          - exact Hnext_edge.
          - exact Hnext_in.
          - apply Hw_in. eapply nth_error_In. exact Hi_eq. }
        exact (Hacyclic x Hreach). }
    (* We have a source node v *)
    destruct Hsource as [v [Hv_in Hv_no_out]].
    set (nodes' := remove_node v (v0 :: rest)).
    set (edges' := restrict_edges_to nodes' edges).
    (* Properties of the smaller problem *)
    assert (Hlen' : length nodes' < k).
    { unfold nodes'. rewrite <- Hlen.
      apply remove_node_length_lt. exact Hv_in. }
    assert (Hnodup' : NoDup nodes').
    { apply remove_node_NoDup. exact Hnodup. }
    assert (Hvalid' : forall e, In e edges' -> In (fst e) nodes' /\ In (snd e) nodes').
    { intros e He. apply restrict_edges_In_iff in He. tauto. }
    assert (Hacyclic' : acyclic edges').
    { apply restrict_edges_acyclic. exact Hacyclic. }
    (* Apply IH to the smaller problem *)
    destruct (IH (length nodes') Hlen' nodes' edges'
                 eq_refl Hnodup' Hvalid' Hacyclic')
      as [order' [Hlen_o' [Hnodup_o' [Hiff_o' Hresp_o']]]].
    (* Construct final order: source v first, then order' *)
    exists (v :: order').
    split; [| split; [| split]].
    + (* Length *)
      simpl. rewrite Hlen_o'.
      unfold nodes'.
      rewrite (remove_node_length_pred v (v0 :: rest) Hnodup Hv_in).
      simpl. lia.
    + (* NoDup *)
      constructor.
      * (* v not in order' *)
        intro Habs. apply Hiff_o' in Habs.
        exact (remove_node_not_In v (v0 :: rest) Habs).
      * exact Hnodup_o'.
    + (* Membership equivalence *)
      intro x. split.
      * (* In x (v0 :: rest) -> In x (v :: order') *)
        intro Hx. destruct (Nat.eq_dec x v) as [<- | Hneq].
        -- left. reflexivity.
        -- right. apply Hiff_o'. apply remove_node_In_iff. tauto.
      * (* In x (v :: order') -> In x (v0 :: rest) *)
        intro Hx. destruct Hx as [<- | Hx'].
        -- exact Hv_in.
        -- apply Hiff_o' in Hx'. apply remove_node_In_iff in Hx'. tauto.
    + (* order_respects_deps *)
      intros i j Hedge.
      destruct (Nat.eq_dec i v) as [Heq_i | Hneq_i].
      * (* i = v: impossible, v has no outgoing edges *)
        subst i. exfalso. exact (Hv_no_out j Hedge).
      * destruct (Nat.eq_dec j v) as [Heq_j | Hneq_j].
        -- (* j = v: v is at position 0, i is in order' *)
           subst j.
           assert (Hi_in_nodes : In i (v0 :: rest)).
           { specialize (Hvalid _ Hedge). simpl in Hvalid. tauto. }
           assert (Hi_in_order : In i order').
           { apply Hiff_o'. apply remove_node_In_iff. tauto. }
           apply In_nth_error_exists in Hi_in_order.
           destruct Hi_in_order as [pi Hi_nth].
           (* v = j at position 0, i at position S pi *)
           exists 0, (S pi). repeat split.
           ++ simpl. reflexivity.
           ++ simpl. exact Hi_nth.
           ++ lia.
        -- (* Neither i nor j is v: edge is in edges' *)
           assert (Hi_in : In i (v0 :: rest)).
           { specialize (Hvalid _ Hedge). simpl in Hvalid. tauto. }
           assert (Hj_in : In j (v0 :: rest)).
           { specialize (Hvalid _ Hedge). simpl in Hvalid. tauto. }
           assert (Hedge' : In (i, j) edges').
           { apply restrict_edges_In_iff. simpl. repeat split.
             - exact Hedge.
             - apply remove_node_In_iff. tauto.
             - apply remove_node_In_iff. tauto. }
           destruct (Hresp_o' i j Hedge') as [pi [pj [Hpi [Hpj Hlt]]]].
           (* Shift positions by 1 for the prepended v *)
           exists (S pi), (S pj). repeat split.
           ++ simpl. exact Hpi.
           ++ simpl. exact Hpj.
           ++ lia.
Qed.

(* ---- Instantiation for the main theorem ---- *)

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
  - (* Forward: acyclic -> valid order exists *)
    intros Hacyclic.
    (* Use topo_sort_of_nodes with nodes = seq 0 n *)
    assert (Hvalid_seq : forall e, In e edges ->
              In (fst e) (seq 0 n) /\ In (snd e) (seq 0 n)).
    { intros e He. specialize (Hvalid e He).
      split; apply in_seq; lia. }
    assert (Hseq_len : length (seq 0 n) = n) by apply seq_length.
    assert (Hseq_nodup : NoDup (seq 0 n)) by apply seq_NoDup.
    destruct (topo_sort_of_nodes n (seq 0 n) edges
                Hseq_len Hseq_nodup Hvalid_seq Hacyclic)
      as [order [Hlen [Hnodup [Hiff Hresp]]]].
    exists order. split.
    + (* order_complete n order *)
      unfold order_complete. repeat split.
      * exact Hlen.
      * exact Hnodup.
      * intros i Hi. apply Hiff. apply in_seq. lia.
    + (* order_respects_deps *)
      exact Hresp.
Qed.

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
  (* Dependency graph is acyclic *)
  acyclic (dg_edges graph) /\
  (* Adapter sites match resolutions *)
  (forall site, In site (rr_adapter_sites result) ->
                exists r, In r (dg_resolved_imports graph) /\
                          as_from_component site = fst (fst r) /\
                          as_to_component site = fst (snd r)).

(* Resolution correctness: the resolution algorithm produces a correct result.

   The non-trivial content is deriving acyclicity from the ordering properties
   via valid_order_implies_acyclic. The ordering and structural invariants are
   taken as preconditions about the algorithm output.

   NOTE: Once Kahn's algorithm is formalized in Rocq, the ordering preconditions
   (order_complete, order_respects_deps) can be replaced by:
     acyclic edges ->
     dg_instantiation_order graph = kahn_sort n edges ->
   and the ordering properties derived. For now, ordering is a precondition
   and acyclicity is derived from it. *)
Theorem resolve_correctness :
  forall (components : list component) (result : resolution_result),
    let graph := rr_graph result in
    (* Structural: component count matches *)
    dg_num_components graph = length components ->
    (* Structural: edges derived from resolutions *)
    (forall e, In e (dg_edges graph) <->
               In e (edges_from_resolutions (dg_resolved_imports graph))) ->
    (* All edges are within bounds *)
    (forall e, In e (dg_edges graph) ->
               fst e < length components /\ snd e < length components) ->
    (* Topological ordering is valid (from Kahn's algorithm) *)
    order_complete (length components) (dg_instantiation_order graph) ->
    order_respects_deps (dg_instantiation_order graph) (dg_edges graph) ->
    (* Adapter sites match resolutions *)
    (forall site, In site (rr_adapter_sites result) ->
                  exists r, In r (dg_resolved_imports graph) /\
                            as_from_component site = fst (fst r) /\
                            as_to_component site = fst (snd r)) ->
    resolution_correct components result.
Proof.
  intros components result graph
    Hcount Hedges_iff Hbounds Hcomplete Hrespects Hadapters.
  unfold resolution_correct.
  repeat split; try assumption.
  (* Derive acyclicity from edge bounds + valid topological ordering *)
  eapply valid_order_implies_acyclic; eauto.
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
