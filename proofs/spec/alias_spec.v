(* =========================================================================
   Component Model Alias Handling Specification

   Baseline: WebAssembly Component Model Specification (commit deb0b0a)

   The Component Model allows components to define aliases that reference
   items from outer components (outer aliases) or from instance exports
   (inner/export aliases). Additionally, core type aliases allow
   referencing types defined in other scopes.

   During fusion, alias chains must be fully resolved before index
   remapping can proceed. This file defines:
   1. The ComponentAlias type representing all alias forms
   2. An alias resolution function that follows alias chains
   3. Well-formedness properties: alias targets must exist and
      resolution must terminate (no alias cycles)
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith PeanoNat.
From MeldSpec Require Import wasm_core component_model.
Import ListNotations.

(* -------------------------------------------------------------------------
   Alias Kinds

   The Component Model defines three kinds of aliases:
   - Outer aliases: reference items from an enclosing component scope
   - Export aliases: reference items from an instance's exports
   - Core type aliases: reference core WASM types from another scope

   Each alias kind has a sort (function, value, type, etc.) that
   determines what kind of item it references.
   ------------------------------------------------------------------------- *)

Inductive alias_sort : Type :=
  | AliasFunc
  | AliasValue
  | AliasType
  | AliasTable
  | AliasMemory
  | AliasGlobal
  | AliasComponent
  | AliasInstance.

(* An outer alias references an item from an enclosing component.
   outer_count indicates how many scopes outward to look (1 = immediate parent).
   outer_index is the item's index within that outer scope. *)
Record outer_alias : Type := mkOuterAlias {
  oa_sort : alias_sort;
  oa_outer_count : nat;   (* Number of enclosing scopes to traverse *)
  oa_outer_index : idx;   (* Index within the outer scope *)
}.

(* An export alias references an item exported by a component instance.
   The instance_idx identifies which instance, and the export_name
   identifies which export within that instance. *)
Record export_alias : Type := mkExportAlias {
  ea_sort : alias_sort;
  ea_instance_idx : idx;    (* Instance providing the export *)
  ea_export_name : wasm_string;  (* Name of the export *)
}.

(* A core type alias references a core WASM type from the core type
   index space. This is used when a component needs to reference a
   functype defined in its core modules. *)
Record core_type_alias : Type := mkCoreTypeAlias {
  cta_outer_count : nat;   (* Scopes outward, or 0 for current scope *)
  cta_type_index : idx;    (* Core type index in the target scope *)
}.

(* The top-level alias type, combining all alias forms *)
Inductive component_alias : Type :=
  | CAOuter (alias : outer_alias)
  | CAExport (alias : export_alias)
  | CACoreType (alias : core_type_alias).

(* -------------------------------------------------------------------------
   Alias Resolution Target

   The result of resolving an alias: a concrete item identified by
   its component index and local index within that component.
   ------------------------------------------------------------------------- *)

(* A resolved alias points to a concrete item in a specific component *)
Record alias_target : Type := mkAliasTarget {
  at_component_idx : nat;  (* Which component contains the item *)
  at_sort : alias_sort;    (* What kind of item *)
  at_local_idx : idx;      (* Index within the component *)
}.

(* -------------------------------------------------------------------------
   Component Nesting Context

   Alias resolution requires knowing the component nesting structure.
   An alias_context represents the stack of enclosing component scopes
   and available instances for export alias resolution.
   ------------------------------------------------------------------------- *)

(* A single scope in the component nesting stack *)
Record component_scope : Type := mkComponentScope {
  cs_component_idx : nat;
  (* Items directly defined in this scope, indexed by sort.
     The nat represents how many items of each sort are available. *)
  cs_func_count : nat;
  cs_type_count : nat;
  cs_table_count : nat;
  cs_memory_count : nat;
  cs_global_count : nat;
  cs_component_count : nat;
  cs_instance_count : nat;
}.

(* An instance export entry: (instance_idx, export_name, sort, local_idx) *)
Definition instance_export_entry :=
  (idx * wasm_string * alias_sort * idx)%type.

(* The alias resolution context *)
Record alias_context : Type := mkAliasContext {
  (* Stack of enclosing scopes, innermost first *)
  ac_scopes : list component_scope;
  (* Export entries available for export alias resolution *)
  ac_instance_exports : list instance_export_entry;
  (* Previously defined aliases in the current scope, which may
     themselves need resolution (forming chains) *)
  ac_prior_aliases : list (component_alias * option alias_target);
}.

(* -------------------------------------------------------------------------
   Alias Resolution

   resolve_alias follows an alias to its target. For outer aliases,
   it looks up the item in the appropriate enclosing scope. For export
   aliases, it looks up the instance's export. For core type aliases,
   it resolves to the type in the target scope.

   Alias chains arise when an alias's target is itself an alias.
   We use a fuel parameter to guarantee termination.
   ------------------------------------------------------------------------- *)

(* Count of items of a given sort in a scope *)
Definition scope_count_for_sort (scope : component_scope) (sort : alias_sort)
    : nat :=
  match sort with
  | AliasFunc => cs_func_count scope
  | AliasValue => 0  (* Values not tracked in scope counts *)
  | AliasType => cs_type_count scope
  | AliasTable => cs_table_count scope
  | AliasMemory => cs_memory_count scope
  | AliasGlobal => cs_global_count scope
  | AliasComponent => cs_component_count scope
  | AliasInstance => cs_instance_count scope
  end.

(* Resolve an outer alias by looking up the enclosing scope *)
Definition resolve_outer_alias (ctx : alias_context) (alias : outer_alias)
    : option alias_target :=
  let scopes := ac_scopes ctx in
  (* outer_count is 1-indexed: 1 means immediate parent *)
  match nth_error scopes (oa_outer_count alias) with
  | Some scope =>
      if Nat.ltb (oa_outer_index alias)
                  (scope_count_for_sort scope (oa_sort alias))
      then Some (mkAliasTarget (cs_component_idx scope)
                                (oa_sort alias)
                                (oa_outer_index alias))
      else None
  | None => None
  end.

(* Resolve an export alias by finding the named export in an instance *)
Definition resolve_export_alias (ctx : alias_context) (alias : export_alias)
    : option alias_target :=
  let entries := ac_instance_exports ctx in
  match List.find (fun entry =>
    let '(inst_idx, exp_name, sort, _) := entry in
    Nat.eqb inst_idx (ea_instance_idx alias) &&
    Nat.eqb exp_name (ea_export_name alias) &&
    match ea_sort alias, sort with
    | AliasFunc, AliasFunc => true
    | AliasType, AliasType => true
    | AliasTable, AliasTable => true
    | AliasMemory, AliasMemory => true
    | AliasGlobal, AliasGlobal => true
    | AliasComponent, AliasComponent => true
    | AliasInstance, AliasInstance => true
    | _, _ => false
    end
  ) entries with
  | Some (_, _, sort, local_idx) =>
      (* The component_idx for an instance export comes from the
         instance's origin, which we simplify to the instance index
         in the current scope. *)
      Some (mkAliasTarget (ea_instance_idx alias) sort local_idx)
  | None => None
  end.

(* Resolve a core type alias *)
Definition resolve_core_type_alias (ctx : alias_context) (alias : core_type_alias)
    : option alias_target :=
  let scopes := ac_scopes ctx in
  match nth_error scopes (cta_outer_count alias) with
  | Some scope =>
      if Nat.ltb (cta_type_index alias) (cs_type_count scope)
      then Some (mkAliasTarget (cs_component_idx scope)
                                AliasType
                                (cta_type_index alias))
      else None
  | None => None
  end.

(* Single-step alias resolution *)
Definition resolve_alias_step (ctx : alias_context) (alias : component_alias)
    : option alias_target :=
  match alias with
  | CAOuter oa => resolve_outer_alias ctx oa
  | CAExport ea => resolve_export_alias ctx ea
  | CACoreType cta => resolve_core_type_alias ctx cta
  end.

(* Multi-step alias resolution with fuel (for alias chains).
   At each step, if the resolved target is itself an alias in the prior
   alias list, we follow it. The fuel parameter bounds the chain length
   to ensure termination. *)
Fixpoint resolve_alias_chain (ctx : alias_context) (alias : component_alias)
    (fuel : nat) : option alias_target :=
  match fuel with
  | 0 => None  (* Exceeded chain length limit: likely a cycle *)
  | S fuel' =>
      match resolve_alias_step ctx alias with
      | None => None
      | Some target =>
          (* Check if this target is itself an alias that needs further resolution *)
          match nth_error (ac_prior_aliases ctx) (at_local_idx target) with
          | Some (next_alias, None) =>
              (* The target is an unresolved alias; follow the chain *)
              resolve_alias_chain ctx next_alias fuel'
          | Some (_, Some final_target) =>
              (* The target was already resolved; use its resolution *)
              Some final_target
          | None =>
              (* The target is a concrete item, not an alias *)
              Some target
          end
      end
  end.

(* Convenience: resolve with a default fuel equal to the number of
   prior aliases (sufficient for acyclic chains). *)
Definition resolve_alias (ctx : alias_context) (alias : component_alias)
    : option alias_target :=
  resolve_alias_chain ctx alias (length (ac_prior_aliases ctx) + 1).

(* -------------------------------------------------------------------------
   Well-formedness Properties

   An alias is well-formed if:
   1. Its target exists in the referenced scope
   2. The alias chain terminates (no cycles)
   3. The resolved sort matches the alias's declared sort
   ------------------------------------------------------------------------- *)

(* An alias target exists: the index is within bounds for the sort *)
Definition alias_target_exists (ctx : alias_context) (target : alias_target)
    : Prop :=
  exists scope,
    In scope (ac_scopes ctx) /\
    cs_component_idx scope = at_component_idx target /\
    at_local_idx target < scope_count_for_sort scope (at_sort target).

(* A single alias is well-formed *)
Definition alias_wf (ctx : alias_context) (alias : component_alias) : Prop :=
  exists target,
    resolve_alias ctx alias = Some target /\
    alias_target_exists ctx target.

(* All aliases in a context are well-formed *)
Definition all_aliases_wf (ctx : alias_context) : Prop :=
  Forall (fun pair =>
    let '(alias, _) := pair in
    alias_wf ctx alias
  ) (ac_prior_aliases ctx).

(* -------------------------------------------------------------------------
   Alias Acyclicity

   Alias chains must be acyclic: following an alias chain must
   eventually reach a concrete (non-alias) item. We express this
   as: for any alias, resolution with sufficient fuel succeeds.
   ------------------------------------------------------------------------- *)

(* An alias chain is acyclic if resolution succeeds with the
   standard fuel budget *)
Definition alias_chain_acyclic (ctx : alias_context)
    (alias : component_alias) : Prop :=
  exists target,
    resolve_alias ctx alias = Some target.

(* If all aliases are well-formed, every alias chain is acyclic.
   This follows from well-formedness requiring successful resolution. *)
Theorem wf_implies_acyclic :
  forall ctx alias,
    alias_wf ctx alias ->
    alias_chain_acyclic ctx alias.
Proof.
  intros ctx alias [target [Hresolve _]].
  unfold alias_chain_acyclic.
  exists target. exact Hresolve.
Qed.

(* -------------------------------------------------------------------------
   Sort Preservation

   Resolution preserves the alias sort: the resolved target's sort
   matches the original alias's declared sort.
   ------------------------------------------------------------------------- *)

(* Extract the sort from an alias *)
Definition alias_sort_of (alias : component_alias) : alias_sort :=
  match alias with
  | CAOuter oa => oa_sort oa
  | CAExport ea => ea_sort ea
  | CACoreType _ => AliasType
  end.

(* Single-step resolution preserves sort for outer aliases *)
Lemma resolve_outer_preserves_sort :
  forall ctx oa target,
    resolve_outer_alias ctx oa = Some target ->
    at_sort target = oa_sort oa.
Proof.
  intros ctx oa target Hresolve.
  unfold resolve_outer_alias in Hresolve.
  destruct (nth_error (ac_scopes ctx) (oa_outer_count oa)) as [scope |] eqn:Hscope;
    [| discriminate].
  destruct (Nat.ltb (oa_outer_index oa) (scope_count_for_sort scope (oa_sort oa)))
    eqn:Hbound; [| discriminate].
  injection Hresolve as Htarget. subst target.
  simpl. reflexivity.
Qed.

(* Single-step resolution preserves sort for core type aliases *)
Lemma resolve_core_type_preserves_sort :
  forall ctx cta target,
    resolve_core_type_alias ctx cta = Some target ->
    at_sort target = AliasType.
Proof.
  intros ctx cta target Hresolve.
  unfold resolve_core_type_alias in Hresolve.
  destruct (nth_error (ac_scopes ctx) (cta_outer_count cta)) as [scope |] eqn:Hscope;
    [| discriminate].
  destruct (Nat.ltb (cta_type_index cta) (cs_type_count scope))
    eqn:Hbound; [| discriminate].
  injection Hresolve as Htarget. subst target.
  simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Connection to Component Model

   Aliases appear during component parsing (meld-core/src/parser.rs).
   Before fusion proceeds, all aliases in the parsed component must
   be resolved to concrete indices. This lemma states that a
   well-formed component's aliases can all be resolved.
   ------------------------------------------------------------------------- *)

(* A component with well-formed aliases has all aliases resolvable *)
Definition component_aliases_resolvable (ctx : alias_context)
    (aliases : list component_alias) : Prop :=
  Forall (alias_wf ctx) aliases.

(* If aliases are resolvable, we can build a complete resolution map *)
Theorem aliases_produce_targets :
  forall ctx aliases,
    component_aliases_resolvable ctx aliases ->
    exists targets,
      length targets = length aliases /\
      Forall2 (fun alias target =>
        resolve_alias ctx alias = Some target
      ) aliases targets.
Proof.
  intros ctx aliases Hwf.
  induction aliases as [| a rest IH].
  - (* Base case: empty alias list *)
    exists []. split; [reflexivity | constructor].
  - (* Inductive case: resolve head, recurse on tail *)
    inversion Hwf as [| a' rest' Ha Hrest]. subst.
    destruct Ha as [target [Hresolve _]].
    destruct (IH Hrest) as [targets [Hlen Hforall2]].
    exists (target :: targets).
    split.
    + simpl. f_equal. exact Hlen.
    + constructor; [exact Hresolve | exact Hforall2].
Qed.

(* End of alias_spec *)
