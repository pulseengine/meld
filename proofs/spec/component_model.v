(* =========================================================================
   WebAssembly Component Model Semantics

   Baseline: Component Model Specification
   See: https://github.com/WebAssembly/component-model

   This module defines the component model abstractions that meld operates on.
   Components contain core modules plus type information and linking metadata.
   ========================================================================= *)

From Stdlib Require Import List ZArith.
From MeldSpec Require Import wasm_core.
Import ListNotations.

(* -------------------------------------------------------------------------
   Component Value Types

   Component Model has a richer type system than core WASM.
   For fusion, we primarily care about the core module embedding.
   ------------------------------------------------------------------------- *)

Inductive component_valtype : Type :=
  | CVBool
  | CVS8 | CVU8
  | CVS16 | CVU16
  | CVS32 | CVU32
  | CVS64 | CVU64
  | CVF32 | CVF64
  | CVChar
  | CVString
  | CVList (elem : component_valtype)
  | CVRecord (fields : list (wasm_string * component_valtype))
  | CVVariant (cases : list (wasm_string * option component_valtype))
  | CVTuple (elems : list component_valtype)
  | CVFlags (labels : list wasm_string)
  | CVOption (inner : component_valtype)
  | CVResult (ok : option component_valtype) (err : option component_valtype)
  | CVOwn (resource : nat)
  | CVBorrow (resource : nat).

(* -------------------------------------------------------------------------
   Component Function Types
   ------------------------------------------------------------------------- *)

Record component_functype : Type := mkComponentFunctype {
  cft_params : list (wasm_string * component_valtype);
  cft_results : list (wasm_string * component_valtype);
}.

(* -------------------------------------------------------------------------
   Core Module Instance within a Component

   A component embeds one or more core modules. Each module instance
   has its own index spaces.
   ------------------------------------------------------------------------- *)

Record core_module_instance : Type := mkCoreModuleInstance {
  cmi_module : module;
  cmi_instance_id : nat;
}.

(* -------------------------------------------------------------------------
   Component Imports and Exports

   Components can import/export at the component level (with rich types)
   or at the core level (direct module access).
   ------------------------------------------------------------------------- *)

Inductive component_import_kind : Type :=
  | CIFunc (ft : component_functype)
  | CIValue (vt : component_valtype)
  | CIType
  | CIInstance
  | CIComponent.

Record component_import : Type := mkComponentImport {
  cimp_name : wasm_string;
  cimp_kind : component_import_kind;
}.

Inductive component_export_kind : Type :=
  | CEFunc (ft : component_functype)
  | CEValue (vt : component_valtype)
  | CEType
  | CEInstance
  | CEComponent.

Record component_export : Type := mkComponentExport {
  cexp_name : wasm_string;
  cexp_kind : component_export_kind;
}.

(* -------------------------------------------------------------------------
   Canonical ABI Lifting/Lowering

   The Canonical ABI defines how component-level values map to core WASM.
   This is relevant for adapter generation during fusion.
   ------------------------------------------------------------------------- *)

(* Represents a canonical option for function adaptation *)
Inductive canonical_option : Type :=
  | CanonStringEncoding (enc : nat) (* 0=utf8, 1=utf16, 2=latin1+utf16 *)
  | CanonMemory (memidx : idx)
  | CanonRealloc (funcidx : idx)
  | CanonPostReturn (funcidx : idx).

(* A lifted function maps core WASM calling convention to component types *)
Record canon_lift : Type := mkCanonLift {
  cl_core_func : idx;
  cl_component_type : component_functype;
  cl_options : list canonical_option;
}.

(* A lowered function maps component calling convention to core WASM *)
Record canon_lower : Type := mkCanonLower {
  clw_component_func : idx;
  clw_core_type : functype;
  clw_options : list canonical_option;
}.

(* -------------------------------------------------------------------------
   Component Structure
   ------------------------------------------------------------------------- *)

Record component : Type := mkComponent {
  comp_core_modules : list core_module_instance;
  comp_imports : list component_import;
  comp_exports : list component_export;
  comp_canon_lifts : list canon_lift;
  comp_canon_lowers : list canon_lower;
}.

(* -------------------------------------------------------------------------
   Component Composition

   When components are composed (via wac, wit-bindgen, etc.), their
   imports/exports are resolved. Meld fuses the result.
   ------------------------------------------------------------------------- *)

Record composition_link : Type := mkCompositionLink {
  link_exporter : nat;  (* component index that exports *)
  link_export_name : wasm_string;
  link_importer : nat;  (* component index that imports *)
  link_import_name : wasm_string;
}.

Record composed_component : Type := mkComposedComponent {
  cc_components : list component;
  cc_links : list composition_link;
  (* Remaining unresolved imports after composition *)
  cc_unresolved_imports : list component_import;
  (* Exposed exports after composition *)
  cc_exposed_exports : list component_export;
}.

(* -------------------------------------------------------------------------
   Well-formedness for Components
   ------------------------------------------------------------------------- *)

Definition component_has_module (c : component) : Prop :=
  length (comp_core_modules c) > 0.

Definition valid_composition_link (cc : composed_component) (l : composition_link) : Prop :=
  l.(link_exporter) < length (cc_components cc) /\
  l.(link_importer) < length (cc_components cc) /\
  l.(link_exporter) <> l.(link_importer).

Definition well_formed_composition (cc : composed_component) : Prop :=
  Forall (valid_composition_link cc) (cc_links cc).

(* -------------------------------------------------------------------------
   Extracting Core Modules from Composed Components

   This is what meld's parser does - extracts all core modules from
   a composed component for fusion.
   ------------------------------------------------------------------------- *)

Definition extract_core_modules (cc : composed_component) : list module :=
  flat_map (fun c => map cmi_module (comp_core_modules c)) (cc_components cc).

(* The source of a core module: (component_idx, module_idx_within_component) *)
Definition module_source := (nat * nat)%type.

Definition enumerate_module_sources (cc : composed_component) : list module_source :=
  let components := cc_components cc in
  flat_map (fun ci =>
    let c := fst ci in
    let comp_idx := snd ci in
    map (fun mi => (comp_idx, mi)) (seq 0 (length (comp_core_modules c)))
  ) (combine components (seq 0 (length components))).

(* =========================================================================
   Instance Scoping

   The Component Model organizes items into instance scopes. Each component
   instance has a set of exports derived from the instantiated component's
   exports. When one component imports from another, the import resolves
   through instance indirection: the importing component sees an instance
   index, and the actual item is looked up in that instance's export map.

   This is important for fusion because:
   1. Import resolution must follow instance indirection
   2. The fused module needs to correctly map instance-scoped indices
      to the flat index space of the merged module
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Instance Scope

   Maps instance indices to their source module origins and the
   exports they provide.
   ------------------------------------------------------------------------- *)

(* An instance scope entry tracks which component and module an
   instance was created from, along with the exports it provides. *)
Record instance_scope_entry : Type := mkInstanceScopeEntry {
  ise_instance_idx : nat;
  ise_source_component : nat;
  ise_source_module : nat;
  (* The exports this instance provides, as (name, kind) pairs.
     These are a subset of the source module's exports. *)
  ise_exports : list (wasm_string * component_export_kind);
}.

(* The instance scope for a composed component *)
Definition instance_scope := list instance_scope_entry.

(* -------------------------------------------------------------------------
   Instance Export Resolution

   Given an instance index and an export name, find the corresponding
   export kind. This models the indirection step in import resolution:
   the resolver first identifies the target instance, then looks up
   the named export within that instance.
   ------------------------------------------------------------------------- *)

Definition resolve_instance_export (scope : instance_scope)
    (inst_idx : nat) (export_name : wasm_string)
    : option component_export_kind :=
  (* Find the instance entry *)
  match List.find (fun entry => Nat.eqb (ise_instance_idx entry) inst_idx) scope with
  | Some entry =>
      (* Find the named export within the instance *)
      match List.find (fun exp => Nat.eqb (fst exp) export_name)
                      (ise_exports entry) with
      | Some (_, kind) => Some kind
      | None => None
      end
  | None => None
  end.

(* -------------------------------------------------------------------------
   Instance Scope Well-formedness

   An instance scope is well-formed with respect to a composed component
   if:
   1. Every instance references a valid component and module
   2. Every instance's exports are a subset of its source module's exports
   3. Instance indices are unique
   ------------------------------------------------------------------------- *)

(* An instance entry's source is valid within a composed component *)
Definition instance_source_valid (cc : composed_component)
    (entry : instance_scope_entry) : Prop :=
  ise_source_component entry < length (cc_components cc) /\
  exists comp,
    nth_error (cc_components cc) (ise_source_component entry) = Some comp /\
    ise_source_module entry < length (comp_core_modules comp).

(* Helper: check if a component export has a given name and kind *)
Definition export_matches_name_kind (exp : component_export)
    (name : wasm_string) (kind : component_export_kind) : bool :=
  Nat.eqb (cexp_name exp) name &&
  match cexp_kind exp, kind with
  | CEFunc _, CEFunc _ => true
  | CEValue _, CEValue _ => true
  | CEType, CEType => true
  | CEInstance, CEInstance => true
  | CEComponent, CEComponent => true
  | _, _ => false
  end.

(* An instance's exports are a subset of its source component's exports.
   Every (name, kind) pair in the instance's export list must correspond
   to an export of the source component. *)
Definition instance_exports_subset (cc : composed_component)
    (entry : instance_scope_entry) : Prop :=
  forall name kind,
    In (name, kind) (ise_exports entry) ->
    exists comp,
      nth_error (cc_components cc) (ise_source_component entry) = Some comp /\
      exists exp,
        In exp (comp_exports comp) /\
        export_matches_name_kind exp name kind = true.

(* Instance indices are unique *)
Definition instance_indices_unique (scope : instance_scope) : Prop :=
  NoDup (map ise_instance_idx scope).

(* Full well-formedness of an instance scope *)
Definition instance_scope_wf (cc : composed_component)
    (scope : instance_scope) : Prop :=
  (* All sources are valid *)
  Forall (instance_source_valid cc) scope /\
  (* All exports are subsets of source exports *)
  Forall (instance_exports_subset cc) scope /\
  (* Instance indices are unique *)
  instance_indices_unique scope.

(* -------------------------------------------------------------------------
   Instance Scope Properties
   ------------------------------------------------------------------------- *)

(* Resolution is deterministic: same inputs produce same outputs *)
Theorem resolve_instance_export_deterministic :
  forall scope inst_idx name r1 r2,
    resolve_instance_export scope inst_idx name = Some r1 ->
    resolve_instance_export scope inst_idx name = Some r2 ->
    r1 = r2.
Proof.
  intros scope inst_idx name r1 r2 H1 H2.
  rewrite H1 in H2. injection H2. auto.
Qed.

(* If an instance export resolves, the instance exists in the scope *)
Theorem resolve_instance_export_implies_instance_exists :
  forall scope inst_idx name kind,
    resolve_instance_export scope inst_idx name = Some kind ->
    exists entry,
      In entry scope /\
      ise_instance_idx entry = inst_idx.
Proof.
  intros scope inst_idx name kind Hresolve.
  unfold resolve_instance_export in Hresolve.
  destruct (List.find (fun entry => Nat.eqb (ise_instance_idx entry) inst_idx)
                      scope) as [entry |] eqn:Hfind; [| discriminate].
  apply List.find_some in Hfind.
  destruct Hfind as [Hin Hpred].
  apply Nat.eqb_eq in Hpred.
  exists entry. split; [exact Hin | exact Hpred].
Qed.

(* In a well-formed instance scope, resolved exports come from the
   source component's exports *)
Theorem resolved_export_from_source :
  forall cc scope inst_idx name kind,
    instance_scope_wf cc scope ->
    resolve_instance_export scope inst_idx name = Some kind ->
    exists entry,
      In entry scope /\
      ise_instance_idx entry = inst_idx /\
      In (name, kind) (ise_exports entry) /\
      instance_exports_subset cc entry.
Proof.
  intros cc scope inst_idx name kind [Hvalid [Hsubset Huniq]] Hresolve.
  unfold resolve_instance_export in Hresolve.
  destruct (List.find (fun entry => Nat.eqb (ise_instance_idx entry) inst_idx)
                      scope) as [entry |] eqn:Hfind_entry; [| discriminate].
  destruct (List.find (fun exp => Nat.eqb (fst exp) name)
                      (ise_exports entry))
    as [[found_name found_kind] |] eqn:Hfind_exp; [| discriminate].
  injection Hresolve as Hkind_eq. subst kind.
  apply List.find_some in Hfind_entry.
  destruct Hfind_entry as [Hin_scope Hpred_inst].
  apply Nat.eqb_eq in Hpred_inst.
  apply List.find_some in Hfind_exp.
  destruct Hfind_exp as [Hin_exports Hpred_name].
  simpl in Hpred_name.
  apply Nat.eqb_eq in Hpred_name.
  subst found_name.
  exists entry. repeat split.
  - exact Hin_scope.
  - exact Hpred_inst.
  - exact Hin_exports.
  - (* instance_exports_subset: entry is in scope, so Forall gives us this *)
    rewrite Forall_forall in Hsubset. exact (Hsubset entry Hin_scope).
Qed.

(* End of component_model specification *)
