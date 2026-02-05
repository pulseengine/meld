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

(* End of component_model specification *)
