(* =========================================================================
   P1 Intra-Component Adapter Specification

   Baseline: WebAssembly Component Model Specification (commit deb0b0a)

   Within a single component (P1 scope), multiple core modules may need
   to call each other. When two core modules within the same component
   have different canonical options (different string encodings, different
   linear memories, or different realloc functions), an intra-component
   adapter is needed to bridge the calling convention gap.

   This is distinct from the cross-component (P2/P3) adapters defined in
   adapter_spec.v: intra-component adapters operate within a single
   component's scope and handle module-to-module calls that go through
   the component's internal import/export wiring.

   This file defines:
   1. IntraComponentAdapterSite: identifies same-component cross-module calls
   2. When an intra-component call needs an adapter
   3. Correctness: adapted calls preserve value semantics
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith PeanoNat.
From MeldSpec Require Import wasm_core component_model fusion_types.
Import ListNotations.

(* -------------------------------------------------------------------------
   Canonical Options per Module

   Each core module within a component may have its own canonical options
   (specified via canon lift/lower). These options determine the string
   encoding, linear memory, and realloc function used for Canonical ABI
   operations.
   ------------------------------------------------------------------------- *)

(* Canonical options relevant to adapter generation *)
Record module_canonical_options : Type := mkModuleCanonicalOptions {
  mco_string_encoding : nat;  (* 0=utf8, 1=utf16, 2=latin1+utf16 *)
  mco_memory_idx : option idx;  (* Linear memory for Canonical ABI ops *)
  mco_realloc_idx : option idx; (* cabi_realloc function *)
}.

(* Default options when none are specified *)
Definition default_module_options : module_canonical_options :=
  mkModuleCanonicalOptions 0 None None.

(* -------------------------------------------------------------------------
   Intra-Component Adapter Site

   An intra-component adapter site represents a call between two core
   modules within the same component that requires adaptation due to
   differing canonical options.
   ------------------------------------------------------------------------- *)

Record intra_component_adapter_site : Type := mkIntraAdapterSite {
  (* The component containing both modules *)
  icas_component_idx : nat;
  (* The calling module (importer) *)
  icas_caller_module : nat;
  icas_caller_import_name : wasm_string;
  (* The target module (exporter) *)
  icas_callee_module : nat;
  icas_callee_export_name : wasm_string;
  (* Canonical options for each side *)
  icas_caller_options : module_canonical_options;
  icas_callee_options : module_canonical_options;
}.

(* -------------------------------------------------------------------------
   Adapter Necessity

   An intra-component call needs an adapter when the caller and callee
   have different canonical options. If all options match, the call can
   be wired directly without an adapter trampoline.
   ------------------------------------------------------------------------- *)

(* Two option sets match: no adapter needed *)
Definition canonical_options_match (caller callee : module_canonical_options)
    : bool :=
  Nat.eqb (mco_string_encoding caller) (mco_string_encoding callee) &&
  match mco_memory_idx caller, mco_memory_idx callee with
  | Some m1, Some m2 => Nat.eqb m1 m2
  | None, None => true
  | _, _ => false
  end &&
  match mco_realloc_idx caller, mco_realloc_idx callee with
  | Some r1, Some r2 => Nat.eqb r1 r2
  | None, None => true
  | _, _ => false
  end.

(* An intra-component call needs an adapter when options differ *)
Definition intra_call_needs_adapter (site : intra_component_adapter_site)
    : bool :=
  negb (canonical_options_match (icas_caller_options site)
                                 (icas_callee_options site)).

(* A call with matching options does not need an adapter *)
Theorem matching_options_no_adapter :
  forall site,
    canonical_options_match (icas_caller_options site)
                            (icas_callee_options site) = true ->
    intra_call_needs_adapter site = false.
Proof.
  intros site Hmatch.
  unfold intra_call_needs_adapter.
  rewrite Hmatch. reflexivity.
Qed.

(* A call with identical options on both sides needs no adapter *)
Theorem same_options_no_adapter :
  forall site,
    icas_caller_options site = icas_callee_options site ->
    intra_call_needs_adapter site = false.
Proof.
  intros site Heq.
  apply matching_options_no_adapter.
  unfold canonical_options_match.
  rewrite Heq.
  destruct (icas_callee_options site) as [enc mem realloc].
  simpl.
  rewrite Nat.eqb_refl.
  destruct mem; [rewrite Nat.eqb_refl |]; simpl;
  destruct realloc; [rewrite Nat.eqb_refl |]; simpl; reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Identifying Intra-Component Adapter Sites

   Given a component and its core modules' canonical options, identify
   all module-to-module calls that need adaptation.
   ------------------------------------------------------------------------- *)

(* A module-level import/export pair within a component *)
Record intra_component_link : Type := mkIntraComponentLink {
  icl_caller_module : nat;
  icl_caller_import : import;
  icl_callee_module : nat;
  icl_callee_export : export;
}.

(* Identify which intra-component links need adapters *)
Definition identify_intra_adapter_sites
    (comp_idx : nat)
    (links : list intra_component_link)
    (options : nat -> module_canonical_options)
    : list intra_component_adapter_site :=
  List.filter (fun site => intra_call_needs_adapter site)
    (map (fun link =>
      mkIntraAdapterSite
        comp_idx
        (icl_caller_module link)
        (imp_name (icl_caller_import link))
        (icl_callee_module link)
        (exp_name (icl_callee_export link))
        (options (icl_caller_module link))
        (options (icl_callee_module link))
    ) links).

(* Every identified site actually needs an adapter *)
Theorem identified_sites_need_adapters :
  forall comp_idx links options site,
    In site (identify_intra_adapter_sites comp_idx links options) ->
    intra_call_needs_adapter site = true.
Proof.
  intros comp_idx links options site Hin.
  unfold identify_intra_adapter_sites in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hfilter].
  exact Hfilter.
Qed.

(* -------------------------------------------------------------------------
   Intra-Component Adapter Correctness

   An intra-component adapter preserves value semantics: the values
   received by the callee are equivalent to the values sent by the caller,
   modulo encoding/memory differences handled by the adapter.

   The key difference from cross-component adapters: intra-component
   adapters operate within a single component's type system. The caller
   and callee agree on the component-level types; only the core-level
   representation may differ due to different canonical options.
   ------------------------------------------------------------------------- *)

(* The result of an adapted intra-component call.
   For calls that don't need adaptation, the values pass through unchanged.
   For calls that need adaptation, the adapter performs lowering in the
   caller's context and lifting in the callee's context (or vice versa
   for return values). *)
Definition intra_adapter_preserves_values
    (site : intra_component_adapter_site)
    (caller_vals : list Z)
    (callee_received_vals : list Z)
    : Prop :=
  if negb (intra_call_needs_adapter site)
  then
    (* No adapter needed: values pass through unchanged *)
    callee_received_vals = caller_vals
  else
    (* Adapter present: values may be transcoded/copied but the
       count is preserved. Individual value correctness depends on
       the Canonical ABI roundtrip property (see adapter_spec.v). *)
    length callee_received_vals = length caller_vals.

(* Direct (non-adapted) calls preserve values exactly *)
Theorem direct_intra_call_preserves_values :
  forall site caller_vals,
    intra_call_needs_adapter site = false ->
    intra_adapter_preserves_values site caller_vals caller_vals.
Proof.
  intros site caller_vals Hno_adapter.
  unfold intra_adapter_preserves_values.
  rewrite Hno_adapter. simpl.
  reflexivity.
Qed.

(* Adapted calls preserve value count *)
Theorem adapted_intra_call_preserves_count :
  forall site caller_vals callee_vals,
    intra_adapter_preserves_values site caller_vals callee_vals ->
    length callee_vals = length caller_vals.
Proof.
  intros site caller_vals callee_vals Hpreserves.
  unfold intra_adapter_preserves_values in Hpreserves.
  destruct (negb (intra_call_needs_adapter site)) eqn:Hneed.
  - (* No adapter: values are equal, so lengths are equal *)
    subst callee_vals. reflexivity.
  - (* Adapter present: length preservation is the specification *)
    exact Hpreserves.
Qed.

(* -------------------------------------------------------------------------
   Connection to Fusion Pipeline

   During fusion, intra-component adapter sites are identified after
   parsing (when canonical options are known) but before merging
   (when the fused module is constructed). The adapters are generated
   alongside the cross-component adapters from adapter_spec.v.

   The key distinction:
   - Cross-component adapters (adapter_spec.v): always needed for
     cross-component calls, handle full lift/lower cycle
   - Intra-component adapters (this file): only needed when canonical
     options differ within a component, handle encoding/memory translation
   ------------------------------------------------------------------------- *)

(* An intra-component adapter site is valid within a component *)
Definition intra_site_valid (c : component) (site : intra_component_adapter_site)
    : Prop :=
  (* Both modules exist within the component *)
  icas_caller_module site < length (comp_core_modules c) /\
  icas_callee_module site < length (comp_core_modules c) /\
  (* The modules are different (same-module calls never need adapters) *)
  icas_caller_module site <> icas_callee_module site.

(* If modules are the same, the site is not valid (self-calls don't
   go through the component model's import/export mechanism) *)
Theorem same_module_not_valid_site :
  forall c site,
    icas_caller_module site = icas_callee_module site ->
    ~ intra_site_valid c site.
Proof.
  intros c site Heq [_ [_ Hneq]].
  contradiction.
Qed.

(* End of p1_adapter_spec *)
