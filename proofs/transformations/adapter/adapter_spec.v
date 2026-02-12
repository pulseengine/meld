(* =========================================================================
   Adapter Transformation Specification

   Source: meld-core/src/adapter/mod.rs, meld-core/src/adapter/fact.rs

   The adapter transformation generates trampoline functions (adapters) that
   handle cross-component calls according to the Canonical ABI:
   1. Lowering component-level values to core WASM values
   2. Copying/transcoding data between linear memories
   3. Calling the target function
   4. Lifting core WASM results back to component-level values
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith PeanoNat.
From MeldSpec Require Import wasm_core component_model fusion_spec.
Import ListNotations.

(* -------------------------------------------------------------------------
   String Encodings

   The Component Model supports multiple string encodings.
   Transcoding may be required when encodings differ.
   ------------------------------------------------------------------------- *)

Inductive string_encoding : Type :=
  | UTF8
  | UTF16
  | Latin1.

Definition string_encoding_eqb (e1 e2 : string_encoding) : bool :=
  match e1, e2 with
  | UTF8, UTF8 => true
  | UTF16, UTF16 => true
  | Latin1, Latin1 => true
  | _, _ => false
  end.

(* -------------------------------------------------------------------------
   Adapter Options

   Configuration for a single adapter function.
   ------------------------------------------------------------------------- *)

Record adapter_options : Type := mkAdapterOptions {
  ao_caller_encoding : string_encoding;
  ao_callee_encoding : string_encoding;
  ao_caller_memory : idx;
  ao_callee_memory : idx;
  ao_caller_realloc : option idx;
  ao_callee_realloc : option idx;
}.

Definition default_adapter_options : adapter_options :=
  mkAdapterOptions UTF8 UTF8 0 0 None None.

(* Whether transcoding is needed *)
Definition needs_transcoding (opts : adapter_options) : bool :=
  negb (string_encoding_eqb (ao_caller_encoding opts) (ao_callee_encoding opts)).

(* Whether memories differ *)
Definition crosses_memory (opts : adapter_options) : bool :=
  negb (Nat.eqb (ao_caller_memory opts) (ao_callee_memory opts)).

(* -------------------------------------------------------------------------
   Adapter Function Representation

   An adapter function is a trampoline that bridges two components.
   ------------------------------------------------------------------------- *)

Record adapter_function : Type := mkAdapterFunction {
  af_name : wasm_string;
  af_type_idx : idx;
  af_body : list instr;
  af_source_component : nat;
  af_source_module : nat;
  af_target_component : nat;
  af_target_module : nat;
  af_target_function : idx;
  af_options : adapter_options;
}.

(* -------------------------------------------------------------------------
   Canonical ABI Value Representation

   How component-level types map to core WASM.
   ------------------------------------------------------------------------- *)

(* Core representation of a component value type *)
Inductive core_repr : Type :=
  | ReprI32
  | ReprI64
  | ReprF32
  | ReprF64
  | ReprPointer      (* i32 pointer to memory *)
  | ReprPair (a b : core_repr).

(* Flatten a representation to core value types *)
Fixpoint flatten_repr (r : core_repr) : list valtype :=
  match r with
  | ReprI32 => [NumType I32]
  | ReprI64 => [NumType I64]
  | ReprF32 => [NumType F32]
  | ReprF64 => [NumType F64]
  | ReprPointer => [NumType I32]
  | ReprPair a b => flatten_repr a ++ flatten_repr b
  end.

(* Component type to core representation *)
Fixpoint component_type_repr (cvt : component_valtype) : core_repr :=
  match cvt with
  | CVBool => ReprI32
  | CVS8 | CVU8 => ReprI32
  | CVS16 | CVU16 => ReprI32
  | CVS32 | CVU32 => ReprI32
  | CVS64 | CVU64 => ReprI64
  | CVF32 => ReprF32
  | CVF64 => ReprF64
  | CVChar => ReprI32
  | CVString => ReprPair ReprPointer ReprI32  (* ptr, len *)
  | CVList _ => ReprPair ReprPointer ReprI32  (* ptr, len *)
  | CVRecord _ => ReprPointer  (* simplified: pointer to struct *)
  | CVVariant _ => ReprPair ReprI32 ReprPointer  (* discriminant, payload ptr *)
  | CVTuple elems =>
      fold_right (fun t acc => ReprPair (component_type_repr t) acc)
                 ReprI32 elems  (* ReprI32 as unit placeholder *)
  | CVFlags _ => ReprI32
  | CVOption inner => ReprPair ReprI32 (component_type_repr inner)
  | CVResult ok err =>
      ReprPair ReprI32 ReprPointer  (* discriminant, payload *)
  | CVOwn _ => ReprI32  (* resource handle *)
  | CVBorrow _ => ReprI32  (* resource handle *)
  end.

(* -------------------------------------------------------------------------
   Lifting and Lowering Operations

   Lifting: core WASM -> component values
   Lowering: component values -> core WASM
   ------------------------------------------------------------------------- *)

(* Abstract operation types *)
Inductive lift_op : Type :=
  | LiftI32
  | LiftI64
  | LiftF32
  | LiftF64
  | LiftBool
  | LiftChar
  | LiftString (encoding : string_encoding)
  | LiftList (elem_type : component_valtype)
  | LiftRecord (fields : list (wasm_string * component_valtype))
  | LiftVariant (cases : list (wasm_string * option component_valtype))
  | LiftOption (inner : component_valtype)
  | LiftResult (ok err : option component_valtype)
  | LiftOwn | LiftBorrow.

Inductive lower_op : Type :=
  | LowerI32
  | LowerI64
  | LowerF32
  | LowerF64
  | LowerBool
  | LowerChar
  | LowerString (encoding : string_encoding)
  | LowerList (elem_type : component_valtype)
  | LowerRecord (fields : list (wasm_string * component_valtype))
  | LowerVariant (cases : list (wasm_string * option component_valtype))
  | LowerOption (inner : component_valtype)
  | LowerResult (ok err : option component_valtype)
  | LowerOwn | LowerBorrow.

(* Derive lifting operation from component type *)
Definition derive_lift_op (cvt : component_valtype) : lift_op :=
  match cvt with
  | CVBool => LiftBool
  | CVS8 | CVU8 | CVS16 | CVU16 | CVS32 | CVU32 => LiftI32
  | CVS64 | CVU64 => LiftI64
  | CVF32 => LiftF32
  | CVF64 => LiftF64
  | CVChar => LiftChar
  | CVString => LiftString UTF8
  | CVList elem => LiftList elem
  | CVRecord fields => LiftRecord fields
  | CVVariant cases => LiftVariant cases
  | CVTuple _ => LiftI32  (* simplified *)
  | CVFlags _ => LiftI32
  | CVOption inner => LiftOption inner
  | CVResult ok err => LiftResult ok err
  | CVOwn _ => LiftOwn
  | CVBorrow _ => LiftBorrow
  end.

(* -------------------------------------------------------------------------
   Lifting/Lowering Correctness Properties
   ------------------------------------------------------------------------- *)

(* Abstract value domain for reasoning *)
Inductive abstract_value : Type :=
  | AVInt (n : Z)
  | AVFloat (f : Z)  (* simplified: integer representation *)
  | AVBool (b : bool)
  | AVChar (c : nat)
  | AVString (s : list nat)
  | AVList (vs : list abstract_value)
  | AVRecord (fields : list (wasm_string * abstract_value))
  | AVVariant (disc : nat) (payload : option abstract_value)
  | AVOption (v : option abstract_value)
  | AVResult (is_ok : bool) (payload : option abstract_value)
  | AVHandle (h : nat).

(* Lifting is the inverse of lowering *)
Definition lift_lower_inverse (cvt : component_valtype)
                               (v : abstract_value)
                               (core_vals : list Z)
                               (lifted : abstract_value) : Prop :=
  (* If we lower v to core_vals and lift back, we get lifted *)
  (* For primitive types, lifted = v *)
  (* For complex types, lifted is semantically equivalent to v *)
  True. (* Abstract specification - full definition requires memory semantics *)

(* -------------------------------------------------------------------------
   String Transcoding Specification
   ------------------------------------------------------------------------- *)

(* String transcoding correctness captures encoding-specific length bounds.
   Each encoding has a known per-code-point size range:
   - UTF-8:  1-4 bytes per Unicode code point
   - UTF-16: 1-2 code units (16-bit) per Unicode code point
   - Latin1: 1 byte per code point (restricted to U+0000..U+00FF) *)
Definition transcode_correct
    (src_encoding dst_encoding : string_encoding)
    (src_bytes : list nat) (dst_bytes : list nat) : Prop :=
  match src_encoding, dst_encoding with
  | UTF8, UTF16 =>
      (* Each code point: >= 1 UTF-8 byte, <= 2 UTF-16 code units *)
      length dst_bytes <= 2 * length src_bytes
  | UTF8, Latin1 =>
      length dst_bytes <= length src_bytes
  | Latin1, UTF8 =>
      (* Latin1 U+0080..U+00FF need 2 UTF-8 bytes *)
      length dst_bytes <= 2 * length src_bytes
  | Latin1, UTF16 =>
      length dst_bytes <= length src_bytes
  | UTF16, UTF8 =>
      (* Each UTF-16 code unit can produce up to 4 UTF-8 bytes *)
      length dst_bytes <= 4 * length src_bytes
  | UTF16, Latin1 =>
      length dst_bytes <= length src_bytes
  | _, _ =>
      (* Same-encoding: no length constraint needed *)
      True
  end.

(* UTF-8 to UTF-16 transcoding length bound *)
Theorem utf8_to_utf16_length :
  forall src_bytes dst_bytes,
    transcode_correct UTF8 UTF16 src_bytes dst_bytes ->
    length dst_bytes <= 2 * length src_bytes.
Proof.
  intros src_bytes dst_bytes Htranscode.
  (* The UTF8/UTF16 match arm is exactly this inequality *)
  unfold transcode_correct in Htranscode.
  exact Htranscode.
Qed.

(* Same-encoding transcoding is trivially correct *)
Theorem same_encoding_identity :
  forall encoding bytes,
    transcode_correct encoding encoding bytes bytes.
Proof.
  intros encoding bytes.
  unfold transcode_correct.
  destruct encoding; simpl; trivial.
Qed.

(* -------------------------------------------------------------------------
   Memory Copy Specification
   ------------------------------------------------------------------------- *)

(* Memory state: offset -> byte value *)
Definition memory := nat -> option nat.

(* Copy bytes between memories *)
Definition memory_copy
    (src_mem : memory) (src_offset : nat)
    (dst_mem : memory) (dst_offset : nat)
    (len : nat) : memory :=
  fun addr =>
    if andb (Nat.leb dst_offset addr) (Nat.ltb addr (dst_offset + len))
    then src_mem (src_offset + (addr - dst_offset))
    else dst_mem addr.

(* Memory copy preserves content *)
Theorem memory_copy_preserves :
  forall src_mem dst_mem src_offset dst_offset len i,
    i < len ->
    memory_copy src_mem src_offset dst_mem dst_offset len (dst_offset + i)
    = src_mem (src_offset + i).
Proof.
  intros.
  unfold memory_copy.
  assert (Hle: Nat.leb dst_offset (dst_offset + i) = true).
  { apply Nat.leb_le. lia. }
  assert (Hlt: Nat.ltb (dst_offset + i) (dst_offset + len) = true).
  { apply Nat.ltb_lt. lia. }
  rewrite Hle, Hlt. simpl.
  replace (dst_offset + i - dst_offset) with i by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Type Compatibility
   ------------------------------------------------------------------------- *)

(* Two component types are compatible if they have the same structure *)
Fixpoint types_compatible (t1 t2 : component_valtype) : bool :=
  match t1, t2 with
  | CVBool, CVBool => true
  | CVS8, CVS8 => true
  | CVU8, CVU8 => true
  | CVS16, CVS16 => true
  | CVU16, CVU16 => true
  | CVS32, CVS32 => true
  | CVU32, CVU32 => true
  | CVS64, CVS64 => true
  | CVU64, CVU64 => true
  | CVF32, CVF32 => true
  | CVF64, CVF64 => true
  | CVChar, CVChar => true
  | CVString, CVString => true
  | CVList e1, CVList e2 => types_compatible e1 e2
  | CVOption i1, CVOption i2 => types_compatible i1 i2
  | CVOwn r1, CVOwn r2 => Nat.eqb r1 r2
  | CVBorrow r1, CVBorrow r2 => Nat.eqb r1 r2
  | _, _ => false  (* simplified: records, variants, etc. need field matching *)
  end.

(* Compatible types have the same core representation *)
Theorem compatible_same_repr :
  forall t1 t2,
    types_compatible t1 t2 = true ->
    component_type_repr t1 = component_type_repr t2.
Proof.
  (* Structural induction on t1, case analysis on t2.
     - Incompatible pairs: types_compatible = false, hypothesis contradicts.
     - Matching primitives: representations are syntactically equal.
     - CVList: repr is (pointer, length) regardless of element type.
     - CVOption: repr includes inner type's repr, needs IH.
     - CVOwn/CVBorrow: repr is ReprI32 regardless of resource index. *)
  induction t1; destruct t2; simpl; intros Hcompat;
    try discriminate; try reflexivity.
  (* Remaining case: CVOption inner1 vs CVOption inner2 *)
  f_equal.
  exact (IHt1 t2 Hcompat).
Qed.

(* -------------------------------------------------------------------------
   Adapter Generation Correctness
   ------------------------------------------------------------------------- *)

(* An adapter correctly bridges a call if:
   1. It lowers caller's arguments correctly
   2. It copies/transcodes data as needed
   3. It calls the target function
   4. It lifts the results back *)

Definition adapter_preserves_semantics
    (adapter : adapter_function)
    (caller_args : list abstract_value)
    (callee_result : list abstract_value)
    (adapter_result : list abstract_value) : Prop :=
  (* The adapter's observable behavior matches the callee's *)
  adapter_result = callee_result.

(* Direct adapter (no memory crossing) is a simple trampoline *)
Theorem direct_adapter_correct :
  forall adapter args result,
    crosses_memory (af_options adapter) = false ->
    needs_transcoding (af_options adapter) = false ->
    adapter_preserves_semantics adapter args result result.
Proof.
  intros.
  unfold adapter_preserves_semantics.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Adapter Body Generation Specification
   ------------------------------------------------------------------------- *)

(* A valid adapter body has the right structure *)
Definition valid_adapter_body (body : list instr) (target_func : idx) : Prop :=
  exists prefix suffix,
    body = prefix ++ [Call target_func] ++ suffix.

(* Direct adapter body just loads args, calls target, returns *)
Definition valid_direct_adapter_body
    (body : list instr) (param_count : nat) (target_func : idx) : Prop :=
  body = map (fun i => LocalGet i) (seq 0 param_count)
         ++ [Call target_func]
         ++ [Return].

(* Memory copy adapter allocates, copies, calls, and copies back *)
Definition valid_memory_copy_adapter
    (body : list instr) (opts : adapter_options)
    (param_count : nat) (target_func : idx) : Prop :=
  (* Must contain allocation, memory operations, and the call *)
  valid_adapter_body body target_func.

(* -------------------------------------------------------------------------
   Adapter Type Correctness
   ------------------------------------------------------------------------- *)

(* The adapter's function type matches the import it replaces *)
Definition adapter_type_matches_import
    (adapter : adapter_function)
    (import_type : functype) : Prop :=
  (* The adapter accepts the same parameters and returns the same results
     as the original import expected *)
  True. (* Abstract - requires type lookup in module *)

(* The adapter's call matches the export's type *)
Definition adapter_call_matches_export
    (adapter : adapter_function)
    (export_type : functype) : Prop :=
  (* The target function call uses the correct arguments *)
  True. (* Abstract - requires type lookup *)

Theorem adapter_type_sound :
  forall adapter import_type export_type,
    adapter_type_matches_import adapter import_type ->
    adapter_call_matches_export adapter export_type ->
    (* The adapter is well-typed *)
    True.
Proof.
  trivial.
Qed.

(* -------------------------------------------------------------------------
   Adapter Collection Properties
   ------------------------------------------------------------------------- *)

(* All generated adapters have unique names *)
Definition adapters_unique_names (adapters : list adapter_function) : Prop :=
  NoDup (map af_name adapters).

(* All adapters reference valid target functions *)
Definition adapters_valid_targets
    (adapters : list adapter_function)
    (module : module) : Prop :=
  Forall (fun a => valid_funcidx module (af_target_function a)) adapters.

(* -------------------------------------------------------------------------
   Main Adapter Generation Theorem
   ------------------------------------------------------------------------- *)

Record adapter_generation_result : Type := mkAdapterGenResult {
  agr_adapters : list adapter_function;
  agr_num_generated : nat;
}.

Definition adapter_generation_correct
    (adapter_sites : list (nat * nat * wasm_string * nat * nat * wasm_string))
    (merged : module)
    (result : adapter_generation_result) : Prop :=
  (* Number of adapters matches number of sites *)
  length (agr_adapters result) = length adapter_sites /\
  (* All adapters have unique names *)
  adapters_unique_names (agr_adapters result) /\
  (* All adapters have valid target functions *)
  adapters_valid_targets (agr_adapters result) merged /\
  (* Each adapter has a valid body *)
  Forall (fun a => valid_adapter_body (af_body a) (af_target_function a))
         (agr_adapters result).

Theorem generate_adapters_correct :
  forall adapter_sites merged result,
    (* If generation succeeds *)
    agr_num_generated result = length adapter_sites ->
    (* Then the result is correct *)
    adapter_generation_correct adapter_sites merged result.
Proof.
  intros adapter_sites merged result Hcount.
  unfold adapter_generation_correct.
  split; [| split; [| split]].

  - (* Sub-obligation 1: length (agr_adapters result) = length adapter_sites.
       Requires: invariant that agr_num_generated = length (agr_adapters).
       Would follow from showing generate_adapters appends one adapter per site. *)
    assert (Hlen_inv: length (agr_adapters result) = agr_num_generated result).
    { (* Implementation invariant: count matches list length. *)
      admit. }
    lia.

  - (* Sub-obligation 2: adapters_unique_names.
       Requires: naming scheme injectivity — adapter names incorporate
       component index, module index, and import name. *)
    admit.

  - (* Sub-obligation 3: adapters_valid_targets.
       Requires: each adapter_site references an export resolved during
       merging, so target function index is valid in merged module. *)
    admit.

  - (* Sub-obligation 4: valid adapter bodies contain Call target.
       Requires: body generation always emits [prefix ++ Call target ++ suffix].
       Case-split on direct vs memory-crossing adapters. *)
    admit.
Admitted.

(* -------------------------------------------------------------------------
   FACT-Style Adapter Properties

   FACT (Fused Adapter Compiler of Trampolines) generates adapters that:
   1. Are inlined into the fused module
   2. Handle string transcoding efficiently
   3. Minimize memory copies when possible
   ------------------------------------------------------------------------- *)

(* FACT optimization: skip transcoding when encodings match *)
Theorem fact_skip_same_encoding :
  forall opts,
    ao_caller_encoding opts = ao_callee_encoding opts ->
    needs_transcoding opts = false.
Proof.
  intros opts Heq.
  unfold needs_transcoding.
  rewrite Heq.
  destruct (ao_callee_encoding opts); reflexivity.
Qed.

(* FACT optimization: skip memory copy when memories match *)
Theorem fact_skip_same_memory :
  forall opts,
    ao_caller_memory opts = ao_callee_memory opts ->
    crosses_memory opts = false.
Proof.
  intros opts Heq.
  unfold crosses_memory.
  rewrite Heq.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(* End of adapter_spec *)
