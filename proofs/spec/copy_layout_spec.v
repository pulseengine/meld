(* =========================================================================
   CopyLayout and ConditionalPointerPair Specification

   Source: meld-core/src/resolver.rs (CopyLayout, ConditionalPointerPair)
           meld-core/src/parser.rs  (copy_layout, element_inner_pointers)
           meld-core/src/adapter/fact.rs (emit_inner_pointer_fixup)

   This module defines the Rocq model of CopyLayout and ConditionalPointerPair,
   the two types that govern how pointer-bearing data is copied across linear
   memories during cross-component adapter calls.

   CopyLayout is an enum:
     - Bulk { byte_multiplier }       -- flat copy, no inner pointers
     - Elements { element_size, inner_pointers } -- element-wise with fixups

   ConditionalPointerPair gates a pointer copy on a discriminant value
   (used for option<T>, result<T, E>, variant types).

   Spec baselines: see proofs/DECISIONS.md.
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith PeanoNat.
Import ListNotations.

(* -------------------------------------------------------------------------
   CopyLayout: describes how to copy a (ptr, len) value across memories

   Mirrors Rust:
     pub enum CopyLayout {
         Bulk { byte_multiplier: u32 },
         Elements { element_size: u32, inner_pointers: Vec<(u32, CopyLayout)> },
     }
   ------------------------------------------------------------------------- *)

Inductive copy_layout : Type :=
  | CLBulk (byte_multiplier : nat)
  | CLElements (element_size : nat) (inner_pointers : list (nat * copy_layout)).

(* -------------------------------------------------------------------------
   ConditionalPointerPair: a pointer pair guarded by a discriminant

   Mirrors Rust:
     pub struct ConditionalPointerPair {
         pub discriminant_position: u32,
         pub discriminant_value: u32,
         pub ptr_position: u32,
         pub copy_layout: CopyLayout,
     }
   ------------------------------------------------------------------------- *)

Record conditional_pointer_pair : Type := mkConditionalPointerPair {
  cpp_discriminant_position : nat;
  cpp_discriminant_value : nat;
  cpp_ptr_position : nat;
  cpp_copy_layout : copy_layout;
}.

(* -------------------------------------------------------------------------
   Memory Model

   A linear memory is modeled as a partial function from byte addresses to
   byte values. An address is accessible iff the memory returns Some at
   that address.
   ------------------------------------------------------------------------- *)

Definition memory := nat -> option nat.

(* A range [base, base+len) is accessible in a memory *)
Definition range_accessible (mem : memory) (base len : nat) : Prop :=
  forall i, i < len -> exists v, mem (base + i) = Some v.

(* -------------------------------------------------------------------------
   CopyLayout Structural Properties
   ------------------------------------------------------------------------- *)

(* Structural depth of a CopyLayout (for reasoning about fixup nesting).
   Because copy_layout is a nested inductive (list of pairs containing
   copy_layout), we define depth via a mutual fixpoint over the type
   and its inner pointer list. *)
Fixpoint copy_layout_depth (cl : copy_layout) : nat :=
  match cl with
  | CLBulk _ => 0
  | CLElements _ ips =>
      match ips with
      | [] => 0
      | _ => 1 + copy_layout_list_max_depth ips
      end
  end
with copy_layout_list_max_depth (ips : list (nat * copy_layout)) : nat :=
  match ips with
  | [] => 0
  | (_, cl) :: rest => Nat.max (copy_layout_depth cl) (copy_layout_list_max_depth rest)
  end.

(* Total byte size of a single element in an Elements layout *)
Definition element_total_bytes (cl : copy_layout) (count : nat) : nat :=
  match cl with
  | CLBulk byte_mult => count * byte_mult
  | CLElements elem_size _ => count * elem_size
  end.

(* The effective byte multiplier for any layout *)
Definition effective_byte_multiplier (cl : copy_layout) : nat :=
  match cl with
  | CLBulk m => m
  | CLElements s _ => s
  end.

(* -------------------------------------------------------------------------
   CopyLayout Well-Formedness

   A CopyLayout is well-formed when:
   1. Bulk: byte_multiplier > 0
   2. Elements: element_size > 0, and for each inner pointer
      (offset, inner_layout):
      a. offset + 8 <= element_size  (ptr + len fit within the element)
      b. inner_layout is itself well-formed
      c. offsets do not overlap (each pointer pair occupies 8 bytes)
   ------------------------------------------------------------------------- *)

(* Two pointer pairs at offsets o1 and o2 do not overlap.
   Each pointer pair occupies 8 bytes: 4 for ptr, 4 for len. *)
Definition pointer_pairs_disjoint (o1 o2 : nat) : Prop :=
  o1 + 8 <= o2 \/ o2 + 8 <= o1.

(* All pointer pairs in a list have pairwise disjoint ranges *)
Definition inner_pointers_disjoint (ips : list (nat * copy_layout)) : Prop :=
  forall i j ip1 ip2,
    nth_error ips i = Some ip1 ->
    nth_error ips j = Some ip2 ->
    i <> j ->
    pointer_pairs_disjoint (fst ip1) (fst ip2).

(* Well-formedness of a CopyLayout, defined via mutual recursion over
   the nested structure. The list recursion ensures Rocq accepts
   the termination argument for the nested inductive type. *)
Fixpoint copy_layout_wf (cl : copy_layout) : Prop :=
  match cl with
  | CLBulk byte_mult =>
      byte_mult > 0
  | CLElements elem_size ips =>
      elem_size > 0 /\
      (* Every inner pointer pair fits within the element *)
      (forall offset inner_cl,
        In (offset, inner_cl) ips ->
        offset + 8 <= elem_size) /\
      (* Every inner layout is itself well-formed *)
      copy_layout_list_wf ips /\
      (* Inner pointer pairs do not overlap *)
      inner_pointers_disjoint ips
  end
with copy_layout_list_wf (ips : list (nat * copy_layout)) : Prop :=
  match ips with
  | [] => True
  | (_, cl) :: rest => copy_layout_wf cl /\ copy_layout_list_wf rest
  end.

(* Relate list well-formedness to In-based formulation *)
Lemma copy_layout_list_wf_In : forall ips offset inner_cl,
  copy_layout_list_wf ips ->
  In (offset, inner_cl) ips ->
  copy_layout_wf inner_cl.
Proof.
  induction ips as [| [o cl] rest IH].
  - intros offset inner_cl _ Hin. contradiction.
  - intros offset inner_cl Hwf Hin.
    simpl in Hwf. destruct Hwf as [Hcl Hrest].
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst. exact Hcl.
    + exact (IH offset inner_cl Hrest Hin).
Qed.

(* -------------------------------------------------------------------------
   ConditionalPointerPair Well-Formedness

   A ConditionalPointerPair is well-formed with respect to a parameter
   count (the number of flat parameters in the function signature) when:
   1. discriminant_position < param_count
   2. ptr_position + 1 < param_count  (ptr and len are consecutive)
   3. discriminant_position <> ptr_position
   4. discriminant_position <> ptr_position + 1
   5. The copy layout is well-formed
   ------------------------------------------------------------------------- *)

Definition conditional_pointer_pair_wf
    (cpp : conditional_pointer_pair) (param_count : nat) : Prop :=
  cpp_discriminant_position cpp < param_count /\
  cpp_ptr_position cpp + 1 < param_count /\
  cpp_discriminant_position cpp <> cpp_ptr_position cpp /\
  cpp_discriminant_position cpp <> cpp_ptr_position cpp + 1 /\
  copy_layout_wf (cpp_copy_layout cpp).

(* Byte-offset variant for return-area conditional pairs.
   Positions refer to byte offsets within the return area, not flat indices.
   The discriminant is 4 bytes (i32), the pointer pair is 8 bytes (ptr + len). *)
Definition conditional_pointer_pair_retptr_wf
    (cpp : conditional_pointer_pair) (return_area_size : nat) : Prop :=
  cpp_discriminant_position cpp + 4 <= return_area_size /\
  cpp_ptr_position cpp + 8 <= return_area_size /\
  (* discriminant must not overlap with the pointer pair *)
  (cpp_discriminant_position cpp + 4 <= cpp_ptr_position cpp \/
   cpp_ptr_position cpp + 8 <= cpp_discriminant_position cpp) /\
  copy_layout_wf (cpp_copy_layout cpp).

(* -------------------------------------------------------------------------
   Memory Copy Operation

   Copy len bytes from src_mem[src_base..] to dst_mem[dst_base..].
   Returns the updated destination memory.
   ------------------------------------------------------------------------- *)

Definition memory_copy
    (src_mem : memory) (src_base : nat)
    (dst_mem : memory) (dst_base : nat)
    (len : nat) : memory :=
  fun addr =>
    if andb (Nat.leb dst_base addr) (Nat.ltb addr (dst_base + len))
    then src_mem (src_base + (addr - dst_base))
    else dst_mem addr.

(* -------------------------------------------------------------------------
   Bulk Copy Specification

   For a Bulk layout with byte_multiplier m, copying count elements
   means copying count * m bytes from source to destination.
   ------------------------------------------------------------------------- *)

Definition bulk_copy_spec
    (src_mem : memory) (src_base : nat)
    (dst_mem : memory) (dst_base : nat)
    (byte_mult : nat) (count : nat) : memory :=
  memory_copy src_mem src_base dst_mem dst_base (count * byte_mult).

(* -------------------------------------------------------------------------
   Copy Completeness for Bulk Layout

   After a bulk copy of count * byte_mult bytes, every byte in the
   destination range [dst_base, dst_base + count * byte_mult) equals the
   corresponding byte in the source range.
   ------------------------------------------------------------------------- *)

Definition copy_complete
    (src_mem dst_mem_after : memory) (src_base dst_base len : nat) : Prop :=
  forall i, i < len ->
    dst_mem_after (dst_base + i) = src_mem (src_base + i).

(* -------------------------------------------------------------------------
   Memory Safety for Copy Operations

   A copy operation is memory-safe when:
   1. The source range [src_base, src_base + len) is readable
   2. The destination range [dst_base, dst_base + len) is writable
      (modeled as accessible)
   3. No writes occur outside [dst_base, dst_base + len)
   ------------------------------------------------------------------------- *)

Definition copy_memory_safe
    (dst_mem dst_mem_after : memory)
    (dst_base len : nat) : Prop :=
  forall addr,
    addr < dst_base \/ addr >= dst_base + len ->
    dst_mem_after addr = dst_mem addr.

(* -------------------------------------------------------------------------
   Conditional Copy Specification

   A conditional copy checks the discriminant at discriminant_position:
   - If discriminant equals discriminant_value, copy the pointed-to data
   - Otherwise, leave the destination memory unchanged

   For flat params: discriminant_position and ptr_position are flat
   local indices. The actual pointer and length are read from locals.

   For return-area: discriminant_position and ptr_position are byte
   offsets within the return area.
   ------------------------------------------------------------------------- *)

(* The result of evaluating a conditional copy *)
Inductive conditional_copy_result : Type :=
  | CCSkipped   (* discriminant did not match *)
  | CCCopied    (* discriminant matched, data was copied *)
    (new_ptr : nat)   (* new pointer in destination memory *)
    (byte_len : nat). (* number of bytes copied *)

(* A conditional copy is correct when:
   - If disc = expected: data is copied and pointer is updated
   - If disc <> expected: nothing changes *)
Definition conditional_copy_correct
    (disc_value expected : nat)
    (src_mem : memory) (src_ptr src_len : nat)
    (dst_mem dst_mem_after : memory)
    (result : conditional_copy_result)
    (cl : copy_layout) : Prop :=
  if Nat.eqb disc_value expected then
    match result with
    | CCCopied new_ptr byte_len =>
        let effective_len := src_len * effective_byte_multiplier cl in
        byte_len = effective_len /\
        copy_complete src_mem dst_mem_after src_ptr new_ptr effective_len /\
        copy_memory_safe dst_mem dst_mem_after new_ptr effective_len
    | CCSkipped => False
    end
  else
    result = CCSkipped.

(* End of copy_layout_spec *)
