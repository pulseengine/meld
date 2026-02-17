(* =========================================================================
   WebAssembly Core Semantics Model

   Baseline: WebAssembly Core Specification, Release 3.0
   See: https://webassembly.github.io/spec/core/

   This module defines the abstract syntax and operational semantics for
   WebAssembly core modules, sufficient for reasoning about fusion.
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia.
Import ListNotations.

(* Use nat as placeholder for strings - can be refined later *)
Definition wasm_string := nat.

(* -------------------------------------------------------------------------
   Value Types
   ------------------------------------------------------------------------- *)

Inductive numtype : Type :=
  | I32 | I64 | F32 | F64.

Inductive vectype : Type :=
  | V128.

Inductive reftype : Type :=
  | FuncRef | ExternRef.

Inductive valtype : Type :=
  | NumType (n : numtype)
  | VecType (v : vectype)
  | RefType (r : reftype).

(* -------------------------------------------------------------------------
   Index Spaces

   WebAssembly uses separate index spaces for functions, tables, memories,
   and globals. During fusion, these indices must be remapped.
   ------------------------------------------------------------------------- *)

Inductive index_space : Type :=
  | FuncIdx
  | TableIdx
  | MemIdx
  | GlobalIdx
  | TypeIdx
  | ElemIdx
  | DataIdx.

Definition idx := nat.

(* -------------------------------------------------------------------------
   Function Types
   ------------------------------------------------------------------------- *)

Record functype : Type := mkFunctype {
  ft_params : list valtype;
  ft_results : list valtype;
}.

(* -------------------------------------------------------------------------
   Limits (for memories and tables)
   ------------------------------------------------------------------------- *)

Record limits : Type := mkLimits {
  lim_min : nat;
  lim_max : option nat;
}.

(* -------------------------------------------------------------------------
   Memory Types
   ------------------------------------------------------------------------- *)

Record memtype : Type := mkMemtype {
  mem_limits : limits;
  mem_shared : bool;
}.

(* -------------------------------------------------------------------------
   Table Types
   ------------------------------------------------------------------------- *)

Record tabletype : Type := mkTabletype {
  tab_limits : limits;
  tab_reftype : reftype;
}.

(* -------------------------------------------------------------------------
   Global Types
   ------------------------------------------------------------------------- *)

Inductive mutability : Type :=
  | Const | Var.

Record globaltype : Type := mkGlobaltype {
  glob_mut : mutability;
  glob_valtype : valtype;
}.

(* -------------------------------------------------------------------------
   Import/Export Descriptors
   ------------------------------------------------------------------------- *)

Inductive importdesc : Type :=
  | ImportFunc (typeidx : idx)
  | ImportTable (tt : tabletype)
  | ImportMem (mt : memtype)
  | ImportGlobal (gt : globaltype).

Inductive exportdesc : Type :=
  | ExportFunc (funcidx : idx)
  | ExportTable (tableidx : idx)
  | ExportMem (memidx : idx)
  | ExportGlobal (globalidx : idx).

(* -------------------------------------------------------------------------
   Instructions (simplified for fusion reasoning)

   We model only the instructions relevant to index remapping.
   ------------------------------------------------------------------------- *)

Inductive instr : Type :=
  (* Control *)
  | Nop
  | Unreachable
  | Block (bt : option functype) (body : list instr)
  | Loop (bt : option functype) (body : list instr)
  | If (bt : option functype) (then_ : list instr) (else_ : list instr)
  | Br (labelidx : idx)
  | BrIf (labelidx : idx)
  | BrTable (labels : list idx) (default : idx)
  | Return
  | Call (funcidx : idx)
  | CallIndirect (tableidx : idx) (typeidx : idx)
  (* Parametric *)
  | Drop
  | Select (ts : option (list valtype))
  (* Variable *)
  | LocalGet (localidx : idx)
  | LocalSet (localidx : idx)
  | LocalTee (localidx : idx)
  | GlobalGet (globalidx : idx)
  | GlobalSet (globalidx : idx)
  (* Memory *)
  | MemorySize (memidx : idx)
  | MemoryGrow (memidx : idx)
  | Load (vt : valtype) (memidx : idx) (memarg_offset : nat) (memarg_align : nat)
  | Store (vt : valtype) (memidx : idx) (memarg_offset : nat) (memarg_align : nat)
  (* Numeric (opaque for fusion) *)
  | NumericOp (op : nat)
  (* Reference *)
  | RefNull (rt : reftype)
  | RefIsNull
  | RefFunc (funcidx : idx)
  (* Table *)
  | TableGet (tableidx : idx)
  | TableSet (tableidx : idx)
  | TableSize (tableidx : idx)
  | TableGrow (tableidx : idx)
  | TableFill (tableidx : idx)
  | TableCopy (dst : idx) (src : idx)
  | TableInit (tableidx : idx) (elemidx : idx)
  | ElemDrop (elemidx : idx)
  (* Memory bulk *)
  | MemoryCopy (dst_memidx : idx) (src_memidx : idx)
  | MemoryFill (memidx : idx)
  | MemoryInit (dataidx : idx) (memidx : idx)
  | DataDrop (dataidx : idx).

(* -------------------------------------------------------------------------
   Module Structure
   ------------------------------------------------------------------------- *)

Record import : Type := mkImport {
  imp_module : wasm_string;
  imp_name : wasm_string;
  imp_desc : importdesc;
}.

Record export : Type := mkExport {
  exp_name : wasm_string;
  exp_desc : exportdesc;
}.

Record func : Type := mkFunc {
  func_type : idx;
  func_locals : list valtype;
  func_body : list instr;
}.

Record global : Type := mkGlobal {
  global_type : globaltype;
  global_init : list instr;
}.

Record elem : Type := mkElem {
  elem_type : reftype;
  elem_init : list (list instr);
  elem_mode : nat; (* 0=passive, 1=active, 2=declarative - simplified *)
}.

Record data : Type := mkData {
  data_init : list nat; (* bytes as nats *)
  data_mode : nat; (* 0=passive, 1=active - simplified *)
}.

Record module : Type := mkModule {
  mod_types : list functype;
  mod_funcs : list func;
  mod_tables : list tabletype;
  mod_mems : list memtype;
  mod_globals : list global;
  mod_elems : list elem;
  mod_datas : list data;
  mod_start : option idx;
  mod_imports : list import;
  mod_exports : list export;
}.

(* -------------------------------------------------------------------------
   Index Counting

   The number of imports affects where defined indices start.
   ------------------------------------------------------------------------- *)

Definition count_func_imports (m : module) : nat :=
  length (List.filter (fun i => match imp_desc i with ImportFunc _ => true | _ => false end)
                 (mod_imports m)).

Definition count_table_imports (m : module) : nat :=
  length (List.filter (fun i => match imp_desc i with ImportTable _ => true | _ => false end)
                 (mod_imports m)).

Definition count_mem_imports (m : module) : nat :=
  length (List.filter (fun i => match imp_desc i with ImportMem _ => true | _ => false end)
                 (mod_imports m)).

Definition count_global_imports (m : module) : nat :=
  length (List.filter (fun i => match imp_desc i with ImportGlobal _ => true | _ => false end)
                 (mod_imports m)).

(* -------------------------------------------------------------------------
   Well-formedness (simplified)
   ------------------------------------------------------------------------- *)

Definition valid_funcidx (m : module) (i : idx) : Prop :=
  i < count_func_imports m + length (mod_funcs m).

Definition valid_tableidx (m : module) (i : idx) : Prop :=
  i < count_table_imports m + length (mod_tables m).

Definition valid_memidx (m : module) (i : idx) : Prop :=
  i < count_mem_imports m + length (mod_mems m).

Definition valid_globalidx (m : module) (i : idx) : Prop :=
  i < count_global_imports m + length (mod_globals m).

Definition valid_typeidx (m : module) (i : idx) : Prop :=
  i < length (mod_types m).

(* End of wasm_core specification *)
