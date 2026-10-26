import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.BackendCommon.ClosTags
import Flapjack.Misc.Sptree

/-! Constant flattening and operator translation for closure conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon ClosLang

/-- Hash a constant component into the original fixed-size bucket space. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "part_hash_def"]
def partHash : ConstPart → Nat
  | .int i => i.natAbs % 999983
  | .str s => (s.explode.length + 3 * (s.explode.map BitVec.toNat).sum) % 999983
  | .w64 w => (17 + w.toNat) % 999983
  | .con t ns => (18 + 5 * t + 7 * ns.sum) % 999983

/-- HOL `ALOOKUP` on a constant-part bucket. -/
private def lookupPart (p : ConstPart) : List (ConstPart × Nat) → Option Nat
  | [] => none
  | (q, n) :: xs => if p = q then some n else lookupPart p xs

/-- Hash-cons one component, preserving bucket and accumulated-list order. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "add_part_def"]
def addPart (n : Nat) (p : ConstPart) (aux : Spt (List (ConstPart × Nat)))
    (acc : List ConstPart) : Nat × Nat × Spt (List (ConstPart × Nat)) × List ConstPart :=
  let h := partHash p
  match sptLookup h aux with
  | none => (n + 1, n, sptInsert h [(p, n)] aux, p :: acc)
  | some bucket =>
      match lookupPart p bucket with
      | none => (n + 1, n, sptInsert h ((p, n) :: bucket) aux, p :: acc)
      | some k => (n, k, aux, acc)

mutual
/-- Flatten a constant recursively, sharing equal components. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "add_parts_def"]
def addParts (c : Const) (n : Nat) (aux : Spt (List (ConstPart × Nat)))
    (acc : List ConstPart) : Nat × Nat × Spt (List (ConstPart × Nat)) × List ConstPart :=
  match c with
  | .constInt i => addPart n (.int i) aux acc
  | .constStr s => addPart n (.str s) aux acc
  | .constWord64 w => addPart n (.w64 w) aux acc
  | .constCons t cs =>
      let (n, rs, aux, acc) := addPartsList cs n aux acc
      addPart n (.con (closTagShift t) rs) aux acc

/-- Flatten a list of constants in source order. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "add_parts_def"]
def addPartsList (cs : List Const) (n : Nat) (aux : Spt (List (ConstPart × Nat)))
    (acc : List ConstPart) : Nat × List Nat × Spt (List (ConstPart × Nat)) × List ConstPart :=
  match cs with
  | [] => (n, [], aux, acc)
  | c :: cs =>
      let (n, r, aux, acc) := addParts c n aux acc
      let (n, rs, aux, acc) := addPartsList cs n aux acc
      (n, r :: rs, aux, acc)
end

/-- Translate a closure constant into the corresponding BVL operator. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_const_def"]
def compileConst : Const → Op
  | .constInt i => .intOp (.const i)
  | .constStr s => .blockOp (.build [.str s])
  | .constWord64 w => .blockOp (.build [.w64 w])
  | .constCons t cs =>
      if cs.isEmpty then .blockOp (.cons (closTagShift t))
      else
        let (_, rs, _, acc) := addPartsList cs 0 .ln []
        .blockOp (.build ((ConstPart.con (closTagShift t) rs :: acc).reverse))

/-- One global is reserved for the partial-application label table. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "num_added_globals_def"]
def numAddedGlobals : Nat := 1

/-- Location of the partial-application label table. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "partial_app_label_table_loc_def"]
def partialAppLabelTableLoc : Nat := 0

/-- Translate a closure operator into its BVL operator, retaining all other
operators unchanged. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_op_def"]
def compileOp : Op → Op
  | .blockOp (.cons t) => .blockOp (.cons (closTagShift t))
  | .blockOp (.consExtend t) => .blockOp (.consExtend (closTagShift t))
  | .blockOp (.tagEq t) => .blockOp (.tagEq (closTagShift t))
  | .blockOp (.tagLenEq t a) => .blockOp (.tagLenEq (closTagShift t) a)
  | .blockOp (.fromList t) => .blockOp (.fromList (closTagShift t))
  | .memOp .lengthByteVec => .memOp .lengthByte
  | .memOp .derefByteVec => .memOp .derefByte
  | .globOp (.setGlobal n) => .globOp (.setGlobal (n + numAddedGlobals))
  | .globOp (.global n) => .globOp (.global (n + numAddedGlobals))
  | .blockOp (.constant c) => compileConst c
  | op => op

end Flapjack.Compiler.Backend.ClosToBvl
