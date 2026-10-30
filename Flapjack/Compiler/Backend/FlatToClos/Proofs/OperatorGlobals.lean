import Flapjack.Compiler.Backend.FlatToClos.Op
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Mathlib.Tactic.Tauto

/-! Global-write safety of generated primitive operations. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendCommon Flapjack.Compiler.Backend.ClosProps

/-- Arithmetic lowering introduces no unsafe closure. -/
theorem compileArith_safe (t : Tra) (a : Flapjack.AstHOL.Arith)
    (ty : Flapjack.AstHOL.PrimType) (xs : List ClosLang.Exp)
    (safe : esgcFreeList xs) : esgcFree (compileArith t a ty xs) := by
  cases ty <;> cases a <;> simp [compileArith, esgcFree, esgcFreeList, safe]

/-- Arithmetic lowering preserves the operand global-write bag. -/
theorem compileArith_globals (t : Tra) (a : Flapjack.AstHOL.Arith)
    (ty : Flapjack.AstHOL.PrimType) (xs : List ClosLang.Exp) :
    setGlobals (compileArith t a ty xs) = elistGlobals xs := by
  funext key
  cases ty <;> cases a <;> simp [compileArith, setGlobals, elistGlobals, opGlobalBag,
    Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]

/-- Primitive lowering preserves closure safety for safe operand lists. -/
theorem compileOp_safe (t : Tra) (op : FlatLang.Op) (xs : List ClosLang.Exp)
    (safe : esgcFreeList xs) : esgcFree (compileOp t op xs) := by
  cases op with
  | src op =>
    cases op <;> simp [compileOp, esgcFree, esgcFreeList, safe, copyByteStr_globalSafe,
      copyByteAw8_globalSafe, compileArith_safe]
    case opapp | opassign =>
      cases xs with
      | nil => simp [arg2, esgcFree, esgcFreeList]
      | cons x xs =>
        cases xs with
        | nil => simp [arg2, esgcFree, safe]
        | cons y ys =>
          cases ys <;> simp [arg2, esgcFree, esgcFreeList] at safe ⊢ <;> tauto
    case test test ty =>
      cases ty <;> cases test
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try cases ‹Opb›
      all_goals simp [esgcFree, safe]
    case fromTo a b =>
      cases a <;> cases b
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try simp [esgcFree, safe]
      all_goals cases xs with
        | nil => simp [arg1, esgcFree, esgcFreeList]
        | cons x xs => cases xs <;> simp [arg1, esgcFree, esgcFreeList] at safe ⊢ <;> tauto
  | globalVarAlloc n => simp [compileOp, esgcFree, esgcFreeList, safe]
  | globalVarInit n => simp [compileOp, esgcFree, safe]
  | globalVarLookup n => simp [compileOp, esgcFree, safe]
  | tagLenEq tag n => simp [compileOp, esgcFree, safe]
  | lenEq n => simp [compileOp, esgcFree, safe]
  | el n =>
    cases xs with
    | nil => simp [compileOp, arg1, esgcFree, esgcFreeList]
    | cons x xs => cases xs <;> simp [compileOp, arg1, esgcFree, esgcFreeList] at safe ⊢ <;> tauto
  | id =>
    cases xs with
    | nil => simp [compileOp, arg1, esgcFree, esgcFreeList]
    | cons x xs => cases xs <;> simp [compileOp, arg1, esgcFree, esgcFreeList] at safe ⊢ <;> tauto

/-- The flat operation's write contribution after the closure slot shift. -/
def loweredOpBag : FlatLang.Op → Flapjack.Compiler.Backend.FlatProps.GlobalBag
  | .globalVarInit n => fun key => if key = n + 1 then 1 else 0
  | _ => Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag

/-- The slot-shifted operation bag is the source bag shifted by one. -/
theorem loweredOpBag_shift (op : FlatLang.Op) (key : Nat) :
    loweredOpBag op key = if key = 0 then 0 else
      Flapjack.Compiler.Backend.FlatProps.opGlobalBag op (key - 1) := by
  cases op <;> simp [loweredOpBag, Flapjack.Compiler.Backend.FlatProps.opGlobalBag,
    Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  case globalVarInit n =>
    cases key with
    | zero => simp
    | succ k => simp

/-- Operator lowering preserves operand writes and shifts the operator's global slot. -/
theorem compileOp_globals (t : Tra) (op : FlatLang.Op) (xs : List ClosLang.Exp) :
    setGlobals (compileOp t op xs) =
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag (loweredOpBag op) (elistGlobals xs) := by
  funext key
  cases op with
  | src op =>
    cases op <;> simp [compileOp, setGlobals, elistGlobals, opGlobalBag, loweredOpBag,
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag,
      compileArith_globals, copyByteStr_noGlobals, copyByteAw8_noGlobals]
    case opapp | opassign =>
      cases xs with
      | nil => simp [arg2, setGlobals, elistGlobals,
          Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
      | cons x xs =>
        cases xs with
        | nil => simp [arg2, setGlobals, elistGlobals,
            Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
        | cons y ys =>
          cases ys <;> simp [arg2, setGlobals, elistGlobals, opGlobalBag,
            Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
          all_goals omega
    case test test ty =>
      cases ty <;> cases test
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try cases ‹Opb›
      all_goals simp [setGlobals, opGlobalBag, Flapjack.Compiler.Backend.FlatProps.unionGlobalBag,
        Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
    case fromTo a b =>
      cases a <;> cases b
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try simp [setGlobals, opGlobalBag, Flapjack.Compiler.Backend.FlatProps.unionGlobalBag,
        Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
      all_goals cases xs with
        | nil => simp [arg1, setGlobals, elistGlobals, opGlobalBag,
            Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
        | cons x xs => cases xs <;> simp [arg1, setGlobals, elistGlobals, opGlobalBag,
            Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  | globalVarAlloc n => simp [compileOp, setGlobals, elistGlobals, opGlobalBag, loweredOpBag,
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  | globalVarInit n => simp [compileOp, setGlobals, opGlobalBag, loweredOpBag,
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag]
  | globalVarLookup n => simp [compileOp, setGlobals, opGlobalBag, loweredOpBag,
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  | tagLenEq tag n => simp [compileOp, setGlobals, opGlobalBag, loweredOpBag,
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  | lenEq n => simp [compileOp, setGlobals, opGlobalBag, loweredOpBag,
      Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  | el n =>
    cases xs with
    | nil => simp [compileOp, arg1, setGlobals, elistGlobals, loweredOpBag,
        Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
    | cons x xs => cases xs <;> simp [compileOp, arg1, setGlobals, elistGlobals, opGlobalBag, loweredOpBag,
        Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
  | id =>
    cases xs with
    | nil => simp [compileOp, arg1, setGlobals, elistGlobals, loweredOpBag,
        Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]
    | cons x xs => cases xs <;> simp [compileOp, arg1, setGlobals, elistGlobals, loweredOpBag,
        Flapjack.Compiler.Backend.FlatProps.unionGlobalBag, Flapjack.Compiler.Backend.FlatProps.emptyGlobalBag]

end Flapjack.Compiler.Backend.FlatToClos
