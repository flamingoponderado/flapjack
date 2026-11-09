module

public import Flapjack.Compiler.Backend.FlatLang
public import Flapjack.Compiler.Backend.ClosLang.Syntax

@[expose] public section

/-! Literal conversion and constructor helpers for flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- Extract the single variable branch used by closure-language handlers. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "dest_pat_def"]
def destPat {α : Type} : List (FlatLang.Pat × α) → Option (MlString × α)
  | [(.pvar v, h)] => some (v, h)
  | _ => none

/-- Successful handler selection identifies the original singleton row.
This inversion is used by Lean's termination proof. -/
theorem destPat_eq_some {α : Type} (rows : List (FlatLang.Pat × α)) (v : MlString) (h : α)
    (found : destPat rows = some (v, h)) : rows = [(.pvar v, h)] := by
  cases rows with
  | nil => simp [destPat] at found
  | cons row rest =>
    cases row with
    | mk pat body =>
      cases rest with
      | cons first rest => simp [destPat] at found
      | nil =>
        cases pat <;> simp [destPat] at found ⊢
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨rfl, rfl⟩

/-- Translate each literal to the source's closure-language constant form. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "compile_lit_def"]
def compileLit (t : Tra) : AstHOL.Lit → ClosLang.Exp
  | .intLit i => .op t (.intOp (.const i)) []
  | .char c => .op t (.intOp (.const (Int.ofNat c.toNat))) []
  | .strLit s => .op t (.blockOp (.constant (.constStr s))) []
  | .word8 b => .op t (.intOp (.const (Int.ofNat b.toNat))) []
  | .word64 w | .float64 w => .op t (.blockOp (.constant (.constWord64 w))) []

/-- Apply a unary lowering only at its expected arity. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "arg1_def"]
def arg1 (xs : List ClosLang.Exp) (f : ClosLang.Exp → ClosLang.Exp) : ClosLang.Exp :=
  match xs with
  | [x] => f x
  | _ => .let .none xs (.var .none 0)

/-- Apply a binary lowering only at its expected arity. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "arg2_def"]
def arg2 (xs : List ClosLang.Exp) (f : ClosLang.Exp → ClosLang.Exp → ClosLang.Exp) : ClosLang.Exp :=
  match xs with
  | [x, y] => f x y
  | _ => .let .none xs (.var .none 0)

/-- Join recursive-function names using the original underscore separator. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "join_strings_def"]
def joinStrings (x y : MlString) : MlString :=
  if x.explode.isEmpty then y else MlString.concat [x, ofString "_", y]

/-- Recognize the two source conversion pairs removed before operator lowering. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "dest_nop_def"]
def destNop (op : FlatLang.Op) (es : List FlatLang.Exp) : Option FlatLang.Exp :=
  match op, es with
  | .src (.fromTo .intT (.wordT .w8)),
      [.app _ (.src (.fromTo .charT .intT)) [x]] => some x
  | .src (.fromTo .intT .charT),
      [.app _ (.src (.fromTo (.wordT .w8) .intT)) [x]] => some x
  | _, _ => none

/-- Successful conversion elimination has one of the two source shapes.
This inversion supports compiler termination and invariant proofs. -/
theorem destNop_shape (op : FlatLang.Op) (es : List FlatLang.Exp) (x : FlatLang.Exp)
    (found : destNop op es = some x) :
    (∃ trace, op = .src (.fromTo .intT (.wordT .w8)) ∧
      es = [.app trace (.src (.fromTo .charT .intT)) [x]]) ∨
    (∃ trace, op = .src (.fromTo .intT .charT) ∧
      es = [.app trace (.src (.fromTo (.wordT .w8) .intT)) [x]]) := by
  simp only [destNop] at found
  split at found <;> simp_all

/-- A successfully eliminated conversion returns a strict subexpression.
This is a Flapjack termination fact for the executable compiler. -/
theorem destNop_size (trace : Tra) (op : FlatLang.Op) (es : List FlatLang.Exp) (x : FlatLang.Exp)
    (found : destNop op es = some x) : sizeOf x < sizeOf (FlatLang.Exp.app trace op es) := by
  simp only [destNop] at found
  split at found <;> simp_all
  all_goals omega

/-- Recognize closure constants that can be folded into a constructor. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "dest_Constant_def"]
def destConstant : ClosLang.Exp → Option ClosLang.Const
  | .op _ (.blockOp (.constant c)) [] => some c
  | .op _ (.intOp (.const i)) [] => some (.constInt i)
  | .op _ (.blockOp (.cons n)) [] => some (.constCons n [])
  | _ => none

/-- Collect constants only if every expression in the list is a constant. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "dest_Constants_def"]
def destConstants : List ClosLang.Exp → Option (List ClosLang.Const)
  | [] => some []
  | e :: es => do
      let c ← destConstant e
      let cs ← destConstants es
      pure (c :: cs)

/-- Emit a constant constructor when all its arguments are constants. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "SmartCons_def"]
def smartCons (t : Tra) (tag : Nat) (xs : List ClosLang.Exp) : ClosLang.Exp :=
  if xs.isEmpty then .op t (.blockOp (.cons tag)) []
  else match destConstants xs with
    | none => .op t (.blockOp (.cons tag)) xs
    | some cs => .op t (.blockOp (.constant (.constCons tag cs.reverse))) []

end Flapjack.Compiler.Backend.FlatToClos
