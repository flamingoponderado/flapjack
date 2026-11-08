import Flapjack.Compiler.Backend.BvlHandle.Proofs.ConstantComposition
import Flapjack.Compiler.Backend.BvlConst.SourceCompile

/-! Total source entry points for BVL handler lowering. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl DbVars

/-- HOL's list traversal, using its equivalent singleton-list formulation. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_def"]
abbrev compile : Nat → Nat → List Exp → List Exp × DbVarSet × Nat × Bool := compileList

/-- The original list traversal agrees with its singleton formulation. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_sing_eq"]
theorem compileSing_eq :
    (∀ e limit env, compile limit env [e] =
      (let (out, vars, size, nr) := compileSing limit env e; ([out], vars, size, nr))) ∧
    (∀ es limit env, compile limit env es = compileList limit env es) := by
  constructor
  · intro e limit env
    cases run : compileSing limit env e with
    | mk out rest =>
      obtain ⟨vars, size, nr⟩ := rest
      cases vars <;> simp [compile, compileList, run, mkUnion]
  · intro es limit env
    rfl

/-- Check the empty and multi-element clauses of the original list traversal. -/
theorem compile_list_equations (limit env : Nat) (x y : Exp) (xs : List Exp) :
    compile limit env [] = ([], .empty, 0, true) ∧
      compile limit env (x :: y :: xs) =
        (let (dx, lx, s1, nr1) := compile limit env [x]
         let (dy, ly, s2, nr2) := compile limit env (y :: xs)
         (dx ++ dy, mkUnion lx ly, s1 + s2, nr1 && nr2)) := by
  constructor
  · simp [compile, compileList]
  · cases first : compileSing limit env x with
    | mk out rest =>
      obtain ⟨vars, size, nr⟩ := rest
      cases vars <;> simp [compile, compileList, first, mkUnion]

/-- Compile one expression after constant propagation and handler simplification. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_exp_def"]
abbrev compileExp : Nat → Nat → Exp → Exp := compileExpression

/-- The expression entry point uses the singleton traversal. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_exp_eq"]
theorem compileExp_eq (limit arity : Nat) (e : Exp) :
    compileExp limit arity e = (compileSing limit arity (handleSimp (BvlConst.compileExp e))).1 := by
  simp [compileExp, compileExpression, BvlConst.compileExp_eq]

/-- The list used by HOL's `HD` in `compile_exp_def` is exactly this singleton,
so the source head operation never encounters its empty-list case. -/
theorem compileExp_list_head (limit arity : Nat) (e : Exp) :
    (compile limit arity [handleSimp (BvlConst.compileExp e)]).1 = [compileExp limit arity e] := by
  have eq := (compileSing_eq.1 (handleSimp (BvlConst.compileExp e)) limit arity)
  simpa [compileExp_eq] using congrArg Prod.fst eq

/-- Recursively split source sequences and compile their individual expressions. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_seqs_def"]
def compileSeqs (limit : Nat) (e : Exp) (acc : Option Exp) : Exp :=
  compileSeqsWith (fun limit e => compileExp limit 0 e) limit e acc

/-- Apply sequence splitting only for zero-arity programs when requested. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_any_def"]
def compileAny (splitSeq : Bool) (limit arity : Nat) (e : Exp) : Exp :=
  if arity == 0 && splitSeq then compileSeqs limit e none else compileExp limit arity e

/-- The bounded executable handler pipeline returns the total source result. -/
theorem compileAnyFuel_eq_compileAny (fuel : Nat) (splitSeq : Bool) (limit arity : Nat) (e : Exp) :
    compileAnyFuel fuel splitSeq limit arity e = some (compileAny splitSeq limit arity e) := by
  simpa [compileAny, compileSeqs, compileExp] using compileAnyFuel_eq_source fuel splitSeq limit arity e

end Flapjack.Compiler.Backend.BvlHandle
