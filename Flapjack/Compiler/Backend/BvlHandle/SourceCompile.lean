module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.ConstantComposition
public import Flapjack.Compiler.Backend.BvlConst.SourceCompile
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Total source entry points for BVL handler lowering. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl DbVars
instance sourceCompileInst1 : Nonempty Exp := ⟨.var 0⟩

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

/-- The source compiler preserves the number of expressions. -/
@[hol "cakeml/compiler/backend/bvl_handleScript.sml" "compile_length"]
theorem compileList_length (limit env : Nat) (expressions : List Exp) :
    (compile limit env expressions).1.length = expressions.length := by
  induction expressions with
  | nil => simp [compile, compileList]
  | cons head tail ih =>
    cases headRun : compileSing limit env head with
    | mk headExp headData =>
      obtain ⟨headLive, headSize, headFlag⟩ := headData
      cases tailRun : compileList limit env tail with
      | mk tailExp tailData =>
        obtain ⟨tailLive, tailSize, tailFlag⟩ := tailData
        simp [compile, compileList, headRun, tailRun] at ih ⊢
        exact ih

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

open Classical in
/-- Constructor clauses of the original handler-lowering list recursion.
This is comparison evidence for `compile_def`, not a separate HOL theorem. -/
theorem compile_singleton_equations (limit env : Nat) :
    (∀ v, compile limit env [.var v] =
      if v < env then ([.var v], .var v, 1, true) else ([zero], .empty, 1, true)) ∧
    (∀ x y z, compile limit env [.ifThenElse x y z] =
      (let (x, lx, sx, nx) := compile limit env [x]
       let (y, ly, sy, ny) := compile limit env [y]
       let (z, lz, sz, nz) := compile limit env [z]
       optionalLetLet (.ifThenElse (Flapjack.holHd x) (Flapjack.holHd y) (Flapjack.holHd z))
         env (mkUnion lx (mkUnion ly lz)) (sx + sy + sz + 1) limit (nx && ny && nz))) ∧
    (∀ xs body, compile limit env [.let xs body] =
      if xs.isEmpty then compile limit env [body] else
        let (ys, lx, sx, nx) := compile limit env xs
        let (body, ly, sy, ny) := compile limit (env + xs.length) [body]
        optionalLetLet (.let ys (Flapjack.holHd body)) env (mkUnion lx (.shift xs.length ly))
          (sx + sy + 1) limit (nx && ny)) ∧
    (∀ x y, compile limit env [.handle x y] =
      (let (x, lx, sx, nx) := compile limit env [x]
       if nx then (x, lx, sx, true) else
         let (y, ly, sy, ny) := compile limit (env + 1) [y]
         ([.handle (letLet env (dbToSet lx) (Flapjack.holHd x)) (Flapjack.holHd y)],
           mkUnion lx (.shift 1 ly), sy, ny))) ∧
    (∀ x, compile limit env [.raise x] =
      (let (x, live, size, _) := compile limit env [x]
       optionalLetLet (.raise (Flapjack.holHd x)) env live (size + 1) limit false)) ∧
    (∀ op xs, compile limit env [.op op xs] =
      (let (ys, live, size, nr) := compile limit env xs
       if op = .thunkOp .forceThunk then ([.op op ys], live, size + 1, false)
       else optionalLetLet (.op op ys) env live (size + 1) limit nr)) ∧
    (∀ x, compile limit env [.tick x] =
      (let (x, live, size, nr) := compile limit env [x]
       ([.tick (Flapjack.holHd x)], live, size, nr))) ∧
    (∀ m v, compile limit env [.force m v] =
      if v < env then ([.force m v], .var v, 1, false) else ([zero], .empty, 1, true)) ∧
    (∀ ticks dest xs, compile limit env [.call ticks dest xs] =
      (let (ys, live, size, _) := compile limit env xs
       optionalLetLet (.call ticks dest ys) env live (size + 1) limit false)) := by
  classical
  repeat' constructor
  all_goals intros
  all_goals simp only [compileSing_eq.1, compileSing, Flapjack.holHd,
    optionalLetLetSing_eq, zero]
  all_goals try (split <;> rfl)
  rename_i op xs
  cases op <;> simp_all
  rename_i thunk
  cases thunk <;> simp_all

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
