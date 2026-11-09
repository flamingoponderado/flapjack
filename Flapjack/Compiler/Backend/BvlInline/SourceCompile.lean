module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramProduction
public import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpProduction
public import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
public import Flapjack.Compiler.Backend.BvlHandle.SourceCompile
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Source-shaped composition of the BVL inlining and handler passes. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

/-- Optimize one named function after inlining. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "optimise_def"]
def optimise {α : Type} (splitSeq : Bool) (cutSize : Nat) (entry : α × Nat × Bvl.Exp) : α × Nat × Bvl.Exp :=
  let (name, arity, body) := entry
  (name, arity, BvlHandle.compileAny splitSeq cutSize arity (letOpSing (removeTicksSing body)))

/-- The source head is applied to a singleton, so its unspecified empty-list
case cannot occur. -/
theorem optimise_source_head {α : Type} (splitSeq : Bool) (cutSize : Nat)
    (name : α) (arity : Nat) (body : Bvl.Exp) :
    optimise splitSeq cutSize (name, arity, body) =
      (name, arity, BvlHandle.compileAny splitSeq cutSize arity
        (letOpSing (@Flapjack.holHd Bvl.Exp ⟨.var 0⟩ (removeTicks [body])))) := by
  rw [removeTicksSing_equivalence.1]
  rfl

/-- The original optimized singleton equation. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "optimise_eq"]
theorem optimise_eq {α : Type} (splitSeq : Bool) (cutSize : Nat)
    (name : α) (arity : Nat) (body : Bvl.Exp) :
    optimise splitSeq cutSize (name, arity, body) =
      (name, arity, BvlHandle.compileAny splitSeq cutSize arity
        (letOpSing (removeTicksSing body))) := rfl

/-- Incrementally optimize a program starting with an existing inline cache. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "compile_inc_def"]
def compileInc (limit : Nat) (splitSeq : Bool) (cutSize : Nat) (cache : Spt (Nat × Bvl.Exp))
    (program : List (Nat × Nat × Bvl.Exp)) : Spt (Nat × Bvl.Exp) × List (Nat × Nat × Bvl.Exp) :=
  let (cache, program) := tickCompileProg limit cache program
  (cache, program.map (optimise splitSeq cutSize))

/-- Optimize a program from an empty inline cache. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "compile_prog_def"]
def compileProg (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) : Spt (Nat × Bvl.Exp) × List (Nat × Nat × Bvl.Exp) :=
  compileInc limit splitSeq cutSize .ln program

/-- The executed incremental compiler returns the total source composition for
all inputs and fuel. This correspondence is Flapjack infrastructure. -/
theorem compileIncFuel_eq_compileInc (fuel limit cutSize : Nat) (splitSeq : Bool)
    (cache : Spt (Nat × Bvl.Exp)) (program : List (Nat × Nat × Bvl.Exp)) :
    compileIncFuel fuel limit cutSize splitSeq cache program =
      some (compileInc limit splitSeq cutSize cache program) := by
  have mapped (xs : List (Nat × Nat × Bvl.Exp)) :
      xs.mapM (fun entry => do
        let body ← removeTicksBounded fuel entry.2.2
        let body ← letOpBounded fuel body
        pure (entry.1, entry.2.1, ← BvlHandle.compileAnyFuel fuel splitSeq cutSize entry.2.1 body)) =
      some (xs.map (optimise splitSeq cutSize)) := by
    induction xs with
    | nil => rfl
    | cons entry rest ih =>
      obtain ⟨name, arity, body⟩ := entry
      simp only [List.mapM_cons, List.map_cons]
      rw [ih]
      simp [removeTicksBounded_eq, letOpBounded_eq,
        BvlHandle.compileAnyFuel_eq_compileAny, letOpSing, letOp, letOpList, optimise]
  unfold compileIncFuel compileInc
  rw [tickInlineAllFuel_eq]
  simp only [bind, Option.bind]
  generalize tickCompileProg limit cache program = result
  obtain ⟨cache, program⟩ := result
  change (do
    let output ← program.mapM (fun entry => do
      let body ← removeTicksBounded fuel entry.2.2
      let body ← letOpBounded fuel body
      pure (entry.1, entry.2.1, ← BvlHandle.compileAnyFuel fuel splitSeq cutSize entry.2.1 body))
    pure (cache, output)) = some (cache, program.map (optimise splitSeq cutSize))
  rw [mapped]
  rfl

/-- The whole-program executable is the source compiler with an empty cache. -/
theorem compileProgFuel_eq_compileProg (fuel limit cutSize : Nat) (splitSeq : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) :
    compileProgFuel fuel limit cutSize splitSeq program =
      some (compileProg limit splitSeq cutSize program) := by
  exact compileIncFuel_eq_compileInc fuel limit cutSize splitSeq .ln program

end Flapjack.Compiler.Backend.BvlInline
