import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineSemantics
import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramProduction
import Flapjack.Compiler.Backend.BvlInline.RemoveTicks

/-! Whole-program behavior of the executed inlining and tick-removal stages. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- A successful production tick-removal traversal returns the source-shaped
transformation on every program body. -/
theorem removeTicks_programFuel_eq (fuel : Nat) (program output : List (Nat × Nat × Bvl.Exp))
    (run : program.mapM (fun entry => do
      pure (entry.1, entry.2.1, ← BvlInline.removeTicksFuel fuel entry.2.2)) = some output) :
    output = program.map (fun (n, arity, body) => (n, arity, removeTicksSing body)) := by
  induction program generalizing output with
  | nil => simpa using run.symm
  | cons entry rest ih =>
    obtain ⟨n, arity, body⟩ := entry
    simp only [List.mapM_cons] at run
    cases first : BvlInline.removeTicksFuel fuel body with
    | none => simp [first] at run
    | some transformed =>
      cases restRun : rest.mapM (fun entry => do
          pure (entry.1, entry.2.1, ← BvlInline.removeTicksFuel fuel entry.2.2)) with
      | none =>
        simp only [bind, pure] at restRun
        simp [first, restRun] at run
      | some remaining =>
        have bodyEq := BvlInline.removeTicksFuel_eq fuel body transformed first
        have restEq := ih remaining restRun
        simp only [bind, pure] at restRun
        simp [first, restRun] at run
        subst output
        simp [bodyEq, restEq]

/-- The production inliner and tick-removal traversal preserve the behavior of
a non-failing initial BVL program. This is Flapjack infrastructure pending
source review of the whole-program semantic representations. -/
theorem inline_removeTicks_production_semantics {C F : Type} (fuel limit start : Nat)
    (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (compiler : Compiler C)
    (cache : Spt (Nat × Bvl.Exp)) (inlined output : List (Nat × Nat × Bvl.Exp))
    (inlineRun : tickInlineAllFuel fuel limit .ln program = some (cache, inlined))
    (removeRun : inlined.mapM (fun entry => do
      pure (entry.1, entry.2.1, ← BvlInline.removeTicksFuel fuel entry.2.2)) = some output)
    (cacheEq : (oracle 0).1.1 = cache)
    (distinct : (program.map Prod.fst).Nodup)
    (nonFail : BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc limit (removeTicksCc compiler)) start ≠ .fail) :
    BvlSem.semantics ffi (sptFromAList output)
      (removeTicksCo ∘ inCo limit oracle) compiler start =
    BvlSem.semantics ffi (sptFromAList program) oracle
      (inCc limit (removeTicksCc compiler)) start := by
  rw [tickInlineAllFuel_eq] at inlineRun
  have pairEq : (cache, inlined) = tickCompileProg limit .ln program := (Option.some.inj inlineRun).symm
  have cacheRun : cache = (tickCompileProg limit .ln program).1 := congrArg Prod.fst pairEq
  have inlineProgram : inlined = (tickCompileProg limit .ln program).2 := congrArg Prod.snd pairEq
  have outputEq := removeTicks_programFuel_eq fuel inlined output removeRun
  have treeEq : sptFromAList output =
      sptMap (fun (arity, body) => (arity, removeTicksSing body)) (sptFromAList inlined) := by
    rw [outputEq, sptMap_sptFromAList]
  rw [treeEq]
  rw [removeTicks_semantics, inlineProgram]
  apply inline_semantics ffi program oracle (removeTicksCc compiler) start limit
  · exact cacheEq.trans cacheRun
  · exact distinct
  · exact nonFail

end Flapjack.Compiler.Backend.BvlInline.Proofs
