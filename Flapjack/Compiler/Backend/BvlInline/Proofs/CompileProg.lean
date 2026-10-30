import Flapjack.Compiler.Backend.BvlInline.Proofs.RemoveTicksSimulation

/-! Initial-state consequence of the BVL tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

namespace CompileCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end CompileCarrier

/-- Adapt a compiler callback by removing ticks from its input program. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "remove_ticks_cc_def"]
def removeTicksCc {A B C D : Type} (compiler : A → List (B × C × Bvl.Exp) → D) :
    A → List (B × C × Bvl.Exp) → D :=
  fun config program => compiler config (program.map fun (name, arity, body) => (name, arity, removeTicksSing body))

/-- Remove ticks from the program in one compiler-oracle entry. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "remove_ticks_co_def"]
def removeTicksCo {A B C : Type} (entry : A × List (B × C × Bvl.Exp)) : A × List (B × C × Bvl.Exp) :=
  (entry.1, entry.2.map fun (name, arity, body) => (name, arity, removeTicksSing body))

/-- An optimized initial evaluation is reproduced by the original program
with more clock and the same final FFI state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_compile_prog"
  (fmap_as_finite_support := [refs])]
theorem evaluateCompileProg {C F : Type} (ffi : HolFfiState F) (program : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C) (clock start : Nat)
    (result : Result (List BvlSem.Value) BvlSem.Value) (final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (run : evaluateTuple ([.call 0 (some start) []], [],
      initialState ffi (sptMap (fun (arity, body) => (arity, removeTicksSing body)) program)
        (removeTicksCo ∘ oracle) compiler clock) = (result, final)) :
    ∃ extra, ∃ sourceFinal : Flapjack.Compiler.Backend.BvlSem.State C F,
      evaluateTuple ([.call 0 (some start) []], [],
        initialState ffi program oracle (removeTicksCc compiler) (clock + extra)) = (result, sourceFinal) ∧
      sourceFinal.ffi = final.ffi := by
  let source := initialState ffi program oracle (removeTicksCc compiler) clock
  let optimized := initialState ffi (sptMap (fun (arity, body) => (arity, removeTicksSing body)) program)
    (removeTicksCo ∘ oracle) compiler clock
  have related : stateRel source optimized := by
    constructor <;> rfl
  have optimizedRun : evaluateTuple (removeTicks [.call 0 (some start) []], [], optimized) = (result, final) := by
    simpa [optimized, removeTicks, removeTicksList, removeTicksSing] using run
  obtain ⟨extra, sourceFinal, sourceRun, finalRel⟩ :=
    evaluateRemoveTicks clock [.call 0 (some start) []] [] optimized source result final ⟨related, rfl, optimizedRun⟩
  refine ⟨extra, sourceFinal, ?_, ?_⟩
  · simpa [source, initialState] using sourceRun
  · exact (stateRel_fields sourceFinal final finalRel).2.2.2.symm

end Flapjack.Compiler.Backend.BvlInline.Proofs
