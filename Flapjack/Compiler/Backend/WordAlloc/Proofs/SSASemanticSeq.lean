import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds
import Flapjack.Pancake.WordConvs.ProgramMonotonicity
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof factoring of the native Seq clause after the original
fix_clock_evaluate theorem discharges clock normalization. This has no
independent HOL declaration; the full semantic Seq case uses this equation
without assuming a target execution or successful first result. -/
private theorem evaluateSeqNative {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq first second) state =
      match WordSemStateFiniteExact.evaluate first state with
      | (none, after) => WordSemStateFiniteExact.evaluate second after
      | (some result, after) => (some result, after) := by
  simp only [WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.fix_clock_evaluate]
  cases WordSemStateFiniteExact.evaluate first state with
  | mk result after => cases result <;> rfl

namespace SemanticSeqWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticSeqWitnesses

/-- Full original semantic Seq case, all six original premises and complete
Error-exempt source-permutation existential/result/frame/result-sensitive locals
conclusion. Only the legitimate smaller-first/second-body IHs are additional.
Second-context allocation/map/occurrence bounds are derived from the native
compiler invariant. The actual scheduler-swap theorem composes the source runs;
no desired target run or post-state relation is assumed. The full evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8). Canonical holEl/holHd are
inherited through the reviewed full compiler invariant and native scheduler-swap
proof; the original Seq9228-9263 requires no new selector bounds or concrete
out-of-range default. The native total opaque selectors and original helper
side conditions remain intact; first-run NONE discharges the scheduler-swap
non-Error guard, not an added premise. Final assembly must discharge both IHs. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstIH : ∀ (source target : WordSemStateFiniteExact width C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation first source target ssa next tables)
    (secondIH : ∀ (source target : WordSemStateFiniteExact width C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation second source target ssa next tables)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.seq first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.seq first second) source target ssa next tables := by
  classical
  have vars : everyVarHOL (fun x => decide (x < next)) first = true ∧
      everyVarHOL (fun x => decide (x < next)) second = true := by
    simpa only [everyVarHOL, Bool.and_eq_true] using h.2.2.2.1
  obtain ⟨permutation, firstSim⟩ := firstIH source target ssa next tables
    ⟨h.1, h.2.1, h.2.2.1, vars.1, h.2.2.2.2⟩
  rcases firstCompiled : ssaCcTrans first ssa next tables with ⟨firstOut, mapFirst, nextFirst⟩
  rcases secondCompiled : ssaCcTrans second mapFirst nextFirst tables with ⟨secondOut, mapSecond, nextSecond⟩
  have compiled : ssaCcTrans (.seq first second) ssa next tables =
      (.seq firstOut secondOut, mapSecond, nextSecond) := by
    simp only [ssaCcTrans, firstCompiled, secondCompiled]
  cases sourceEval : WordSemStateFiniteExact.evaluate first {source with permute := permutation} with
  | mk firstResult sourceAfter =>
    cases firstResult with
    | some result =>
      refine ⟨permutation, ?_⟩
      by_cases error : result = .error
      · subst result
        simp only [evaluateSeqNative, sourceEval, ↓reduceIte]
      · cases targetEval : WordSemStateFiniteExact.evaluate firstOut target with
        | mk targetResult targetAfter =>
          dsimp only at firstSim
          rw [sourceEval] at firstSim
          have noError : (some result : Option (WordSemResult width)) ≠ some .error := by simpa using error
          simp only [if_neg noError, firstCompiled, targetEval] at firstSim
          have eq : targetResult = some result := firstSim.1.symm
          subst targetResult
          dsimp only
          rw [evaluateSeqNative, sourceEval]
          simp only [if_neg noError, compiled, evaluateSeqNative, targetEval]
          cases result <;> simpa only using firstSim
    | none =>
      cases targetEval : WordSemStateFiniteExact.evaluate firstOut target with
      | mk targetResult targetAfter =>
        dsimp only at firstSim
        rw [sourceEval] at firstSim
        simp only [reduceCtorEq, ↓reduceIte, firstCompiled, targetEval] at firstSim
        have resultEq : targetResult = none := firstSim.1.symm
        subst targetResult
        have firstInvariant := ssaCcTransProps first ssa next tables firstOut mapFirst nextFirst
          firstCompiled ⟨h.2.2.2.2.1, h.2.2.1⟩
        have secondVars : everyVarHOL (fun x => decide (x < nextFirst)) second = true := by
          apply Flapjack.everyVarMono _ second _
          refine ⟨?_, vars.2⟩
          intro x bound
          have : x < next := of_decide_eq_true bound
          exact decide_eq_true (Nat.lt_of_lt_of_le this firstInvariant.1)
        obtain ⟨secondPermutation, secondSim⟩ := secondIH sourceAfter targetAfter mapFirst nextFirst tables
          ⟨firstSim.2.1, firstSim.2.2, firstInvariant.2.1, secondVars,
            firstInvariant.2.2, h.2.2.2.2.2⟩
        obtain ⟨combinedPermutation, swapped⟩ := WordSemStateFiniteExact.permute_swap_lemma first
          {source with permute := permutation} secondPermutation (by simp only [sourceEval]; simp)
        refine ⟨combinedPermutation, ?_⟩
        simp only [sourceEval] at swapped
        have firstRun : WordSemStateFiniteExact.evaluate first {source with permute := combinedPermutation} =
            (none, {sourceAfter with permute := secondPermutation}) := swapped
        have sourceSeq : WordSemStateFiniteExact.evaluate (.seq first second)
            {source with permute := combinedPermutation} =
            WordSemStateFiniteExact.evaluate second {sourceAfter with permute := secondPermutation} := by
          rw [evaluateSeqNative, firstRun]
        have targetSeq : WordSemStateFiniteExact.evaluate (.seq firstOut secondOut) target =
            WordSemStateFiniteExact.evaluate secondOut targetAfter := by
          rw [evaluateSeqNative, targetEval]
        dsimp only at secondSim ⊢
        rw [sourceSeq]
        simp only [compiled, targetSeq]
        simpa only [secondCompiled] using secondSim

end Flapjack.Compiler.Backend.WordAlloc
