import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticMustTerminateWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticMustTerminateWitnesses

/-- Original full semantic MustTerminate case, six original premises and
complete Error-exempt source-permutation existential/result/frame/locals conclusion.
The only additional premise is the legitimate smaller-body induction hypothesis,
specialized from original complete induction on prog_size. All depth-zero, body
Error/timeout and caller clock/depth restoration paths are derived. The full
evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectMustTerminate {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (body : WordLangProgHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH : ∀ (source target : WordSemStateFiniteExact width C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) body = true ∧
      ssaMapOK next ssa ∧ ltOK tables →
      ssaSimulation body source target ssa next tables)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.mustTerminate body : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.mustTerminate body : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  classical
  by_cases zero : source.termdep = 0
  · refine ⟨target.permute, ?_⟩
    simp [WordSemStateFiniteExact.evaluate, zero]
  · let innerSource := {source with clock := wordSemMustTerminateLimit width,
                                    termdep := source.termdep - 1}
    let innerTarget := {target with clock := wordSemMustTerminateLimit width,
                                    termdep := source.termdep - 1}
    have frame : Flapjack.WordAlloc.wordStateEqRel innerSource innerTarget := by
      simp_all [innerSource, innerTarget, Flapjack.WordAlloc.wordStateEqRel]
    have locals : ssaLocalsRel next ssa innerSource.locals innerTarget.locals := h.2.1
    have vars : everyVarHOL (fun x => decide (x < next)) body = true := h.2.2.2.1
    obtain ⟨permutation, simulation⟩ := bodyIH innerSource innerTarget ssa next tables
      ⟨frame, locals, h.2.2.1, vars, h.2.2.2.2⟩
    refine ⟨permutation, ?_⟩
    generalize compiledEq : ssaCcTrans body ssa next tables = compiled at simulation ⊢
    rcases compiled with ⟨output, mapOut, nextOut⟩
    have depth : target.termdep = source.termdep := by
      rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, depth, _, _, _, _⟩
      exact depth
    cases sourceEval : WordSemStateFiniteExact.evaluate body
      {innerSource with permute := permutation} with
    | mk result after =>
      by_cases error : result = some .error
      · subst result
        simp [WordSemStateFiniteExact.evaluate, zero, sourceEval, innerSource]
      · by_cases timeout : result = some .timeOut
        · subst result
          simp [WordSemStateFiniteExact.evaluate, zero, sourceEval, innerSource]
        · cases targetEval : WordSemStateFiniteExact.evaluate output innerTarget with
          | mk targetResult targetAfter =>
            dsimp only at simulation
            rw [sourceEval] at simulation
            simp only [if_neg error, targetEval] at simulation
            have eq : targetResult = result := simulation.1.symm
            subst targetResult
            have sourceOuter : WordSemStateFiniteExact.evaluate (.mustTerminate body)
                {source with permute := permutation} =
                (result, {after with clock := source.clock, termdep := source.termdep}) := by
              simp only [WordSemStateFiniteExact.evaluate, zero]
              rw [sourceEval]
              cases result with
              | none => rfl
              | some result => cases result <;> simp_all
            have targetInner : WordSemStateFiniteExact.evaluate output
                {target with clock := wordSemMustTerminateLimit width, termdep := target.termdep - 1} = (result, targetAfter) := by
              simpa only [innerTarget, depth] using targetEval
            have targetOuter : WordSemStateFiniteExact.evaluate (.mustTerminate output) target =
                (result, {targetAfter with clock := target.clock, termdep := target.termdep}) := by
              have targetNonzero : target.termdep ≠ 0 := by simpa only [depth] using zero
              simp only [WordSemStateFiniteExact.evaluate, targetNonzero]
              rw [targetInner]
              cases result with
              | none => rfl
              | some result => cases result <;> simp_all
            have compileOuter : ssaCcTrans (.mustTerminate body) ssa next tables =
                (.mustTerminate output, mapOut, nextOut) := by
              rw [ssaCcTrans, compiledEq]
            dsimp only
            rw [sourceOuter]
            simp only [if_neg error, compileOuter, targetOuter]
            refine ⟨True.intro, ?_, simulation.2.2⟩
            simp_all [Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
