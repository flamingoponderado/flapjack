import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticInstDivWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstDivWitnesses

/-- Full native Div opcode case of the original SSA simulation. All six
original premises and the complete Error-exempt source-permutation conclusion
are retained. Actual source getVars reads divisor then dividend; missing and
non-word reads and zero divisors retain the source Error exemption. Successful
target reads and fresh destination relation follow from the original locals
helpers, without target-evaluation or successful-source premises.
The native Inst/evaluator boundary inherits reals_as_rational_cuts
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstDiv {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst left right : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.inst (.arith (.div dst left right))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.div dst left right))) source target ssa next tables := by
  have bound : dst < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact of_decide_eq_true occurrences.1.1
  let permuted := {source with permute := target.permute}
  refine ⟨target.permute, ?_⟩
  cases reads : WordSemStateFiniteExact.getVars [right, left] permuted with
  | none =>
    have absent : WordSemStateFiniteExact.getVars [right, left]
        {source with permute := target.permute} = none := reads
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, absent]
  | some values =>
    have transferred := ssaLocalsRelGetVars [right, left] values next ssa permuted target ⟨h.2.1, reads⟩
    have length := Flapjack.WordAlloc.getVarsLength [right, left] permuted values reads
    cases values with
    | nil => simp at length
    | cons q rest =>
      cases rest with
      | nil => simp at length
      | cons w rest =>
        cases rest with
        | cons x xs => simp at length
        | nil =>
          cases q with
          | loc label offset =>
            simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
          | word divisor =>
            cases w with
            | loc label offset =>
              simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
            | word dividend =>
              by_cases zero : divisor = 0
              · simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
              · have locals := ssaLocalsRelSetVar next ssa source.locals target.locals dst
                  (.word (dividend.sdiv divisor)) ⟨h.2.1, h.2.2.2.2.1, bound⟩
                simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                  WordSemStateFiniteExact.setVar, ssaCcTrans, ssaCcTransInst,
                  nextVarRename, Flapjack.WordAlloc.wordStateEqRel, permuted]

end Flapjack.Compiler.Backend.WordAlloc
