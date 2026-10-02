import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticBufferWriteWitnesses

/-- Canonical roundtrip of the imported native state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticBufferWriteWitnesses

/-- Full original native CodeBufferWrite SSA simulation. All six original premises
and complete Error-exempt permutation/result/frame/locals conclusion retained.
No target execution or successful buffer write is assumed. Inherits
reals_as_rational_cuts evaluator boundary (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next first second : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.codeBufferWrite first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.codeBufferWrite first second) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  have related : ssaLocalsRel next ssa permuted.locals target.locals := h.2.1
  refine ⟨target.permute, ?_⟩
  cases firstRead : WordSemStateFiniteExact.getVar first permuted with
  | none => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead]
  | some firstValue =>
    cases firstValue with
    | loc p q => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead]
    | word firstWord =>
      cases secondRead : WordSemStateFiniteExact.getVar second permuted with
      | none => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead, secondRead]
      | some secondValue =>
        cases secondValue with
        | loc p q => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead, secondRead]
        | word secondWord =>
          have targetFirst := ssaLocalsRelGetVar next ssa permuted target first (.word firstWord)
            ⟨related, firstRead⟩
          have targetSecond := ssaLocalsRelGetVar next ssa permuted target second (.word secondWord)
            ⟨related, secondRead⟩
          have sameBuffer : target.codeBuffer = permuted.codeBuffer := by
            simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          cases written : wordSemBufferWrite permuted.codeBuffer firstWord (secondWord.setWidth 8) with
          | none => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead, secondRead, written]
          | some buffer =>
            simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans,
              Flapjack.WordAlloc.wordStateEqRel, permuted]

/-- Full original native DataBufferWrite SSA simulation. All six original premises
and complete Error-exempt permutation/result/frame/locals conclusion retained.
No target execution or successful buffer write is assumed. Inherits
reals_as_rational_cuts evaluator boundary (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next first second : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next)) (.dataBufferWrite first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.dataBufferWrite first second) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  have related : ssaLocalsRel next ssa permuted.locals target.locals := h.2.1
  refine ⟨target.permute, ?_⟩
  cases firstRead : WordSemStateFiniteExact.getVar first permuted with
  | none => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead]
  | some firstValue =>
    cases firstValue with
    | loc p q => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead]
    | word firstWord =>
      cases secondRead : WordSemStateFiniteExact.getVar second permuted with
      | none => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead, secondRead]
      | some secondValue =>
        cases secondValue with
        | loc p q => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead, secondRead]
        | word secondWord =>
          have targetFirst := ssaLocalsRelGetVar next ssa permuted target first (.word firstWord)
            ⟨related, firstRead⟩
          have targetSecond := ssaLocalsRelGetVar next ssa permuted target second (.word secondWord)
            ⟨related, secondRead⟩
          have sameBuffer : target.dataBuffer = permuted.dataBuffer := by
            simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          cases written : wordSemBufferWrite permuted.dataBuffer firstWord secondWord with
          | none => simp [WordSemStateFiniteExact.evaluate, permuted, firstRead, secondRead, written]
          | some buffer =>
            simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans,
              Flapjack.WordAlloc.wordStateEqRel, permuted]

end Flapjack.Compiler.Backend.WordAlloc
