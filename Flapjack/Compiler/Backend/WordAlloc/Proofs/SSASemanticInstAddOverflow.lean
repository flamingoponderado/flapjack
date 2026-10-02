import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend

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

namespace SemanticInstAddOverflowWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstAddOverflowWitnesses

/-- Full original native AddOverflow opcode simulation with all six
premises and the complete Error-exempt source-permutation conclusion. Original
operand reads transport to the native instruction; the result and physical-0
signed-overflow flag are evaluated before the fresh-flag output Move. Original
fresh-write/map-extension/physical-write relations establish both destinations,
including aliases. The wrapped signed sum comparison is unchanged. Missing and
non-word reads retain the source Error exemption, without target-run, success
or post-state premises. The Inst/evaluator boundary inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstAddOverflow {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next result left right flag : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.inst (.arith (.addOverflow result left right flag))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.addOverflow result left right flag))) source target ssa next tables := by
  have bounds : result < next ∧ flag < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact ⟨of_decide_eq_true occurrences.1.1.1, of_decide_eq_true occurrences.2⟩
  let permuted := {source with permute := target.permute}
  refine ⟨target.permute, ?_⟩
  cases reads : WordSemStateFiniteExact.getVars [left, right] permuted with
  | none =>
    have absent : WordSemStateFiniteExact.getVars [left, right]
        {source with permute := target.permute} = none := reads
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, absent]
  | some values =>
    have transferred := ssaLocalsRelGetVars [left, right] values next ssa permuted target ⟨h.2.1, reads⟩
    have length := Flapjack.WordAlloc.getVarsLength [left, right] permuted values reads
    cases values with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons b rest =>
        cases rest with
        | cons x xs => simp at length
        | nil =>
          cases a with
          | loc l o => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
          | word aw =>
            cases b with
            | loc l o => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
            | word bw =>
              let resultWord := aw + bw
              let flagWord : BitVec width := if (aw + bw).toInt ≠ aw.toInt + bw.toInt then 1 else 0
              let sourceResult := WordSemStateFiniteExact.setVar result (.word resultWord) permuted
              let targetResult := WordSemStateFiniteExact.setVar next (.word resultWord) target
              let added := WordSemStateFiniteExact.setVar 0 (.word flagWord) targetResult
              have instRun : WordSemStateFiniteExact.evaluate
                  (.inst (.arith (.addOverflow next (optionLookup ssa left) (optionLookup ssa right) 0))) target =
                  (none, added) := by
                have renamedReads : WordSemStateFiniteExact.getVars [optionLookup ssa left, optionLookup ssa right] target =
                    some [.word aw, .word bw] := by simpa using transferred
                simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, renamedReads]
                rfl
              have notPhysical : ¬ isPhyVar next := by
                have allocated := h.2.2.1
                simp [isAllocVar, isPhyVar] at allocated ⊢
                omega
              have extended := ssaMapOKExtend next ssa result ⟨h.2.2.2.2.1, notPhysical⟩
              have resultLocals := ssaLocalsRelSetVar next ssa source.locals target.locals result (.word resultWord)
                  ⟨h.2.1, h.2.2.2.2.1, bounds.1⟩
              have addedLocals := ssaLocalsRelIgnoreSetVar (next + 4) (sptInsert result next ssa)
                  sourceResult targetResult 0 (.word flagWord) ⟨extended, resultLocals, by decide⟩
              have finalLocals := ssaLocalsRelSetVar (next + 4) (sptInsert result next ssa)
                  sourceResult.locals added.locals flag (.word flagWord) ⟨addedLocals, extended, by omega⟩
              have sourceRun : WordSemStateFiniteExact.evaluate
                  (.inst (.arith (.addOverflow result left right flag)))
                  {source with permute := target.permute} =
                  (none, WordSemStateFiniteExact.setVar flag (.word flagWord) sourceResult) := by
                change WordSemStateFiniteExact.evaluate
                  (.inst (.arith (.addOverflow result left right flag))) permuted = _
                simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, reads]
                rfl
              dsimp only
              simp only [ssaCcTrans, ssaCcTransInst, nextVarRename, evaluateSeqNative, instRun, sourceRun]
              simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
                LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same,
                Flapjack.WordAlloc.wordStateEqRel, sourceResult, targetResult,
                added, resultWord, flagWord, permuted]

end Flapjack.Compiler.Backend.WordAlloc
