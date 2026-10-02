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

namespace SemanticInstLongDivWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstLongDivWitnesses

/-- Full original native LongDiv opcode simulation with all six premises
and complete Error-exempt source-permutation conclusion. The physical input
Move6/0 preserves the mapped divisor by the original SSA locals relation.
Actual LongDiv0/6/6/0 and fresh-output Move are evaluated; the two fresh
relations and distinct-key insertion swap establish remainder then quotient,
including aliased source destinations. Missing/non-word reads, zero divisor
and quotient overflow retain the original Error exemption. No target-run,
source-success or post-state premise is added. The Inst/evaluator boundary
inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstLongDiv {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next quotient remainder high low divisor : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.inst (.arith (.longDiv quotient remainder high low divisor))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.longDiv quotient remainder high low divisor))) source target ssa next tables := by
  have bounds : quotient < next ∧ remainder < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact ⟨of_decide_eq_true occurrences.1.1.1.1, of_decide_eq_true occurrences.1.1.1.2⟩
  let permuted := {source with permute := target.permute}
  refine ⟨target.permute, ?_⟩
  cases reads : WordSemStateFiniteExact.getVars [high, low, divisor] permuted with
  | none =>
    have absent : WordSemStateFiniteExact.getVars [high, low, divisor]
        {source with permute := target.permute} = none := reads
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, absent]
  | some values =>
    have length := Flapjack.WordAlloc.getVarsLength [high, low, divisor] permuted values reads
    cases values with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons b rest =>
        cases rest with
        | nil => simp at length
        | cons c rest =>
          cases rest with
          | cons x xs => simp at length
          | nil =>
            cases a with
            | loc l o => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
            | word aw =>
              cases b with
              | loc l o => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
              | word bw =>
                cases c with
                | loc l o => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
                | word cw =>
                  have sourceReads :
                      WordSemStateFiniteExact.getVar high permuted = some (.word aw) ∧
                      WordSemStateFiniteExact.getVar low permuted = some (.word bw) ∧
                      WordSemStateFiniteExact.getVar divisor permuted = some (.word cw) := by
                    cases hh : WordSemStateFiniteExact.getVar high permuted <;>
                      cases hl : WordSemStateFiniteExact.getVar low permuted <;>
                      cases hd : WordSemStateFiniteExact.getVar divisor permuted <;>
                      simp_all [WordSemStateFiniteExact.getVars]
                  obtain ⟨sourceHigh, sourceLow, sourceDivisor⟩ := sourceReads
                  have sourceInputs : WordSemStateFiniteExact.getVars [high, low] permuted = some [.word aw, .word bw] := by
                    simp [WordSemStateFiniteExact.getVars, sourceHigh, sourceLow]
                  have renamedInputs := ssaLocalsRelGetVars [high, low] [.word aw, .word bw] next ssa permuted target ⟨h.2.1, sourceInputs⟩
                  let incoming := WordSemStateFiniteExact.setVars [6, 0] [.word aw, .word bw] target
                  have moveRun : WordSemStateFiniteExact.evaluate
                      (.move 1 [(6, optionLookup ssa high), (0, optionLookup ssa low)]) target = (none, incoming) := by
                    have renamedReads : WordSemStateFiniteExact.getVars [optionLookup ssa high, optionLookup ssa low] target = some [.word aw, .word bw] := by simpa using renamedInputs
                    simp [WordSemStateFiniteExact.evaluate, incoming, renamedReads]
                  have incomingLocals := ssaLocalsRelIgnoreListInsert next ssa permuted target [6, 0] [.word aw, .word bw]
                      ⟨h.2.2.2.2.1, h.2.1, by simp [isPhyVar], rfl⟩
                  have incomingDivisor := ssaLocalsRelGetVar next ssa permuted incoming divisor (.word cw)
                      ⟨incomingLocals, sourceDivisor⟩
                  let numerator := aw.toNat * 2 ^ width + bw.toNat
                  let denominator := cw.toNat
                  by_cases valid : denominator ≠ 0 ∧ numerator / denominator < 2 ^ width
                  · let remainderWord := BitVec.ofNat width (numerator % denominator)
                    let quotientWord := BitVec.ofNat width (numerator / denominator)
                    let divided := WordSemStateFiniteExact.setVar 0 (.word quotientWord)
                        (WordSemStateFiniteExact.setVar 6 (.word remainderWord) incoming)
                    have instRun : WordSemStateFiniteExact.evaluate
                        (.inst (.arith (.longDiv 0 6 6 0 (optionLookup ssa divisor)))) incoming = (none, divided) := by
                      have incomingHigh : WordSemStateFiniteExact.getVar 6 incoming = some (.word aw) := by
                        simp [incoming, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars,
                          LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same]
                      have incomingLow : WordSemStateFiniteExact.getVar 0 incoming = some (.word bw) := by
                        simp [incoming, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars,
                          LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_ne,
                          sptLookup_sptInsert_same]
                      simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                        WordSemStateFiniteExact.getVars, incomingHigh, incomingLow, incomingDivisor]
                      have condition : cw.toNat ≠ 0 ∧
                          (aw.toNat * 2 ^ width + bw.toNat) / cw.toNat < 2 ^ width := valid
                      simp [condition, divided, numerator, denominator, quotientWord, remainderWord]
                    have remainderLocals := ssaLocalsRelIgnoreSetVar next ssa permuted incoming 6 (.word remainderWord)
                        ⟨h.2.2.2.2.1, incomingLocals, by decide⟩
                    have dividedLocals := ssaLocalsRelIgnoreSetVar next ssa permuted
                        (WordSemStateFiniteExact.setVar 6 (.word remainderWord) incoming) 0 (.word quotientWord)
                        ⟨h.2.2.2.2.1, remainderLocals, by decide⟩
                    have notPhysical : ¬ isPhyVar next := by
                      have allocated := h.2.2.1
                      simp [isAllocVar, isPhyVar] at allocated ⊢
                      omega
                    have extended := ssaMapOKExtend next ssa remainder ⟨h.2.2.2.2.1, notPhysical⟩
                    have firstLocals := ssaLocalsRelSetVar next ssa source.locals divided.locals remainder (.word remainderWord)
                        ⟨dividedLocals, h.2.2.2.2.1, bounds.2⟩
                    have finalLocals := ssaLocalsRelSetVar (next + 4) (sptInsert remainder next ssa)
                        (sptInsert remainder (.word remainderWord) source.locals)
                        (sptInsert next (.word remainderWord) divided.locals) quotient (.word quotientWord)
                        ⟨firstLocals, extended, by omega⟩
                    have orderedLocals : ssaLocalsRel (next + 4 + 4)
                        (sptInsert quotient (next + 4) (sptInsert remainder next ssa))
                        (sptInsert quotient (.word quotientWord) (sptInsert remainder (.word remainderWord) source.locals))
                        (sptInsert next (.word remainderWord) (sptInsert (next + 4) (.word quotientWord) divided.locals)) := by
                      rw [sptInsert_swap next (next + 4) (.word remainderWord) (.word quotientWord) divided.locals (by omega)]
                      exact finalLocals
                    dsimp only
                    simp only [ssaCcTrans, ssaCcTransInst, nextVarRename, evaluateSeqNative, moveRun, instRun]
                    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                      WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                      WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
                      LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same,
                      sptLookup_sptInsert_ne, Flapjack.WordAlloc.wordStateEqRel,
                      incoming, divided, permuted, quotientWord, remainderWord, numerator, denominator]
                  · have invalid : ¬(cw.toNat ≠ 0 ∧
                        (aw.toNat * 2 ^ width + bw.toNat) / cw.toNat < 2 ^ width) := valid
                    have sourceError : WordSemStateFiniteExact.evaluate
                        (.inst (.arith (.longDiv quotient remainder high low divisor)))
                        {source with permute := target.permute} = (some WordSemResult.error, permuted) := by
                      change WordSemStateFiniteExact.evaluate
                        (.inst (.arith (.longDiv quotient remainder high low divisor))) permuted = _
                      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, reads, invalid]
                    simp [sourceError]

end Flapjack.Compiler.Backend.WordAlloc
