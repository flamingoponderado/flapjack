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

namespace SemanticInstAddCarryWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstAddCarryWitnesses

/-- Full original native AddCarry opcode simulation with all six premises
and complete Error-exempt source-permutation conclusion. Actual input Move
copies carry to physical 0 while the original SSA relation preserves both
operand reads. Native wordAddCarryHOL and the fresh result/physical carry
writes are evaluated, followed by the output Move. Original physical and two
fresh-write relations prove final locals including destination aliases.
Missing/non-word reads retain the source Error exemption; no target-run,
source-success or post-state premise is assumed. The Inst/evaluator boundary
inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstAddCarry {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next result left right carry : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.inst (.arith (.addCarry result left right carry))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.addCarry result left right carry))) source target ssa next tables := by
  have bounds : result < next ∧ carry < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact ⟨of_decide_eq_true occurrences.1.1.1, of_decide_eq_true occurrences.2⟩
  let permuted := {source with permute := target.permute}
  refine ⟨target.permute, ?_⟩
  cases reads : WordSemStateFiniteExact.getVars [left, right, carry] permuted with
  | none =>
    have absent : WordSemStateFiniteExact.getVars [left, right, carry]
        {source with permute := target.permute} = none := reads
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, absent]
  | some values =>
    have length := Flapjack.WordAlloc.getVarsLength [left, right, carry] permuted values reads
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
                      WordSemStateFiniteExact.getVar left permuted = some (.word aw) ∧
                      WordSemStateFiniteExact.getVar right permuted = some (.word bw) ∧
                      WordSemStateFiniteExact.getVar carry permuted = some (.word cw) := by
                    cases hl : WordSemStateFiniteExact.getVar left permuted <;>
                      cases hr : WordSemStateFiniteExact.getVar right permuted <;>
                      cases hc : WordSemStateFiniteExact.getVar carry permuted <;>
                      simp_all [WordSemStateFiniteExact.getVars]
                  obtain ⟨sourceLeft, sourceRight, sourceCarry⟩ := sourceReads
                  have renamedCarry := ssaLocalsRelGetVar next ssa permuted target carry (.word cw) ⟨h.2.1, sourceCarry⟩
                  let incoming := WordSemStateFiniteExact.setVar 0 (.word cw) target
                  have moveRun : WordSemStateFiniteExact.evaluate (.move 1 [(0, optionLookup ssa carry)]) target = (none, incoming) := by
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars, renamedCarry,
                      WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
                      WordSemStateFiniteExact.setVar, incoming]
                  have incomingLocals := ssaLocalsRelIgnoreSetVar next ssa permuted target 0 (.word cw)
                    ⟨h.2.2.2.2.1, h.2.1, by decide⟩
                  have incomingLeft := ssaLocalsRelGetVar next ssa permuted incoming left (.word aw) ⟨incomingLocals, sourceLeft⟩
                  have incomingRight := ssaLocalsRelGetVar next ssa permuted incoming right (.word bw) ⟨incomingLocals, sourceRight⟩
                  have incomingCarry : WordSemStateFiniteExact.getVar 0 incoming = some (.word cw) := by
                    simp [incoming, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                  let resultWord := (wordAddCarryHOL aw bw cw).1
                  let carryWord := (wordAddCarryHOL aw bw cw).2
                  let sourceResult := WordSemStateFiniteExact.setVar result (.word resultWord) permuted
                  let targetResult := WordSemStateFiniteExact.setVar next (.word resultWord) incoming
                  let added := WordSemStateFiniteExact.setVar 0 (.word carryWord) targetResult
                  have instRun : WordSemStateFiniteExact.evaluate
                      (.inst (.arith (.addCarry next (optionLookup ssa left) (optionLookup ssa right) 0))) incoming = (none, added) := by
                    simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                      WordSemStateFiniteExact.getVars, incomingLeft, incomingRight, incomingCarry]
                    rfl
                  have notPhysical : ¬ isPhyVar next := by
                    have allocated := h.2.2.1
                    simp [isAllocVar, isPhyVar] at allocated ⊢
                    omega
                  have extended := ssaMapOKExtend next ssa result ⟨h.2.2.2.2.1, notPhysical⟩
                  have resultLocals := ssaLocalsRelSetVar next ssa source.locals incoming.locals result (.word resultWord)
                    ⟨incomingLocals, h.2.2.2.2.1, bounds.1⟩
                  have addedLocals := ssaLocalsRelIgnoreSetVar (next + 4) (sptInsert result next ssa)
                      sourceResult targetResult 0 (.word carryWord) ⟨extended, resultLocals, by decide⟩
                  have finalLocals := ssaLocalsRelSetVar (next + 4) (sptInsert result next ssa)
                      sourceResult.locals added.locals carry (.word carryWord) ⟨addedLocals, extended, by omega⟩
                  have sourceRun : WordSemStateFiniteExact.evaluate
                      (.inst (.arith (.addCarry result left right carry)))
                      {source with permute := target.permute} =
                      (none, WordSemStateFiniteExact.setVar carry (.word carryWord) sourceResult) := by
                    change WordSemStateFiniteExact.evaluate
                      (.inst (.arith (.addCarry result left right carry))) permuted = _
                    simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, reads]
                    rfl
                  dsimp only
                  simp only [ssaCcTrans, ssaCcTransInst, nextVarRename, evaluateSeqNative, moveRun, instRun, sourceRun]
                  simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                    WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
                    LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same,
                    Flapjack.WordAlloc.wordStateEqRel, incoming, sourceResult, targetResult,
                    added, resultWord, carryWord]
                  simp [permuted]

end Flapjack.Compiler.Backend.WordAlloc
