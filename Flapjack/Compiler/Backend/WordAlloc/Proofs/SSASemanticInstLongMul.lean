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

namespace SemanticInstLongMulWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstLongMulWitnesses

/-- Full original native LongMul opcode simulation with the six original
premises and complete Error-exempt source-permutation conclusion. The compiler's
input Move into physical 0/4, actual LongMul 6/0/0/4 and output Move to the two
fresh destinations are evaluated. Physical writes preserve SSA locals; two
original fresh-write relations establish destination updates, including aliased
source destinations. Operand errors retain the original source Error exemption.
No target-run, source-success or post-state relation premise is added.
The native Inst/evaluator boundary inherits reals_as_rational_cuts
(SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstLongMul {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next high low left right : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.inst (.arith (.longMul high low left right))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.longMul high low left right))) source target ssa next tables := by
  have bounds : high < next ∧ low < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact ⟨of_decide_eq_true occurrences.1.1.1, of_decide_eq_true occurrences.1.1.2⟩
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
    | cons l rest =>
      cases rest with
      | nil => simp at length
      | cons r rest =>
        cases rest with
        | cons x xs => simp at length
        | nil =>
          cases l with
          | loc label offset => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
          | word lword =>
            cases r with
            | loc label offset => simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
            | word rword =>
              let incoming := WordSemStateFiniteExact.setVars [0, 4] [.word lword, .word rword] target
              have moveRun : WordSemStateFiniteExact.evaluate
                  (.move 1 [(0, optionLookup ssa left), (4, optionLookup ssa right)]) target =
                  (none, incoming) := by
                have renamedReads : WordSemStateFiniteExact.getVars
                    [optionLookup ssa left, optionLookup ssa right] target =
                    some [.word lword, .word rword] := by simpa using transferred
                simp [WordSemStateFiniteExact.evaluate, incoming, renamedReads]
              let product := lword.toNat * rword.toNat
              let highWord := BitVec.ofNat width (product / 2 ^ width)
              let lowWord := BitVec.ofNat width product
              let multiplied := WordSemStateFiniteExact.setVar 0 (.word lowWord)
                  (WordSemStateFiniteExact.setVar 6 (.word highWord) incoming)
              have instRun : WordSemStateFiniteExact.evaluate (.inst (.arith (.longMul 6 0 0 4))) incoming =
                  (none, multiplied) := by
                simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                  WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                  WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
                  LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same,
                  sptLookup_sptInsert_ne, incoming, multiplied, highWord, lowWord, product]
              have incomingLocals := ssaLocalsRelIgnoreListInsert next ssa permuted target [0, 4]
                  [.word lword, .word rword] ⟨h.2.2.2.2.1, h.2.1, by simp [isPhyVar], rfl⟩
              have highLocals := ssaLocalsRelIgnoreSetVar next ssa permuted incoming 6 (.word highWord)
                  ⟨h.2.2.2.2.1, incomingLocals, by decide⟩
              have multipliedLocals := ssaLocalsRelIgnoreSetVar next ssa permuted
                  (WordSemStateFiniteExact.setVar 6 (.word highWord) incoming) 0 (.word lowWord)
                  ⟨h.2.2.2.2.1, highLocals, by decide⟩
              have notPhysical : ¬ isPhyVar next := by
                have allocated := h.2.2.1
                simp [isAllocVar, isPhyVar] at allocated ⊢
                omega
              have extended := ssaMapOKExtend next ssa high ⟨h.2.2.2.2.1, notPhysical⟩
              have firstLocals := ssaLocalsRelSetVar next ssa source.locals multiplied.locals high (.word highWord)
                  ⟨multipliedLocals, h.2.2.2.2.1, bounds.1⟩
              have finalLocals := ssaLocalsRelSetVar (next + 4) (sptInsert high next ssa)
                  (sptInsert high (.word highWord) source.locals)
                  (sptInsert next (.word highWord) multiplied.locals) low (.word lowWord)
                  ⟨firstLocals, extended, by omega⟩
              dsimp only
              simp only [ssaCcTrans, ssaCcTransInst, nextVarRename, evaluateSeqNative, moveRun, instRun]
              simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
                LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same,
                sptLookup_sptInsert_ne, Flapjack.WordAlloc.wordStateEqRel,
                incoming, multiplied, permuted, highWord, lowWord, product]

end Flapjack.Compiler.Backend.WordAlloc
