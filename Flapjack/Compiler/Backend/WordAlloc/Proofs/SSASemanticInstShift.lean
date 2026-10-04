import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates

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

namespace SemanticInstShiftWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstShiftWitnesses

/-- Genuine full native Shift opcode case, including register and immediate
operands, all six original premises and the complete source-permutation
simulation conclusion. The register case executes the compiler's physical
Move8; original physical-write and getVar relations derive preservation of the
source operand. Failed reads and out-of-range shift counts retain the original
Error exemption. No successful-evaluation or post-state premise is added.
The native Inst/evaluator boundary inherits reals_as_rational_cuts
(SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectInstShift {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next dst src : Nat) (operator : Shift)
    (immediate : WordRegImm (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst (.arith (.shift operator dst src immediate))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.arith (.shift operator dst src immediate))) source target ssa next tables := by
  have bound : dst < next := by
    have occurrences := h.2.2.2.1
    simp only [everyVarHOL, everyVarInstHOL, Bool.and_eq_true] at occurrences
    exact of_decide_eq_true occurrences.1.1
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  cases immediate with
  | reg right =>
    refine ⟨target.permute, ?_⟩
    cases sourceRead : WordSemStateFiniteExact.getVar src permuted with
    | none =>
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, WordSemStateFiniteExact.wordExp, permuted] at sourceRead ⊢
      simp [sourceRead]
    | some sourceValue =>
      cases sourceValue with
      | loc label offset =>
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
          WordSemStateFiniteExact.assign, WordSemStateFiniteExact.wordExp, permuted] at sourceRead ⊢
        simp [sourceRead]
      | word sourceWord =>
        cases countRead : WordSemStateFiniteExact.getVar right permuted with
        | none =>
          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
            WordSemStateFiniteExact.assign, WordSemStateFiniteExact.wordExp, permuted] at sourceRead countRead ⊢
          simp [sourceRead, countRead]
        | some countValue =>
          cases countValue with
          | loc label offset =>
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
              WordSemStateFiniteExact.assign, WordSemStateFiniteExact.wordExp, permuted] at sourceRead countRead ⊢
            simp [sourceRead, countRead]
          | word countWord =>
            let updated := WordSemStateFiniteExact.setVar 8 (.word countWord) target
            have renamedCount := ssaLocalsRelGetVar next ssa permuted target right (.word countWord) ⟨h.2.1, countRead⟩
            have moveRun : WordSemStateFiniteExact.evaluate (.move 1 [(8, optionLookup ssa right)]) target =
                (none, updated) := by
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars, renamedCount,
                WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
                LoopSemStateFiniteExact.sptAlistInsert, updated]
            have updatedLocals := ssaLocalsRelIgnoreSetVar next ssa permuted target 8 (.word countWord)
              ⟨h.2.2.2.2.1, h.2.1, by decide⟩
            have updatedRead := ssaLocalsRelGetVar next ssa permuted updated src (.word sourceWord)
              ⟨updatedLocals, sourceRead⟩
            have updatedCount : WordSemStateFiniteExact.getVar 8 updated = some (.word countWord) := by
              simp [updated, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
                sptLookup_sptInsert_same]
            let expr : WordLangExpHOL (BitVec width) := .shift operator (.var src) (.var right)
            have transferred : WordSemStateFiniteExact.wordExp updated
                (.shift operator (.var (optionLookup ssa src)) (.var 8)) =
                WordSemStateFiniteExact.wordExp permuted expr := by
              simp only [expr, WordSemStateFiniteExact.wordExp, updatedRead, updatedCount, sourceRead, countRead]
            have compiled : ssaCcTrans (width := width) (.inst (.arith (.shift operator dst src (.reg right)))) ssa next tables =
                (.seq (.move 1 [(8, optionLookup ssa right)])
                  (.inst (.arith (.shift operator next (optionLookup ssa src) (.reg 8)))),
                  sptInsert dst next ssa, next + 4) := rfl
            cases found : WordSemStateFiniteExact.wordExp permuted expr with
            | none =>
              have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
                  (.shift operator (.var src) (.var right)) = none := found
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                WordSemStateFiniteExact.assign, absent]
            | some value =>
              have targetExpr := transferred.trans found
              have locals := ssaLocalsRelSetVar next ssa source.locals updated.locals dst value
                ⟨updatedLocals, h.2.2.2.2.1, bound⟩
              dsimp only
              simp only [compiled, evaluateSeqNative, moveRun]
              simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                WordSemStateFiniteExact.assign, WordSemStateFiniteExact.setVar,
                Flapjack.WordAlloc.wordStateEqRel, permuted, expr, updated]
  | imm word =>
    let expr : WordLangExpHOL (BitVec width) := .shift operator (.var src) (.const word)
    refine ⟨target.permute, ?_⟩
    cases found : WordSemStateFiniteExact.wordExp permuted expr with
    | none =>
      have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute}
          (.shift operator (.var src) (.const word)) = none := found
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, absent]
    | some value =>
      have targetEval := ssaCcTransExpCorrect permuted expr target ssa next value ⟨found, frame, h.2.1⟩
      have locals := ssaLocalsRelSetVar next ssa source.locals target.locals dst value
        ⟨h.2.1, h.2.2.2.2.1, bound⟩
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
        WordSemStateFiniteExact.assign, WordSemStateFiniteExact.setVar,
        ssaCcTrans, ssaCcTransInst, nextVarRename, ssaCcTransExp,
        Flapjack.WordAlloc.wordStateEqRel, permuted, expr]

end Flapjack.Compiler.Backend.WordAlloc
