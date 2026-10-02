import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof factoring of the native Seq clause after the original
fix_clock_evaluate theorem discharges clock normalization. This has no
independent HOL declaration; the full semantic Seq case uses this equation
without assuming a target execution or successful first result. -/
private theorem evaluateSeqFPMove {width : Nat} [NeZero width] {C F : Type}
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

namespace SemanticInstFPMovFromRegWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInstFPMovFromRegWitnesses

/-- Full original FPMovFromReg opcode with all six premises and complete
Error-exempt source-permutation simulation. Original SSA locals derive mapped
word reads; width64 copies one word to fixed64 FP, other widths concatenate
high/low inputs. Equal mapped inputs execute the actual fresh input Move;
map bounds derive preserved reads, and original fresh locals relation derives
postlocals without changing source locals. The exact Seq clock normalization
and postframe are proved. No target-run, source-success or post-state premise
is added. Missing/nonword reads retain Error exemption. Inst/evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8); this opcode only moves bits. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectInstFPMovFromReg {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next fp left right : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.inst (.fp (.fpMovFromReg fp left right))) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.inst (.fp (.fpMovFromReg fp left right))) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  refine ⟨target.permute, ?_⟩
  cases readLeft : WordSemStateFiniteExact.getVar left permuted with
  | none =>
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
  | some leftValue =>
    cases leftValue with
    | loc label offset =>
      simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
    | word leftWord =>
      have targetLeft := ssaLocalsRelGetVar next ssa permuted target left (.word leftWord) ⟨h.2.1, readLeft⟩
      by_cases size : width = 64
      · simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
          WordSemStateFiniteExact.setFpVar, ssaCcTrans, ssaCcTransInst,
          Flapjack.WordAlloc.wordStateEqRel, permuted]
      · cases readRight : WordSemStateFiniteExact.getVar right permuted with
        | none =>
          simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
        | some rightValue =>
          cases rightValue with
          | loc label offset =>
            simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst, permuted]
          | word rightWord =>
            have targetRight := ssaLocalsRelGetVar next ssa permuted target right (.word rightWord) ⟨h.2.1, readRight⟩
            by_cases mappedSame : optionLookup ssa left = optionLookup ssa right
            · have rightBound : right < next := by
                have occurrences := h.2.2.2.1
                simp only [everyVarHOL, everyVarInstHOL, size, if_false, Bool.and_eq_true] at occurrences
                exact of_decide_eq_true occurrences.2
              have originalRead : sptLookup right source.locals = some (.word rightWord) := readRight
              have domain := (h.2.1.2 right (.word rightWord) originalRead).1
              obtain ⟨register, found⟩ := (sptMem_iff_lookup right ssa).mp domain
              have registerBound := (h.2.2.2.2.1 right register found).2
              have selected : optionLookup ssa right = register := by simp [optionLookup, found]
              have fresh : optionLookup ssa right ≠ next := by omega
              have insertedLocals := ssaLocalsRelSetVar next ssa source.locals target.locals right (.word rightWord)
                ⟨h.2.1, h.2.2.2.2.1, rightBound⟩
              have unchanged (key : Nat) : sptLookup key (sptInsert right (.word rightWord) source.locals) =
                  sptLookup key source.locals := by
                by_cases same : key = right
                · subst key
                  simpa only [sptLookup_sptInsert_same] using originalRead.symm
                · exact sptLookup_sptInsert_ne right key (.word rightWord) source.locals same
              have finalLocals : ssaLocalsRel (next + 4) (sptInsert right next ssa)
                  source.locals (sptInsert next (.word rightWord) target.locals) := by
                simpa only [ssaLocalsRel, ssaLocalsRelWith, unchanged] using insertedLocals
              let moved := WordSemStateFiniteExact.setVar next (.word rightWord) target
              have moveRun : WordSemStateFiniteExact.evaluate
                  (.move 0 [(next, optionLookup ssa right)]) target = (none, moved) := by
                simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                  targetRight, WordSemStateFiniteExact.setVars, moved, WordSemStateFiniteExact.setVar,
                  LoopSemStateFiniteExact.sptAlistInsert]
              have movedLeft : WordSemStateFiniteExact.getVar (optionLookup ssa left) moved = some (.word leftWord) := by
                simpa [moved, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                  mappedSame, sptLookup_sptInsert_ne next (optionLookup ssa right) (.word rightWord) target.locals fresh]
                  using targetLeft
              have movedRight : WordSemStateFiniteExact.getVar next moved = some (.word rightWord) := by
                simp [moved, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
              have targetRun : WordSemStateFiniteExact.evaluate
                  (.seq (.move 0 [(next, optionLookup ssa right)])
                    (.inst (.fp (.fpMovFromReg fp (optionLookup ssa left) next)))) target =
                  (none, WordSemStateFiniteExact.setFpVar fp ((rightWord ++ leftWord).setWidth 64) moved) := by
                rw [evaluateSeqFPMove, moveRun]
                simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                  size, if_false, movedLeft, movedRight]
              have sourceRun : WordSemStateFiniteExact.evaluate
                  (.inst (.fp (.fpMovFromReg fp left right)))
                  {source with permute := target.permute} =
                  (none, WordSemStateFiniteExact.setFpVar fp ((rightWord ++ leftWord).setWidth 64) permuted) := by
                change WordSemStateFiniteExact.evaluate (.inst (.fp (.fpMovFromReg fp left right))) permuted = _
                simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                  size, if_false, readLeft, readRight]
              dsimp only
              simp only [sourceRun]
              simp only [ssaCcTrans, ssaCcTransInst, size, if_false, mappedSame, if_true,
                nextVarRename]
              have targetRunSame := targetRun
              simp only [mappedSame] at targetRunSame
              simp only [targetRunSame]
              simp_all [WordSemStateFiniteExact.setFpVar, Flapjack.WordAlloc.wordStateEqRel,
                moved, WordSemStateFiniteExact.setVar, permuted]
            · simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.inst,
                WordSemStateFiniteExact.setFpVar, ssaCcTrans, ssaCcTransInst,
                Flapjack.WordAlloc.wordStateEqRel, permuted]

end Flapjack.Compiler.Backend.WordAlloc
