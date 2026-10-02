import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsDelete
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the native Seq clause using original fix_clock_evaluate;
no independently claimed HOL declaration or successful target-run premise. -/
private theorem evaluateSeqStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq first second) state =
      match WordSemStateFiniteExact.evaluate first state with
      | (none, after) => WordSemStateFiniteExact.evaluate second after
      | (some result, after) => (some result, after) := by
  simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases WordSemStateFiniteExact.evaluate first state with
  | mk result after => cases result <;> rfl

namespace SemanticStoreConstsWitnesses

/-- Canonical roundtrip of the actual imported native state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticStoreConstsWitnesses

/-- Full original StoreConsts SSA simulation. The original six premises and
entire Error-exempt source permutation/result/frame/locals conclusion remain.
Physical scratch-register writes/deletions and both fresh SSA destinations are
derived from the actual three-step target program. Inherits evaluator real
rendering boundary (reals_as_rational_cuts, SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next tmp1 tmp2 address offset : Nat)
    (words : List (Bool × BitVec width)) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := width) (fun x => decide (x < next))
        (.storeConsts tmp1 tmp2 address offset words) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.storeConsts tmp1 tmp2 address offset words) source target ssa next tables := by
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  have related : ssaLocalsRel next ssa permuted.locals target.locals := h.2.1
  refine ⟨target.permute, ?_⟩
  cases addressRead : WordSemStateFiniteExact.getVar address permuted with
  | none => simp [WordSemStateFiniteExact.evaluate, permuted, addressRead]
  | some addressValue =>
    cases addressValue with
    | loc p q => simp [WordSemStateFiniteExact.evaluate, permuted, addressRead]
    | word a =>
      cases offsetRead : WordSemStateFiniteExact.getVar offset permuted with
      | none => simp [WordSemStateFiniteExact.evaluate, permuted, addressRead, offsetRead]
      | some offsetValue =>
        cases offsetValue with
        | loc p q => simp [WordSemStateFiniteExact.evaluate, permuted, addressRead, offsetRead]
        | word off =>
          by_cases validAddresses : wordSemConstAddresses a words permuted.mdomain = true
          · have targetAddress := ssaLocalsRelGetVar next ssa permuted target address (.word a)
              ⟨related, addressRead⟩
            have targetOffset := ssaLocalsRelGetVar next ssa permuted target offset (.word off)
              ⟨related, offsetRead⟩
            let advanced := a + wordSemBytesInWord * BitVec.ofNat width words.length
            let scratch := WordSemStateFiniteExact.setVars [4,6] [.word a,.word off] target
            let written := WordSemStateFiniteExact.setVar 4 (.word advanced)
              (WordSemStateFiniteExact.setVar 6 (.word off)
              (WordSemStateFiniteExact.unsetVar 0 (WordSemStateFiniteExact.unsetVar 2
                {scratch with memory := wordSemConstWrites a off words scratch.memory})))
            let finished := WordSemStateFiniteExact.setVars [next+4,next]
              [.word advanced,.word off] written
            let sourceWritten := WordSemStateFiniteExact.setVar address (.word advanced)
              (WordSemStateFiniteExact.setVar offset (.word off)
              (WordSemStateFiniteExact.unsetVar tmp1 (WordSemStateFiniteExact.unsetVar tmp2
                {permuted with memory := wordSemConstWrites a off words permuted.memory})))
            have scratchRun : WordSemStateFiniteExact.evaluate
                (.move 1 [(4,optionLookup ssa address),(6,optionLookup ssa offset)]) target =
                (none,scratch) := by
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                targetAddress,targetOffset,scratch]
            have domainSame : target.mdomain = permuted.mdomain := frame.2.2.2.2.2.2.2.2.1
            have validTarget : wordSemConstAddresses a words target.mdomain = true := by
              rw [domainSame]; exact validAddresses
            have writeRun : WordSemStateFiniteExact.evaluate (.storeConsts 0 2 4 6 words) scratch =
                (none,written) := by
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
                scratch, WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
                sptLookup_sptInsert, validTarget, written, advanced]
            have finishRun : WordSemStateFiniteExact.evaluate
                (.move 1 [(next+4,4),(next,6)]) written = (none,finished) := by
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                WordSemStateFiniteExact.getVar, written, WordSemStateFiniteExact.setVar,
                sptLookup_sptInsert, finished]
            have compiledRun : WordSemStateFiniteExact.evaluate
                (.seq (.move 1 [(4,optionLookup ssa address),(6,optionLookup ssa offset)])
                  (.seq (.storeConsts 0 2 4 6 words) (.move 1 [(next+4,4),(next,6)]))) target =
                (none,finished) := by
              rw [evaluateSeqStoreConsts, scratchRun]
              dsimp only
              rw [evaluateSeqStoreConsts, writeRun]
              exact finishRun
            have beforeFresh : ssaLocalsRel next ssa
                (sptDelete tmp1 (sptDelete tmp2 permuted.locals)) written.locals := by
              have physicalUpdates := ssaLocalsPhysicalListUpdate next ssa permuted.locals
                target.locals [4,6] [.word a,.word off] h.2.2.2.2.1 related
                (by intro name member; simp at member; rcases member with rfl | rfl <;> decide)
              have sourceDeleted := ssaLocalsRelDeleteLeft next ssa _ _ tmp1
                (ssaLocalsRelDeleteLeft next ssa _ _ tmp2 physicalUpdates)
              have delete2 := ssaLocalsRelDeleteRight next ssa _ _ 2
                ⟨h.2.2.2.2.1,sourceDeleted,by decide⟩
              have delete0 := ssaLocalsRelDeleteRight next ssa _ _ 0
                ⟨h.2.2.2.2.1,delete2,by decide⟩
              have insert6 := ssaLocalsRelIgnoreInsert next ssa _ _ 6 (.word off)
                ⟨h.2.2.2.2.1,delete0,by decide⟩
              exact ssaLocalsRelIgnoreInsert next ssa _ _ 4 (.word advanced)
                ⟨h.2.2.2.2.1,insert6,by decide⟩
            have bounds := h.2.2.2.1
            simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at bounds
            have nonphysical : ¬ isPhyVar next := by
              have alloc := h.2.2.1
              simp only [isAllocVar, decide_eq_true_eq] at alloc
              simp only [isPhyVar, decide_eq_true_eq]; omega
            have freshOffset := ssaLocalsRelSetVar next ssa _ _ offset (.word off)
              ⟨beforeFresh,h.2.2.2.2.1,bounds.2⟩
            have freshAddress := ssaLocalsRelSetVar (next+4) (sptInsert offset next ssa)
              _ _ address (.word advanced)
              ⟨freshOffset,ssaMapOKExtend next ssa offset ⟨h.2.2.2.2.1,nonphysical⟩,
                by have addressBound := bounds.1.2; omega⟩
            have finalLocals : ssaLocalsRel (next+4+4)
                (sptInsert address (next+4) (sptInsert offset next ssa))
                sourceWritten.locals finished.locals := by
              simpa only [sourceWritten,finished,WordSemStateFiniteExact.setVars,
                WordSemStateFiniteExact.setVar,WordSemStateFiniteExact.unsetVar,
                LoopSemStateFiniteExact.sptAlistInsert] using freshAddress
            have sourceRun : WordSemStateFiniteExact.evaluate
                (.storeConsts tmp1 tmp2 address offset words) permuted = (none,sourceWritten) := by
              simp only [WordSemStateFiniteExact.evaluate,addressRead,offsetRead,
                validAddresses,not_true_eq_false,if_false]
              rfl
            have sourceExpanded := sourceRun
            dsimp only [permuted] at sourceExpanded
            dsimp only
            simp only [sourceExpanded,reduceCtorEq,if_false]
            simp only [ssaCcTrans,nextVarRename]
            rw [compiledRun]
            refine ⟨rfl,?_,finalLocals⟩
            simp_all [sourceWritten,finished,written,scratch,
              WordSemStateFiniteExact.setVar,WordSemStateFiniteExact.setVars,
              WordSemStateFiniteExact.unsetVar,Flapjack.WordAlloc.wordStateEqRel]
          · simp [WordSemStateFiniteExact.evaluate,permuted,addressRead,offsetRead,validAddresses]

end Flapjack.Compiler.Backend.WordAlloc
