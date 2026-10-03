import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar

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

namespace SemanticRaiseWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticRaiseWitnesses

/-- Full original native Raise semantic case, with all six original premises
and complete Error-exempt source-permutation/result/frame/result-sensitive locals
conclusion. Renamed register lookup and the actual singleton Move to register 2
are derived internally. The original handler bound, LASTN stack-frame shape,
and optional handler cases are preserved. Successful native jumpExc restores
identical frame locals on both sides; no desired target run, successful unwind,
or post-state relation is assumed. The total evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectRaise {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.raise name : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.raise name : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  have sameRead (permutation : Nat → Nat → Nat) :
      WordSemStateFiniteExact.getVar name {source with permute := permutation} =
        WordSemStateFiniteExact.getVar name source := rfl
  refine ⟨target.permute, ?_⟩
  cases found : WordSemStateFiniteExact.getVar name source with
  | none => simp [WordSemStateFiniteExact.evaluate, sameRead, found]
  | some value =>
    have renamed := ssaLocalsRelGetVar next ssa source target name value ⟨h.2.1, found⟩
    have moveRun : WordSemStateFiniteExact.evaluate
        (.move 1 [(2, optionLookup ssa name)]) target =
        (none, WordSemStateFiniteExact.setVars [2] [value] target) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars, renamed]
    have movedRead : WordSemStateFiniteExact.getVar 2
        (WordSemStateFiniteExact.setVars [2] [value] target) = some value := by
      simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars,
        LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same]
    have stackEq : target.stack = source.stack := h.1.2.2.2.1
    have handlerEq : target.handler = source.handler := h.1.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp only
    simp only [ssaCcTrans, evaluateSeqNative, moveRun]
    by_cases bound : source.handler < source.stack.length
    · cases frames : wordSemLastN (source.handler + 1) source.stack with
      | nil =>
        simp [WordSemStateFiniteExact.evaluate, sameRead, found,
          WordSemStateFiniteExact.jumpExc, bound, frames]
      | cons frame rest =>
        cases frame with
        | stackFrame size nonGc gc handler =>
          cases handler with
          | none =>
            simp [WordSemStateFiniteExact.evaluate, sameRead, found,
              WordSemStateFiniteExact.jumpExc, bound, frames]
          | some info =>
            rcases info with ⟨handler, label, offset⟩
            simp only [WordSemStateFiniteExact.evaluate, sameRead, found,
              WordSemStateFiniteExact.jumpExc, WordSemStateFiniteExact.setVars,
              stackEq, handlerEq, bound, if_pos, frames]
            simp_all [Flapjack.WordAlloc.wordStateEqRel, WordSemStateFiniteExact.getVar,
              LoopSemStateFiniteExact.sptAlistInsert, sptLookup_sptInsert_same]
    · simp [WordSemStateFiniteExact.evaluate, sameRead, found,
        WordSemStateFiniteExact.jumpExc, bound]

end Flapjack.Compiler.Backend.WordAlloc
