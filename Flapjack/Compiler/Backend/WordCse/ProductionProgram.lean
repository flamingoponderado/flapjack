import Flapjack.Compiler.Backend.WordCse.ProductionArithmetic
import Flapjack.Compiler.Backend.WordCse.ProductionMemory
import Flapjack.Compiler.Backend.WordCse.ProductionHeapLoc
import Flapjack.Compiler.Backend.WordCse.ProductionAssign
import Flapjack.Compiler.Backend.WordCse.ProductionJoin
import Flapjack.Compiler.Backend.WordCse.CanonicalMove

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV Compiler.Encoders.Asm

/-- Whole actual instruction transition on the existing input codec image.
Only source wfData, input knowledge relation and input representation are
assumed. Unsupported native Skip/FP instruction carriers are rejected by the
existing codec, rather than silently translated. No HOL tag is added. -/
theorem wordCseInstruction_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (instruction : WordLangInst (BitVec width)) (executedInstruction : WordInst (BitVec width))
    (converted : wordLangInstFromHOL instruction = some executedInstruction) :
    let nativeOutput := wordCseInst native (HolInst.ofWordLangInst instruction)
    let executedOutput := RiscV.wordCseInst executed executedInstruction
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  cases instruction with
  | skip => simp [wordLangInstFromHOL] at converted
  | fp operation => simp [wordLangInstFromHOL] at converted
  | const destination word =>
    simp only [wordLangInstFromHOL, Option.some.injEq] at converted
    subst executedInstruction
    have invalidRelated := invalidateData_transport native executed related destination
    have invalidWf := wfData_invalidate native destination wellFormed
    simp only [HolInst.ofWordLangInst, wordCseInst, RiscV.wordCseInst]
    by_cases even : destination % 2 = 0
    · simp only [even, if_pos, beq_self_eq_true]
      exact ⟨invalidRelated, rfl⟩
    · have evenBool : (destination % 2 == 0) = false := beq_eq_false_iff_ne.mpr even
      simp only [even, evenBool, Bool.false_eq_true, if_false]
      have output := addToDataConst_transport _ _ invalidRelated
        invalidWf.2.2.2.2.2.2.2.1 destination word
      exact ⟨output.1, output.2.2⟩
  | arith operation =>
    have codec : wordLangArithFromHOL operation =
        some (executedArithmetic (HolArith.ofWordLangArith operation)) := by
      cases operation <;> simp [wordLangArithFromHOL, executedArithmetic, HolArith.ofWordLangArith]
    simp only [wordLangInstFromHOL, codec, Option.map_some, Option.some.injEq] at converted
    subst executedInstruction
    simpa only [HolInst.ofWordLangInst] using
      wordCseArithmetic_production_transport native executed related wellFormed
        (HolArith.ofWordLangArith operation)
  | mem operator destination address =>
    cases address with
    | addr source offset =>
      have codec : wordLangInstFromHOL (.mem operator destination (.addr source offset)) =
          some (executedMemoryInst operator destination source offset) := by
        by_cases zero : offset = 0 <;> simp_all [wordLangInstFromHOL, executedMemoryInst]
      rw [codec] at converted
      simp only [Option.some.injEq] at converted
      subst executedInstruction
      simpa only [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr] using
        wordCseMemory_production_transport native executed related wellFormed
          operator destination source offset

/-- Complete CSE program relationship on the existing input carrier codec.
The representation boundary is an input conversion, never an assumed output
or target run. Every recursive call uses original wfData preservation.
This is production correspondence infrastructure, not a new tagged HOL port. -/
theorem wordCseProgram_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (program : WordLangProgHOL (BitVec width)) (executedProgram : WordProg (BitVec width))
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (converted : wordLangProgFromHOL program = some executedProgram) :
    KnowledgeRel width (wordCse native program).1 (wordCseProg executed executedProgram).2 ∧
      wordLangProgFromHOL (wordCse native program).2 = some (wordCseProg executed executedProgram).1 := by
  have originalConverted := converted
  cases program
  all_goals try simp only [wordLangProgFromHOL] at converted
  all_goals try simp only [Option.some.injEq] at converted
  all_goals try subst executedProgram
  all_goals first
    | exact wordCseAssign_production_transport _ _ related _ _
    | exact wordCseHeap_production_transport _ _ related wellFormed _ _ _
    | exact wordCseLocValue_production_transport _ _ related wellFormed _ _
    | simpa only [wordCse] using getClause_transport _ _ related _ _
    | simpa only [wordCse] using setClause_transport _ _ related _ _
    | skip
  all_goals try (simp only [wordCse, wordCseProg]; exact ⟨related, rfl⟩)
  all_goals try (simp only [wordCse, wordCseProg]; exact ⟨emptyKnowledgeRel width, rfl⟩)
  case move priority moves =>
    simp only [wordCse, wordCseProg]
    exact ⟨canonicalMoveRegs_transport native executed related moves, rfl⟩
  case inst instruction =>
    cases codec : wordLangInstFromHOL instruction with
    | none => simp [codec] at converted
    | some actual =>
      simp only [codec, Option.map_some, Option.some.injEq] at converted
      subst executedProgram
      simpa only [wordCse, wordCseProg] using
        wordCseInstruction_production_transport native executed related wellFormed instruction actual codec
  case store address value =>
    simp only [wordCse, wordCseProg]
    exact ⟨wipeLoads_production_transport native executed related, rfl⟩
  case storeConsts source bitmap codeLength dataLength constants =>
    simp only [wordCse, wordCseProg]
    exact ⟨wipeLoads_production_transport _ _
      (invalidateRegs_transport native executed related [source,bitmap,codeLength,dataLength]), rfl⟩
  case shareInst operator name address =>
    cases store : isStore operator <;> simp only [wordCse, wordCseProg, wordCseIsStore, store,
      Bool.false_eq_true, if_false, if_true]
    · exact ⟨invalidateData_transport native executed related name, rfl⟩
    · exact ⟨related, rfl⟩
  case mustTerminate body =>
    cases codec : wordLangProgFromHOL body with
    | none => simp [codec] at converted
    | some actual =>
      simp only [codec, Option.map_some, Option.some.injEq] at converted
      subst executedProgram
      have output := wordCseProgram_production_transport native executed body actual related wellFormed codec
      simp only [wordCse, wordCseProg]
      refine ⟨output.1, ?_⟩
      simp only [wordLangProgFromHOL, output.2, Option.map_some]
  case seq first second =>
    cases firstCodec : wordLangProgFromHOL first with
    | none => simp [firstCodec] at converted
    | some actualFirst =>
      cases secondCodec : wordLangProgFromHOL second with
      | none => simp [firstCodec, secondCodec] at converted
      | some actualSecond =>
        simp [firstCodec, secondCodec] at converted
        subst executedProgram
        have firstOutput := wordCseProgram_production_transport native executed first actualFirst related wellFormed firstCodec
        have secondOutput := wordCseProgram_production_transport (wordCse native first).1
          (wordCseProg executed actualFirst).2 second actualSecond firstOutput.1
          (word_cse_wf_data first native wellFormed) secondCodec
        simp only [wordCse, wordCseProg]
        refine ⟨secondOutput.1, ?_⟩
        simp [wordLangProgFromHOL, firstOutput.2, secondOutput.2]
  case ite operator condition right first second =>
    cases firstCodec : wordLangProgFromHOL first with
    | none => simp [firstCodec] at converted
    | some actualFirst =>
      cases secondCodec : wordLangProgFromHOL second with
      | none => simp [firstCodec, secondCodec] at converted
      | some actualSecond =>
        simp [firstCodec, secondCodec] at converted
        subst executedProgram
        have firstOutput := wordCseProgram_production_transport native executed first actualFirst related wellFormed firstCodec
        have secondOutput := wordCseProgram_production_transport native executed second actualSecond related wellFormed secondCodec
        simp only [wordCse, wordCseProg]
        refine ⟨mergeData_wf_production_transport _ _ _ _ firstOutput.1 secondOutput.1
          (word_cse_wf_data first native wellFormed) (word_cse_wf_data second native wellFormed), ?_⟩
        simp [wordLangProgFromHOL, firstOutput.2, secondOutput.2]
  case loop liveIn body liveOut =>
    cases codec : wordLangProgFromHOL body with
    | none => simp [codec] at converted
    | some actual =>
      simp [codec] at converted
      subst executedProgram
      have output := wordCseProgram_production_transport emptyData wordCseEmpty body actual
        (emptyKnowledgeRel width) wfData_empty codec
      simp only [wordCse, wordCseProg]
      refine ⟨emptyKnowledgeRel width, ?_⟩
      simp [wordLangProgFromHOL, output.2]
  case call returns target arguments handler =>
    cases returns <;> cases handler
    all_goals simp [wordLangProgFromHOL, bind, Option.bind_eq_some_iff] at converted
    all_goals repeat' rcases converted with ⟨_, converted⟩
    all_goals simp only [wordCse, wordCseProg]
    all_goals exact ⟨emptyKnowledgeRel width, originalConverted⟩
termination_by sizeOf program

/-- Actual whole-pass wrapper corresponds to the reviewed original wrapper
for every successfully represented input program. Source well-formedness and
all five initial knowledge observations are discharged from empty knowledge;
no output correspondence, callback or successful execution is assumed. -/
theorem wordCommonSubexpElim_production_transport {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (executedProgram : WordProg (BitVec width))
    (converted : wordLangProgFromHOL program = some executedProgram) :
    wordLangProgFromHOL (wordCommonSubexpElim program) = some (wordCseProp executedProgram) := by
  have output := wordCseProgram_production_transport emptyData wordCseEmpty program executedProgram
    (emptyKnowledgeRel width) wfData_empty converted
  exact output.2

end Flapjack.Compiler.Backend.WordCse
