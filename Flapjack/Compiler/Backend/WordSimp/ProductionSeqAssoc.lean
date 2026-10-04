import Flapjack.Compiler.Backend.WordSimp.ProductionSmartSeq

namespace Flapjack.Compiler.Backend.WordSimp

open RiscV
set_option autoImplicit false

/-- The executed accumulator traversal `wordSimpSeqAssocAcc` is the reviewed native
`Seq_assoc` (`word_simpScript.sml:21-38`) on the input codec image: for every represented
accumulator and program, the executed result encodes to `seqAssoc` of their encodings.
No output encoding is assumed. Flapjack carrier infrastructure; no separate HOL
declaration. -/
theorem seqAssocAcc_production {width : Nat} [NeZero width]
    (before program : WordProg (BitVec width))
    (nativeBefore native : WordLangProgHOL (BitVec width))
    (encodedBefore : wordLangProgToHOL before = some nativeBefore)
    (encoded : wordLangProgToHOL program = some native) :
    wordLangProgToHOL (wordSimpSeqAssocAcc before program) =
      some (seqAssoc nativeBefore native) := by
  match program with
  | .skip =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    rw [wordSimpSeqAssocAcc]
    simpa only [seqAssoc] using encodedBefore
  | .seq first second =>
    cases encodedFirst : wordLangProgToHOL first <;>
      cases encodedSecond : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, encodedFirst, encodedSecond] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    exact seqAssocAcc_production _ second _ _
      (seqAssocAcc_production before first nativeBefore _ encodedBefore encodedFirst)
      encodedSecond
  | .ite operator condition right thenBranch elseBranch =>
    cases encodedThen : wordLangProgToHOL thenBranch <;>
      cases encodedElse : wordLangProgToHOL elseBranch <;>
      simp [wordLangProgToHOL, encodedThen, encodedElse] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    apply smartSeq_production _ _ _ _ encodedBefore
    simp [wordLangProgToHOL,
      seqAssocAcc_production .skip thenBranch .skip _ rfl encodedThen,
      seqAssocAcc_production .skip elseBranch .skip _ rfl encodedElse]
  | .mustTerminate body =>
    cases encodedBody : wordLangProgToHOL body <;>
      simp [wordLangProgToHOL, encodedBody] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    apply smartSeq_production _ _ _ _ encodedBefore
    simp [wordLangProgToHOL, seqAssocAcc_production .skip body .skip _ rfl encodedBody]
  | .loop liveIn body liveOut =>
    cases encodedBody : wordLangProgToHOL body <;>
      simp [wordLangProgToHOL, encodedBody] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    apply smartSeq_production _ _ _ _ encodedBefore
    simp [wordLangProgToHOL, seqAssocAcc_production .skip body .skip _ rfl encodedBody]
  | .call none target arguments none =>
    simp [wordLangProgToHOL] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    exact smartSeq_production _ _ _ _ encodedBefore (by simp [wordLangProgToHOL])
  | .call none target arguments (some (exception, handlerBody, handlerFirst, handlerSecond)) =>
    cases encodedHandler : wordLangProgToHOL handlerBody <;>
      simp [wordLangProgToHOL, encodedHandler] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    apply smartSeq_production _ _ _ _ encodedBefore
    simp [wordLangProgToHOL,
      seqAssocAcc_production .skip handlerBody .skip _ rfl encodedHandler]
  | .call (some (values, sets, returnBody, firstLabel, secondLabel)) target arguments none =>
    cases encodedReturn : wordLangProgToHOL returnBody <;>
      simp [wordLangProgToHOL, encodedReturn] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    apply smartSeq_production _ _ _ _ encodedBefore
    simp [wordLangProgToHOL,
      seqAssocAcc_production .skip returnBody .skip _ rfl encodedReturn]
  | .call (some (values, sets, returnBody, firstLabel, secondLabel)) target arguments
      (some (exception, handlerBody, handlerFirst, handlerSecond)) =>
    cases encodedReturn : wordLangProgToHOL returnBody <;>
      cases encodedHandler : wordLangProgToHOL handlerBody <;>
      simp [wordLangProgToHOL, encodedReturn, encodedHandler] at encoded
    subst native
    rw [wordSimpSeqAssocAcc, seqAssoc]
    apply smartSeq_production _ _ _ _ encodedBefore
    simp [wordLangProgToHOL,
      seqAssocAcc_production .skip returnBody .skip _ rfl encodedReturn,
      seqAssocAcc_production .skip handlerBody .skip _ rfl encodedHandler]
  | .move _ _ | .assign _ _ | .inst _ | .get _ _ | .store _ _ | .set _ _ | .break _
  | .continue _ | .raise _ | .return _ _ | .tick | .locValue _ _ | .alloc _ _
  | .storeConsts _ _ _ _ _ | .opCurrHeap _ _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ =>
    rw [wordSimpSeqAssocAcc]
    · rw [smartSeq_production _ _ _ _ encodedBefore encoded]
      simp only [wordLangProgToHOL, Option.some.injEq, Option.map_eq_some_iff] at encoded
      first
        | (subst native; rfl)
        | (obtain ⟨_, _, rfl⟩ := encoded; rfl)
    all_goals simp
termination_by sizeOf program

/-- The executed `wordSimpSeqAssoc` is the native `Seq_assoc Skip` of HOL `compile_exp`
(`word_simpScript.sml:493`) on the codec image (Flapjack carrier infrastructure). -/
theorem seqAssoc_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordLangProgToHOL (wordSimpSeqAssoc program) = some (seqAssoc .skip native) :=
  seqAssocAcc_production .skip program .skip native rfl encoded

end Flapjack.Compiler.Backend.WordSimp
