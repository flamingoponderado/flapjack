import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAInputCodec

namespace Flapjack

/-- Fixed positive-width production-carrier boundary for the complete native
SSA producer. Rejection is exactly the existing input encoder boundary; the
checked decoder introduces no new rejection. This Flapjack adapter has no HOL
original and is not yet wired into the executed allocation callers. -/
def wordFullSsaCcTransNative {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    Option (WordProg (BitVec width)) :=
  (wordLangProgToHOL program).bind fun native =>
    wordLangProgFromHOL (Compiler.Backend.WordAlloc.fullSsaCcTrans parameterCount native)

/-- The complete native pass has no additional output-decoder failure on any
accepted production encoding. No native input-availability or target-result
premise is assumed. This is Flapjack carrier infrastructure, not a HOL port. -/
theorem wordFullSsaCcTransNative_domain {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    (wordFullSsaCcTransNative parameterCount program).isSome =
      (wordLangProgToHOL program).isSome := by
  cases encoded : wordLangProgToHOL program with
  | none => simp [wordFullSsaCcTransNative, encoded]
  | some native =>
    simp only [wordFullSsaCcTransNative, encoded, Option.bind_some, Option.isSome_some]
    exact Compiler.Backend.WordAlloc.fullSsaCcTrans_decoderClosure parameterCount native
      (Compiler.Backend.WordAlloc.ssaInput_decoderClosure program native encoded)

/-- Exact wrapper equation on each accepted input image. It invokes the native
full producer itself; it does not call the generic SSA implementation. -/
theorem wordFullSsaCcTransNative_of_encoded {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordFullSsaCcTransNative parameterCount program =
      wordLangProgFromHOL (Compiler.Backend.WordAlloc.fullSsaCcTrans parameterCount native) := by
  simp [wordFullSsaCcTransNative, encoded]

end Flapjack
