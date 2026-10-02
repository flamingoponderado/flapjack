import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack.Compiler.Backend.WordAlloc

/-! Flapjack SSA input-boundary infrastructure, with no independent HOL original.
An accepted production encoding supplies native decoder availability. This is
not a structural roundtrip: cutsets and zero-offset memory may normalize. -/

theorem ssaInputInst_decoderClosure {width : Nat}
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) :
    (wordLangInstFromHOL native).isSome = true := by
  cases instruction with
  | arith operation =>
    cases operation <;> simp [wordLangInstToHOL, wordLangArithToHOL] at encoded
    all_goals subst native
    all_goals simp [wordLangInstFromHOL, wordLangArithFromHOL]
  | const destination value =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    rfl
  | mem operation destination address =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    simp [wordLangInstFromHOL]
  | memOffset operation destination address offset =>
    simp only [wordLangInstToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordLangInstFromHOL]
    split <;> rfl

theorem ssaInput_decoderClosure {width : Nat}
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    (wordLangProgFromHOL native).isSome = true := by
  cases program
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction with
    | none => simp [wordLangProgToHOL, hi] at encoded
    | some ni =>
      simp only [wordLangProgToHOL, hi, Option.map_some, Option.some.injEq] at encoded
      subst native
      simpa [wordLangProgFromHOL] using ssaInputInst_decoderClosure instruction ni hi
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp only [wordLangProgToHOL, hb, Option.map_some, Option.some.injEq] at encoded
      subst native
      simpa using ssaInput_decoderClosure body nb hb
  case seq left right =>
    cases hl : wordLangProgToHOL left <;> cases hr : wordLangProgToHOL right <;>
      simp [wordLangProgToHOL, hl, hr] at encoded
    subst native
    simp [ssaInput_decoderClosure left _ hl, ssaInput_decoderClosure right _ hr]
  case ite cmp register right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    simp [ssaInput_decoderClosure yes _ hy, ssaInput_decoderClosure no _ hn]
  case loop names body exits =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp [wordLangProgToHOL, hb] at encoded
      subst native
      simpa using ssaInput_decoderClosure body nb hb
  case call returns target arguments handler =>
    cases hReturns : returns with
    | none =>
      cases hHandler : handler with
      | none => simp [wordLangProgToHOL, hReturns, hHandler] at encoded; subst native; rfl
      | some h =>
        rcases h with ⟨exception, body, l1, l2⟩
        cases hb : wordLangProgToHOL body with
        | none => simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
        | some nb =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simp [ssaInput_decoderClosure body nb hb]
    | some r =>
      rcases r with ⟨values, sets, body, l1, l2⟩
      cases hb : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
      | some nb =>
        cases hHandler : handler with
        | none =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simp [ssaInput_decoderClosure body nb hb]
        | some h =>
          rcases h with ⟨exception, hbody, h1, h2⟩
          cases hh : wordLangProgToHOL hbody with
          | none => simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
          | some nh =>
            simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
            subst native
            simp [ssaInput_decoderClosure body nb hb, ssaInput_decoderClosure hbody nh hh]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals rfl
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

end Flapjack.Compiler.Backend.WordAlloc
