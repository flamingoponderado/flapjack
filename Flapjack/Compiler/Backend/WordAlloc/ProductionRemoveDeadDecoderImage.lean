import Flapjack.Compiler.Backend.WordAlloc.ProductionRemoveDead
import Flapjack.Compiler.Backend.WordUnreach.ProductionEncoderDomain

namespace Flapjack.WordAlloc
open Compiler.Backend.WordUnreach

/-- Flapjack carrier infrastructure: native dead-code removal preserves the
actual decoder domain for arbitrary backward liveness and store state. HOL has
no separate codec theorem; this supplies an executed-pass boundary obligation,
not an evaluation premise or a narrowed pass-correctness theorem. -/
theorem removeDead_decoderDomain {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (live : NumSet)
    (nlive : List WordStoreHOL) (frames : List (NumSet × NumSet))
    (accepted : decoderDomain program = true) :
    decoderDomain (removeDead program live nlive frames).1 = true := by
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing live nlive frames with
  | h program ih =>
    cases program
    case seq first second =>
      simp only [decoderDomain, Bool.and_eq_true] at accepted
      rcases secondRun : removeDead second live nlive frames with ⟨outSecond, liveSecond, storesSecond⟩
      have goodSecond := ih second (by change sizeOf second < sizeOf (WordLangProgHOL.seq first second); simp; omega)
        live nlive frames accepted.2
      simp only [secondRun] at goodSecond
      rcases firstRun : removeDead first liveSecond storesSecond frames with ⟨outFirst, liveFirst, storesFirst⟩
      have goodFirst := ih first (by change sizeOf first < sizeOf (WordLangProgHOL.seq first second); simp; omega)
        liveSecond storesSecond frames accepted.1
      simp only [firstRun] at goodFirst
      simp only [removeDead, secondRun, firstRun]
      split <;> simp_all [decoderDomain]
    case mustTerminate body =>
      rcases bodyRun : removeDead body live nlive frames with ⟨output, liveOutput, storesOutput⟩
      have good := ih body (by change sizeOf body < sizeOf (WordLangProgHOL.mustTerminate body); simp)
        live nlive frames (by simpa only [decoderDomain] using accepted)
      simpa only [removeDead, bodyRun, decoderDomain] using good
    case ite cmp register operand first second =>
      simp only [decoderDomain, Bool.and_eq_true] at accepted
      rcases firstRun : removeDead first live nlive frames with ⟨outFirst, liveFirst, storesFirst⟩
      rcases secondRun : removeDead second live nlive frames with ⟨outSecond, liveSecond, storesSecond⟩
      have goodFirst := ih first (by change sizeOf first < sizeOf (WordLangProgHOL.ite cmp register operand first second); simp; omega)
        live nlive frames accepted.1
      have goodSecond := ih second (by change sizeOf second < sizeOf (WordLangProgHOL.ite cmp register operand first second); simp; omega)
        live nlive frames accepted.2
      simp only [firstRun] at goodFirst
      simp only [secondRun] at goodSecond
      simp only [removeDead, firstRun, secondRun]
      split <;> simp_all [decoderDomain]
    case set store value =>
      cases value <;> simp only [removeDead] <;>
        repeat' first
          | simp_all +zetaDelta [decoderDomain]
          | split
    case call returns target arguments handler =>
      rcases returns with _ | ⟨values, cuts, body, label1, label2⟩ <;>
        rcases handler with _ | ⟨exception, handlerBody, handlerLabel1, handlerLabel2⟩ <;>
        simp only [removeDead] <;>
        simp_all +zetaDelta only [decoderDomain, Bool.and_eq_true]
      all_goals
        repeat' first
          | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
          | assumption
          | simp_all +zetaDelta
          | constructor
    all_goals
      try simp only [removeDead]
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta [decoderDomain]
        | split
        | constructor

/-- Decoder acceptance of the whole native pass is derived from input
acceptance. This is Flapjack codec infrastructure, not a HOL theorem port. -/
theorem removeDeadProg_decoder_isSome {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (accepted : (wordLangProgFromHOL program).isSome = true) :
    (wordLangProgFromHOL (removeDeadProg program)).isSome = true := by
  rw [decoderDomain_eq] at accepted ⊢
  exact removeDead_decoderDomain program .ln [] [] accepted

/-- Successful source encoding supplies decoder acceptance independently of
any target output. This native pass closure is Flapjack codec infrastructure. -/
theorem removeDeadProg_of_toHOL_decoder_isSome {width : Nat} [NeZero width]
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native) :
    (wordLangProgFromHOL (removeDeadProg native)).isSome = true :=
  removeDeadProg_decoder_isSome native
    (wordLangProgFromHOL_of_toHOL_isSome source native encoded)

/-- The actual router always takes its reviewed native branch on a successfully
encoded source. The output and its decoder success are derived, not assumed.
This is Flapjack production routing infrastructure; evaluator composition is
separate and no HOL pass-correctness tag is claimed. -/
theorem wordRemoveDeadProgramViaHOL_sourceNative {width : Nat} [NeZero width]
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native) :
    ∃ output : WordProg (BitVec width),
      wordLangProgFromHOL (removeDeadProg native) = some output ∧
      RiscV.wordRemoveDeadProgramViaHOL source = output := by
  have available := removeDeadProg_of_toHOL_decoder_isSome source native encoded
  cases decoded : wordLangProgFromHOL (removeDeadProg native) with
  | none => simp [decoded] at available
  | some output =>
    exact ⟨output, rfl,
      RiscV.wordRemoveDeadProgramViaHOL_native source native output encoded decoded⟩

end Flapjack.WordAlloc
