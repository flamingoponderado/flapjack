import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAGeneratedProgramCodec

namespace Flapjack.Compiler.Backend.WordAlloc

/-! Flapjack decoder-boundary facts for native SSA control and its entry prologue.
There is no HOL declaration for this cross-carrier availability property. These
lemmas do not assert the full pass simulation or its production routing. -/

theorem ssaReconcile_decoderClosure {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    (wordLangProgFromHOL (ssaReconcile (width := width) current target names)).isSome = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [wordLangProgFromHOL]

theorem setupSSA_decoderClosure {inputWidth outputWidth : Nat}
    [NeZero inputWidth] [NeZero outputWidth] (count limit : Nat)
    (program : WordLangProgHOL (BitVec inputWidth)) :
    (wordLangProgFromHOL (setupSSA (outputWidth := outputWidth) count limit program).1).isSome = true := by
  simp [setupSSA, wordLangProgFromHOL]

theorem ssaCcTrans_break_decoderClosure {width : Nat} [NeZero width]
    (label : Nat) (ssa : Spt Nat) (next : Nat) (contexts : List (Spt Nat × Spt Unit × Spt Unit)) :
    (wordLangProgFromHOL (ssaCcTrans (width := width) (.break label) ssa next contexts).1).isSome = true := by
  simp only [ssaCcTrans]
  cases h : contexts[label]? with
  | none => simp [wordLangProgFromHOL]
  | some context =>
    rcases context with ⟨target, names, exits⟩
    simp only
    have accepted := ssaReconcile_decoderClosure (width := width) ssa target exits
    generalize hm : ssaReconcile (width := width) ssa target exits = moves at accepted ⊢
    cases moves <;> solve
      | simp [wordLangProgFromHOL]
      | exact ssaGeneratedSeq_decoderClosure _ _ accepted (by simp [wordLangProgFromHOL])

theorem ssaCcTrans_continue_decoderClosure {width : Nat} [NeZero width]
    (label : Nat) (ssa : Spt Nat) (next : Nat) (contexts : List (Spt Nat × Spt Unit × Spt Unit)) :
    (wordLangProgFromHOL (ssaCcTrans (width := width) (.continue label) ssa next contexts).1).isSome = true := by
  simp only [ssaCcTrans]
  cases h : contexts[label]? with
  | none => simp [wordLangProgFromHOL]
  | some context =>
    rcases context with ⟨target, names, exits⟩
    simp only
    have accepted := ssaReconcile_decoderClosure (width := width) ssa target names
    generalize hm : ssaReconcile (width := width) ssa target names = moves at accepted ⊢
    cases moves <;> solve
      | simp [wordLangProgFromHOL]
      | exact ssaGeneratedSeq_decoderClosure _ _ accepted (by simp [wordLangProgFromHOL])

end Flapjack.Compiler.Backend.WordAlloc
