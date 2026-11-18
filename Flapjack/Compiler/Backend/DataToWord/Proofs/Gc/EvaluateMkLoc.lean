module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackKeys
public import Flapjack.Compiler.Backend.DataToWord.Variables
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
@[expose] public section

/-! Exception locations after normal word evaluation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.WordSemStackEq WordSemStateFiniteExact

/-- The HOL proof uses stack-key equality to compare exception destinations;
this local helper packages that comparison for related stacks and handlers. -/
private theorem mkLocJumpKeyEq {width : Nat} [NeZero width] {C F : Type}
    (s t : WordSemStateFiniteExact width C F)
    (keys : sKeyEq s.stack t.stack) (handlers : s.handler = t.handler) :
    mkLoc (width := width) (jumpExc s) = mkLoc (width := width) (jumpExc t) := by
  have lengths := sKeyEqLength s.stack t.stack keys
  have suffix := sKeyEqLastN s.stack t.stack (s.handler + 1) keys
  unfold jumpExc
  rw [← handlers, ← lengths]
  split
  · generalize h1 : wordSemLastN (s.handler + 1) s.stack = xs at suffix ⊢
    generalize h2 : wordSemLastN (s.handler + 1) t.stack = ys at suffix ⊢
    cases xs with
    | nil => cases ys <;> simp_all [sKeyEq, mkLoc]
    | cons x xs =>
      cases ys with
      | nil => simp [sKeyEq] at suffix
      | cons y ys =>
        cases x with
        | stackFrame m a b h =>
          cases y with
          | stackFrame n c d k =>
            cases h <;> cases k <;> simp_all [sKeyEq, sFrameKeyEq, mkLoc]
  · rfl

namespace evaluateMkLocMap
/-- Canonical finite-map target-state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end evaluateMkLocMap

/-- Normal evaluation preserves the location selected by exception unwinding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "evaluate_mk_loc_EQ"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_mkLoc {width : Nat} [NeZero width] {C F : Type}
    (q : WordLangProgHOL (BitVec width)) (t t1 : WordSemStateFiniteExact width C F)
    (run : evaluate q t = (none, t1)) :
    mkLoc (width := width) (jumpExc t1) = mkLoc (width := width) (jumpExc t) := by
  have post := evaluateStackSwap q t
  simp only [stackSwapPost, run] at post
  exact (mkLocJumpKeyEq t t1 post.1 post.2.1.symm).symm
/-- A caught exception after a pushed handler preserves the prior unwind location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "mk_loc_eq_push_env_exc_Exception"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mkLoc_pushEnv_exception {width : Nat} [NeZero width] {C F : Type}
    (c : WordLangProgHOL (BitVec width)) (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (x0 x1 l : Nat)
    (prog1 : WordLangProgHOL (BitVec width)) (t t1 : WordSemStateFiniteExact width C F)
    (xx w : WordLocW width)
    (run : evaluate c (WordSemStateFiniteExact.callEnv args ss (pushEnv envs (some (x0,prog1,x1,l)) (decClock t))) =
      (some (.exception xx w), t1)) :
    mkLoc (width := width) (jumpExc t1) = mkLoc (width := width) (jumpExc t) := by
  have post := evaluateStackSwap c (WordSemStateFiniteExact.callEnv args ss (pushEnv envs (some (x0,prog1,x1,l)) (decClock t)))
  simp only [stackSwapPost, run] at post
  cases envList : wordSemEnvToList envs.2 t.permute with
  | mk entries perm =>
    simp only [WordSemStateFiniteExact.callEnv, pushEnv, decClock, envList] at post
    obtain ⟨_, e0, e, n, ls, m, lss, head, mEq, envEq, keys, handlerEq, transport⟩ := post
    have suffix : wordSemLastN (t.stack.length + 1)
        (.stackFrame t.localsSize (sptToAList envs.1) entries (some (t.handler, x1, l)) :: t.stack) =
        .stackFrame t.localsSize (sptToAList envs.1) entries (some (t.handler, x1, l)) :: t.stack := by
      apply lastNLengthCond
      simp
    rw [suffix] at head
    have frameEq := (List.cons.inj head).1
    have tailEq := (List.cons.inj head).2
    have handlerVal : some (t.handler, x1, l) = some n :=
      congrArg (fun frame => match frame with | .stackFrame _ _ _ h => h) frameEq
    have handlerVal' := Option.some.inj handlerVal
    rw [← handlerVal'] at handlerEq
    rw [← tailEq] at keys
    exact mkLocJumpKeyEq t1 t keys handlerEq

/-- Unwinding immediately after installing a handler selects its saved location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "mk_loc_jump_exc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mkLoc_jumpExc {width : Nat} {outWidth : Nat} [NeZero width] [NeZero outWidth] {C F : Type}
    (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (n x0 l : Nat)
    (prog1 : WordLangProgHOL (BitVec width)) (t : WordSemStateFiniteExact width C F) :
    mkLoc (width := outWidth) (jumpExc (WordSemStateFiniteExact.callEnv args ss
      (pushEnv envs (some (Flapjack.Compiler.Backend.DataToWord.adjustVar n, prog1, x0, l)) (decClock t)))) = .loc x0 l := by
  cases envList : wordSemEnvToList envs.2 t.permute with
  | mk entries perm =>
    simp [WordSemStateFiniteExact.callEnv, pushEnv, decClock, envList, jumpExc,
      wordSemLastN, List.take_of_length_le, mkLoc]

/-- Stack-key and handler equality preserve the presence of an unwind target. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "s_key_eq_handler_eq_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExc_keyEq_iff {width : Nat} [NeZero width] {C F D G : Type}
    (t : WordSemStateFiniteExact width C F) (t1 : WordSemStateFiniteExact width D G)
    (premises : sKeyEq t.stack t1.stack ∧ t.handler = t1.handler) :
    (jumpExc t1 ≠ none ↔ jumpExc t ≠ none) := by
  obtain ⟨keys, handlers⟩ := premises
  have lengths := sKeyEqLength t.stack t1.stack keys
  have suffix := sKeyEqLastN t.stack t1.stack (t.handler + 1) keys
  unfold jumpExc
  rw [← handlers, ← lengths]
  split
  · generalize h1 : wordSemLastN (t.handler + 1) t.stack = xs at suffix ⊢
    generalize h2 : wordSemLastN (t.handler + 1) t1.stack = ys at suffix ⊢
    cases xs with
    | nil => cases ys <;> simp_all [sKeyEq]
    | cons x xs =>
      cases ys with
      | nil => simp [sKeyEq] at suffix
      | cons y ys =>
        cases x with
        | stackFrame m a b h =>
          cases y with
          | stackFrame n c d k =>
            cases h <;> cases k <;> simp_all [sKeyEq, sFrameKeyEq]
  · simp

/-- Normal evaluation preserves whether exception unwinding fails. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "eval_NONE_IMP_jump_exc_NONE_EQ"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_jumpExc_none_iff {width : Nat} [NeZero width] {C F : Type}
    (q : WordLangProgHOL (BitVec width)) (t t1 : WordSemStateFiniteExact width C F)
    (run : evaluate q t = (none, t1)) :
    (jumpExc t1 = none ↔ jumpExc t = none) := by
  have post := evaluateStackSwap q t
  simp only [stackSwapPost, run] at post
  have eq := jumpExc_keyEq_iff t t1 ⟨post.1, post.2.1.symm⟩
  by_cases h1 : jumpExc t1 = none <;> by_cases h2 : jumpExc t = none <;> simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
