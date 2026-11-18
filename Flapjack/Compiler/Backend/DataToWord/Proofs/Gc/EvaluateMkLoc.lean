module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackKeys
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
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
