import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap
import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames
import Lean.Elab.Tactic.Omega

namespace Flapjack.WordToStackProofs
open Flapjack WordSemStackEq

/-- Flapjack key-projection infrastructure for the adjacent native sortedness
predicate. No separate HOL original is attached to this normalization. -/
private theorem adjacentKeys {α : Type} (xs : List (Nat × α)) :
    (xs.zip xs.tail).all (fun (x,y) => decide (x.1 > y.1)) =
      ((xs.map Prod.fst).zip (xs.map Prod.fst).tail).all
        (fun (x,y) => decide (x > y)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simpa using congrArg (fun b => decide (x.1 > y.1) && b) ih

/-- Flapjack transport of handler flags along the reviewed frame key relation;
no separate HOL declaration is attached to this generic relation helper. -/
private theorem frameKeyHandler {width : Nat} [NeZero width]
    (x y : WordSemStackFrame width) (h : sFrameKeyEq x y) :
    isHandlerFrame x = isHandlerFrame y := by
  cases x with
  | stackFrame n l0 l handler =>
    cases y with
    | stackFrame n' l0' l' handler' =>
      cases handler <;> cases handler' <;> simp_all [sFrameKeyEq, isHandlerFrame]

/-- Flapjack list transport of the handler predicates along actual frame keys;
no separate HOL original. -/
private theorem keyHandlerMap {width : Nat} [NeZero width]
    (xs ys : List (WordSemStackFrame width)) (h : sKeyEq xs ys) :
    xs.map isHandlerFrame = ys.map isHandlerFrame := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [sKeyEq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [sKeyEq] at h
    | cons y ys =>
      simp only [sKeyEq] at h
      simp only [List.map_cons, frameKeyHandler x y h.2, ih ys h.1]

/-- Full original handler flag equivalence under the original source index bound.
HOL EL is represented by the native bounded accessor only under that bound;
the target bound is derived from the actual decoder's reviewed key/length
preservation, rather than added as a hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_stack_dec_stack_shape"
  (words_as_type_indexed_bitvec)]
theorem wordStackDecStackShape {width : Nat} [NeZero width]
    (ls : List (WordLocW width)) (wstack res : List (WordSemStackFrame width))
    (n : Nat) (h : wordSemDecStack ls wstack = some res) (hn : n < wstack.length) :
    isHandlerFrame wstack[n] = true ↔
      isHandlerFrame (res[n]'(by
        rw [← sKeyEqLength wstack res (decStackStackKeyEq ls wstack res h)]
        exact hn)) = true := by
  have he := keyHandlerMap wstack res (decStackStackKeyEq ls wstack res h)
  have ho := congrArg (fun xs => xs[n]?) he
  simpa [List.getElem?_eq_getElem hn,
    List.getElem?_eq_getElem (by rw [← sKeyEqLength wstack res (decStackStackKeyEq ls wstack res h)]; exact hn)] using
    congrArg (fun o => o = some true) ho

/-- Full original sorted GC-key preservation when equal-length values replace
an arbitrary frame's GC values. No distinctness or stronger sortedness premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "sorted_env_zip"
  (words_as_type_indexed_bitvec)]
theorem sortedEnvZip {width : Nat} [NeZero width]
    (l l0 : List (Nat × WordLocW width)) (ls : List (WordLocW width))
    (x : Option (Nat × Nat × Nat)) (n : Option Nat)
    (hs : sortedEnv (.stackFrame n l0 l x) = true) (hlen : ls.length = l.length) :
    sortedEnv (.stackFrame n l0 ((l.map Prod.fst).zip ls) x) = true := by
  simp only [sortedEnv, adjacentKeys] at hs ⊢
  have hk : ((l.map Prod.fst).zip ls).map Prod.fst = l.map Prod.fst := by
    rw [List.map_fst_zip]
    simp [hlen]
  rw [hk]
  exact hs

/-- Flapjack sortedness transport along the reviewed frame key relation;
no separate HOL original. -/
private theorem frameKeySorted {width : Nat} [NeZero width]
    (x y : WordSemStackFrame width) (h : sFrameKeyEq x y) :
    sortedEnv x = sortedEnv y := by
  cases x with
  | stackFrame n l0 l handler =>
    cases y with
    | stackFrame n' l0' l' handler' =>
      rw [sFrameKeyEqDef2] at h
      simp only [sortedEnv, adjacentKeys]
      rw [h.1]

/-- Flapjack all-frame sortedness transport from the actual key relation;
no separate HOL original. -/
private theorem keySortedAll {width : Nat} [NeZero width]
    (xs ys : List (WordSemStackFrame width)) (h : sKeyEq xs ys) :
    xs.all sortedEnv = ys.all sortedEnv := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [sKeyEq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [sKeyEq] at h
    | cons y ys =>
      simp only [sKeyEq] at h
      simp only [List.all_cons, frameKeySorted x y h.2, ih ys h.1]

/-- Full original successful decoder preservation of every frame's sortedness,
with exactly the original successful decode and EVERY sorted_env hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_stack_dec_stack_sorted"
  (words_as_type_indexed_bitvec)]
theorem wordStackDecStackSorted {width : Nat} [NeZero width]
    (ls : List (WordLocW width)) (wstack res : List (WordSemStackFrame width))
    (h : wordSemDecStack ls wstack = some res) (hs : wstack.all sortedEnv = true) :
    res.all sortedEnv = true := by
  rw [← keySortedAll wstack res (decStackStackKeyEq ls wstack res h)]
  exact hs

end Flapjack.WordToStackProofs
