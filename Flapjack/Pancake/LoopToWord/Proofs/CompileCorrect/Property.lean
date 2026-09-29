import Flapjack.Pancake.LoopToWord.Proofs.RelationsExact
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Misc.GoodDimindex

/-!
# Shared statement for exact `loop_to_word` `compile_correct` case ports

This module is Flapjack-specific proof organization for HOL `compile_correct`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:57-97`).  HOL states that
theorem as `loopSem$evaluate_ind` specialised to the lambda `goal`.  This
module renders two pieces of it:
* `resultCase` is the result-indexed `case res of ...` in the goal's
  conclusion;
* `PropertyAt prog s` is the whole goal at one `(prog, s)` pair.

The constructor case theorems carry the `compile_correct` reference.  They
use `PropertyAt` only for the induction hypotheses on sub-programs.  Neither
declaration has a separate HOL declaration, so both are untagged.

The carriers are all the tagged exact ports:
* the loopSem `evaluate` over `LoopSemStateFiniteExact`;
* the wordSem `evaluate` over `WordSemStateFiniteExact`;
* `comp` (`compHOL`), `state_rel`, `locals_rel` and `acc_vars`;
* `good_dimindex`, `isWord` and `jump_exc`.

HOL `domain a ⊆ domain b` is `∀ k, sptMem k a → sptMem k b`, and HOL `bool`
guards are `= true`.
-/

namespace Flapjack.LoopToWord.CompileCorrect

open Flapjack

/-- The `case res of ...` conjunct of HOL `compile_correct`'s goal
    (`loop_to_wordProofScript.sml:69-92`), for the source result `res`, the
    source final state `s1`, the initial target `t`, and the target result
    `res1` with final state `t1`. -/
def resultCase {width : Nat} [NeZero width] {C F : Type} (ctxt : Spt Nat)
    (retv : WordLocW width) (t : WordSemStateFiniteExact width C F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F)
    (res1 : Option (WordSemResult width)) (t1 : WordSemStateFiniteExact width C F) : Prop :=
  match res with
  | none =>
      loopToWordStateRelHOLExact s1 t1 ∧ res1 = none ∧ sptLookup 0 t1.locals = some retv ∧
        localsRelHOL ctxt s1.locals t1.locals ∧
        t1.stack = t.stack ∧ t1.handler = t.handler
  | some (.result v) =>
      loopToWordStateRelHOLExact s1 t1 ∧ res1 = some (.result retv v) ∧
        t1.stack = t.stack ∧ t1.handler = t.handler
  | some (.exception v) =>
      loopToWordStateRelHOLExact s1 t1 ∧
        (res1 ≠ some .error → ∃ u1 u2, res1 = some (.exception u1 u2)) ∧
        ∀ r l1 l2,
          WordSemStateFiniteExact.jumpExc { t1 with stack := t.stack, handler := t.handler } =
              some (r, l1, l2) →
            res1 = some (.exception (.loc l1 l2) v) ∧ r = t1
  | some (.break n) =>
      loopToWordStateRelHOLExact s1 t1 ∧ res1 = some (.break n) ∧
        sptLookup 0 t1.locals = some retv ∧
        localsRelHOL ctxt s1.locals t1.locals ∧
        t1.stack = t.stack ∧ t1.handler = t.handler
  | some (.continue n) =>
      loopToWordStateRelHOLExact s1 t1 ∧ res1 = some (.continue n) ∧
        sptLookup 0 t1.locals = some retv ∧
        localsRelHOL ctxt s1.locals t1.locals ∧
        t1.stack = t.stack ∧ t1.handler = t.handler
  | some .timeOut => res1 = some .timeOut
  | some (.finalFfi f) => res1 = some (.finalFfi f)
  | some .error => False

/-- HOL `compile_correct`'s `goal` at one `(prog, s)` pair
    (`loop_to_wordProofScript.sml:57-92`): the target state `t` is typed at
    the source FFI host `F`, with an arbitrary compiler-configuration type
    `C`. -/
def PropertyAt {width : Nat} [NeZero width] (C : Type) {F : Type}
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F) : Prop :=
  ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
    LoopSemStateFiniteExact.evaluate prog s = (res, s1) ∧ res ≠ some .error ∧
      loopToWordStateRelHOLExact s t ∧ localsRelHOL ctxt s.locals t.locals ∧
      sptLookup 0 t.locals = some retv ∧
      goodDimindex width ∧
      ¬ wordSemIsWordLoc retv = true ∧
      (∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt) →
    ∃ t1 res1,
      WordSemStateFiniteExact.evaluate (compHOL ctxt prog l).1 t = (res1, t1) ∧
        t1.ffi = s1.ffi ∧
        resultCase ctxt retv t res s1 res1 t1

end Flapjack.LoopToWord.CompileCorrect
