import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
import Flapjack.Compiler.Backend.Semantics.DataSem.Control
import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-! Exception-frame alignment for the candidate data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Dropping equally many frames preserves pairwise correspondence. -/
theorem forall₂_drop_frames {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (related : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction related generalizing n with
  | nil => simp
  | @cons x y xs ys pair tail ih =>
    cases n with
    | zero => exact .cons pair tail
    | succ n => simpa using ih n

/-- The word-language suffix operation is the corresponding drop. -/
theorem wordSemLastN_eq_drop {α : Type} (count : Nat) (xs : List α) :
    wordSemLastN count xs = xs.drop (xs.length - count) := by
  simp [wordSemLastN, List.take_reverse]

/-- If a related source stack reaches an exception frame, the target stack
reaches a matching exception frame and keeps related remaining frames. This
only establishes stack alignment; the memory-root and full state relation
needed for HOL's exception theorem are not asserted here. -/
theorem stateRel64_jumpExc_frames {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (jump : DataSem.jumpExc source = some next) :
    ∃ targetNext label1 label2 returnLoc remainingLocs,
      WordSemStateFiniteExact.jumpExc target = some (targetNext, label1, label2) ∧
      List.Forall₂ stackRel next.stack targetNext.stack ∧
      next.handler = targetNext.handler ∧ next.localsSize = targetNext.localsSize ∧
      locs.drop (target.stack.length - (target.handler + 1)) = returnLoc :: remainingLocs ∧
      List.Forall₂ containsLoc targetNext.stack remainingLocs ∧
      ∃ frame, target.stack.drop (target.stack.length - (target.handler + 1)) = frame :: targetNext.stack ∧
        containsLoc frame returnLoc := by
  rcases related with ⟨_, _, handlerEq, _, _, _, _, _, _, _, _, _, stackPairs, locationPairs, _⟩
  have lengths := stackPairs.length_eq
  have handlerBound : source.handler < source.stack.length := by
    by_contra notBound
    simp [DataSem.jumpExc, notBound] at jump
  cases dropped : source.stack.drop (source.stack.length - (source.handler + 1)) with
  | nil => simp [DataSem.jumpExc, handlerBound, dropped] at jump
  | cons frame rest =>
    cases frame with
    | env size env => simp [DataSem.jumpExc, handlerBound, dropped] at jump
    | exc size env saved =>
      simp [DataSem.jumpExc, handlerBound, dropped] at jump
      subst next
      have tailRel := forall₂_drop_frames stackPairs (source.stack.length - (source.handler + 1))
      rw [dropped] at tailRel
      cases targetDropped : target.stack.drop (target.stack.length - (target.handler + 1)) with
      | nil =>
        have sameDrop : target.stack.length - (target.handler + 1) =
            source.stack.length - (source.handler + 1) := by omega
        rw [← sameDrop, targetDropped] at tailRel
        cases tailRel
      | cons frame' rest' =>
        have sameDrop : target.stack.length - (target.handler + 1) =
            source.stack.length - (source.handler + 1) := by omega
        rw [← sameDrop, targetDropped] at tailRel
        cases tailRel with
        | cons headRel restRel =>
          cases frame' with
          | stackFrame size' nonGc gc handler =>
            cases handler with
            | none => simp [stackRel] at headRel
            | some info =>
              obtain ⟨saved', label1, label2⟩ := info
              simp only [stackRel] at headRel
              have sizeEq : size = size' := headRel.1.2.1
              have savedEq : saved' = saved := headRel.2
              have locationTail := forall₂_drop_frames locationPairs (target.stack.length - (target.handler + 1))
              rw [targetDropped] at locationTail
              cases locDrop : locs.drop (target.stack.length - (target.handler + 1)) with
              | nil => rw [locDrop] at locationTail; cases locationTail
              | cons returnLoc remainingLocs =>
                rw [locDrop] at locationTail
                cases locationTail with
                | cons locHead locRest =>
                  refine ⟨{ target with handler := saved', locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := rest', localsSize := size' }, label1, label2, returnLoc, remainingLocs, ?_, restRel, ?_, ?_, rfl, locRest, ?_⟩
                  · have targetBound : target.handler < target.stack.length := by omega
                    simp only [WordSemStateFiniteExact.jumpExc, if_pos targetBound, wordSemLastN_eq_drop, targetDropped]
                  · exact savedEq.symm
                  · exact sizeEq
                  · exact ⟨_, rfl, locHead⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
