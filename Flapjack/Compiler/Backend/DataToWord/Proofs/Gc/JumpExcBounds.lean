import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcFrames
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

/-! Stack-size bounds after jumping to an exception handler. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- Adding optional nonnegative sizes bounds either summand. -/
theorem optionLe_wordSemOptionAdd_right (a b : Option Nat) : optionLe b (wordSemOptionAdd a b) := by
  cases a <;> cases b <;> simp [wordSemOptionAdd, optionLe]

/-- The left summand is bounded by the same optional sum. -/
theorem optionLe_wordSemOptionAdd_left (a b : Option Nat) : optionLe a (wordSemOptionAdd a b) := by
  cases a <;> cases b <;> simp [wordSemOptionAdd, optionLe]

/-- Dropping frames cannot increase the optional stack-size measure. -/
theorem wordStackSize_drop_le {width : Nat} [NeZero width]
    (stack : List (WordSemStackFrame width)) (count : Nat) :
    optionLe (wordSemStackSize (stack.drop count)) (wordSemStackSize stack) := by
  induction stack generalizing count with
  | nil => simp [wordSemStackSize, optionLe]
  | cons frame rest ih =>
    cases count with
    | zero => exact optionLe_refl _
    | succ count =>
      have tail := ih count
      have head : optionLe (wordSemStackSize rest) (wordSemStackSize (frame :: rest)) := by
        change optionLe (wordSemStackSize rest) (wordSemOptionAdd (wordSemStackSizeFrame frame) (wordSemStackSize rest))
        exact optionLe_wordSemOptionAdd_right _ _
      exact optionLe_trans _ _ _ ⟨by simpa using tail, head⟩

/-- Restoring an exception frame's locals uses no more space than that
frame and the remaining stack. -/
theorem wordStackSize_restore_handler_le {width : Nat} [NeZero width]
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width)) (saved l1 l2 : Nat)
    (rest : List (WordSemStackFrame width)) :
    optionLe (wordSemOptionAdd (wordSemStackSize rest) size)
      (wordSemStackSize (.stackFrame size nonGc gc (some (saved, l1, l2)) :: rest)) := by
  change optionLe (wordSemOptionAdd (wordSemStackSize rest) size)
    (wordSemOptionAdd (size.map (fun n => 3 + n)) (wordSemStackSize rest))
  generalize h : wordSemStackSize rest = total
  cases size <;> cases total <;> simp [wordSemOptionAdd, optionLe]
  omega

/-- The optional stack maximum remains a valid bound after a successful
target exception jump restores a handler's locals and drops frames. -/
theorem jumpExc_stackMaxBound {width : Nat} [NeZero width] {C F : Type}
    (target next : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (jump : WordSemStateFiniteExact.jumpExc target = some (next, l1, l2))
    (bound : optionLe (wordSemOptionAdd (wordSemStackSize target.stack) target.localsSize) target.stackMax) :
    optionLe (wordSemOptionAdd (wordSemStackSize next.stack) next.localsSize) next.stackMax := by
  have stackBound : optionLe (wordSemStackSize target.stack)
      (wordSemOptionAdd (wordSemStackSize target.stack) target.localsSize) := by
    exact optionLe_wordSemOptionAdd_left _ _
  have belowMax := optionLe_trans _ _ _ ⟨stackBound, bound⟩
  unfold WordSemStateFiniteExact.jumpExc at jump
  split at jump
  · rename_i valid
    rw [wordSemLastN_eq_drop] at jump
    cases dropped : target.stack.drop (target.stack.length - (target.handler + 1)) with
    | nil => simp [dropped] at jump
    | cons frame rest =>
      cases frame with
      | stackFrame size nonGc gc handler =>
        cases handler with
        | none => simp [dropped] at jump
        | some info =>
          obtain ⟨saved, a, b⟩ := info
          simp [dropped] at jump
          obtain ⟨rfl, rfl, rfl⟩ := jump
          have droppedBound := wordStackSize_drop_le target.stack (target.stack.length - (target.handler + 1))
          rw [dropped] at droppedBound
          have restored := wordStackSize_restore_handler_le size nonGc gc saved a b rest
          exact optionLe_trans _ _ _ ⟨restored, optionLe_trans _ _ _ ⟨droppedBound, belowMax⟩⟩
  · simp at jump

/-- Dropping matching stack prefixes cannot introduce a new memory root. -/
theorem flatStack_drop_subset {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (target : List (WordSemStackFrame width)) (count : Nat) :
    flatStack (source.drop count) (target.drop count) ⊆ flatStack source target := by
  induction source generalizing target count with
  | nil => simp [flatStack]
  | cons frame rest ih =>
    cases target with
    | nil => simp [flatStack]
    | cons targetFrame targetRest =>
      cases count with
      | zero => exact List.Subset.refl _
      | succ count =>
        have tail := ih targetRest count
        intro root member
        have inTail := tail member
        cases frame <;> cases targetFrame <;>
          simp only [flatStack, List.mem_append] <;> exact Or.inr inTail

/-- A successful data exception jump retains the suffix after its handler. -/
theorem dataJumpExc_stack_drop {C F : Type} (source next : DataSem.State C F)
    (jump : DataSem.jumpExc source = some next) :
    next.stack = source.stack.drop (source.stack.length - (source.handler + 1) + 1) := by
  unfold DataSem.jumpExc at jump
  split at jump
  · cases dropped : source.stack.drop (source.stack.length - (source.handler + 1)) with
    | nil => simp [dropped] at jump
    | cons frame rest =>
      cases frame with
      | env size env => simp [dropped] at jump
      | exc size env saved =>
        simp [dropped] at jump
        subst next
        rw [← List.drop_drop, dropped]
        rfl
  · simp at jump

/-- A successful word exception jump retains the suffix after its handler. -/
theorem wordJumpExc_stack_drop {width : Nat} [NeZero width] {C F : Type}
    (target next : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (jump : WordSemStateFiniteExact.jumpExc target = some (next, l1, l2)) :
    next.stack = target.stack.drop (target.stack.length - (target.handler + 1) + 1) := by
  unfold WordSemStateFiniteExact.jumpExc at jump
  split at jump
  · rw [wordSemLastN_eq_drop] at jump
    cases dropped : target.stack.drop (target.stack.length - (target.handler + 1)) with
    | nil => simp [dropped] at jump
    | cons frame rest =>
      cases frame with
      | stackFrame size nonGc gc handler =>
        cases handler with
        | none => simp [dropped] at jump
        | some info =>
          obtain ⟨saved, a, b⟩ := info
          simp [dropped] at jump
          obtain ⟨rfl, _, _⟩ := jump
          rw [← List.drop_drop, dropped]
          rfl
  · simp at jump

/-- Retained exception-stack roots were already roots of the related
pre-jump states. -/
theorem relatedJumpExc_flatStack_subset {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target targetNext : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (sourceJump : DataSem.jumpExc source = some next) (a b : Nat)
    (targetJump : WordSemStateFiniteExact.jumpExc target = some (targetNext, a, b)) :
    flatStack next.stack targetNext.stack ⊆ flatStack source.stack target.stack := by
  have handlerEq := related.2.2.1
  have lengths := related.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have same : target.stack.length - (target.handler + 1) + 1 =
      source.stack.length - (source.handler + 1) + 1 := by omega
  rw [dataJumpExc_stack_drop source next sourceJump, wordJumpExc_stack_drop target targetNext a b targetJump, same]
  exact flatStack_drop_subset source.stack target.stack _

/-- The global and retained stack roots still satisfy the pre-jump memory
relation. Restored local roots require a separate correspondence argument. -/
theorem relatedJumpExc_retained_memory {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target targetNext : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (sourceJump : DataSem.jumpExc source = some next) (a b : Nat)
    (targetJump : WordSemStateFiniteExact.jumpExc target = some (targetNext, a, b)) :
    Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((theGlobal source.global, holFapply target.store .globals) :: flatStack next.stack targetNext.stack) := by
  have subset := relatedJumpExc_flatStack_subset conf l1 l2 source next target targetNext locs related sourceJump a b targetJump
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, memory⟩
  apply Memory.memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ ?_ memory
  intro pair member
  simp only [Option.getD_none, List.nil_append, List.mem_cons] at member ⊢
  rcases member with global | root
  · simp [global]
  · simp [subset root]

/-- Related exception jumps preserve both the frame relations and the
target stack-maximum bound. Memory-root rearrangement is separate. -/
theorem stateRel64_jumpExc_frames_and_bound {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (jump : DataSem.jumpExc source = some next) :
    ∃ targetNext label1 label2 returnLoc remainingLocs,
      WordSemStateFiniteExact.jumpExc target = some (targetNext, label1, label2) ∧
      List.Forall₂ stackRel next.stack targetNext.stack ∧
      next.handler = targetNext.handler ∧ next.localsSize = targetNext.localsSize ∧
      locs.drop (target.stack.length - (target.handler + 1)) = returnLoc :: remainingLocs ∧
      List.Forall₂ containsLoc targetNext.stack remainingLocs ∧
      (∃ frame, target.stack.drop (target.stack.length - (target.handler + 1)) = frame :: targetNext.stack ∧
        containsLoc frame returnLoc) ∧
      optionLe (wordSemOptionAdd (wordSemStackSize targetNext.stack) targetNext.localsSize) targetNext.stackMax := by
  obtain ⟨targetNext, a, b, returnLoc, remaining, targetJump, stackRel, handler, size, locations, locationRel, frame⟩ :=
    stateRel64_jumpExc_frames conf l1 l2 source next target locs related jump
  have oldBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨targetNext, a, b, returnLoc, remaining, targetJump, stackRel, handler, size, locations,
    locationRel, frame, jumpExc_stackMaxBound target targetNext a b targetJump oldBound⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
