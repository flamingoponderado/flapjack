import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLengths
import Flapjack.Misc.ListEl

/-!
# Word-to-Stack returning-call support lemmas

Stack-relation and list facts used by the returning `Call` cases of
`comp_correct` (`word_to_stackProofScript.sml`): `LLOOKUP_TAKE` (308-312),
`state_rel_IMP_LENGTH` (5260-5268), `stack_rel_DROP_NONE` (5368-5396),
`stack_rel_cons_LEN_NONE` (5409-5423) and `stack_rel_cons_locals_size`
(5425-5440).
-/

namespace Flapjack.WordToStackProofs.CallReturnSupport
open Flapjack.Compiler.Encoders.Asm

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Inhabitation of the source frame carrier for total HOL `EL`, as in `stackRelAux`. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Exact HOL `LLOOKUP_TAKE` (`word_to_stackProofScript.sml:308-312`); HOL
`LLOOKUP` is native optional indexing. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LLOOKUP_TAKE"]
theorem llookupTake {α : Type} (n f : Nat) (xs : List α) :
    n < f → (xs.take f)[n]? = xs[n]? := by
  intro h
  rw [List.getElem?_take, if_pos h]

/-- Exact HOL `state_rel_IMP_LENGTH` (`word_to_stackProofScript.sml:5260-5268`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelImpLength {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) (extra : Nat) :
    stateRel ac k f f' s t lens extra → lens.length = s.stack.length := by
  intro h
  unfold stateRel at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, ⟨-, astack, habs, -, -⟩, -⟩ := h
  exact (absStackImpLength _ _ _ _ _ habs).2

/-- Shape of a successful abstraction of a stack headed by a handler-free
frame. Flapjack helper; no separate HOL original. -/
theorem absStack_cons_none {width frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (n : Option Nat) (l0 l : List (Nat × WordLocW frameWidth))
    (wstack : List (WordSemStackFrame frameWidth)) (sstack : List (WordLocW width))
    (f' : Nat) (lens : List Nat)
    (astack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : absStack bs (.stackFrame n l0 l none :: wstack) sstack (f' :: lens) = some astack) :
    ∃ w rest bits ys, sstack = w :: rest ∧ StackSem.fullReadBitmap bs w = some bits ∧
      bits.length = f' ∧ f' ≤ rest.length ∧
      absStack bs wstack (rest.drop f') lens = some ys ∧
      astack = (none, bits, rest.take f') :: ys := by
  rcases sstack with _ | ⟨w, rest⟩
  · rw [absStack.eq_def] at h; simp at h
  rw [absStack.eq_def] at h
  simp only at h
  rcases hb : StackSem.fullReadBitmap bs w with _ | bits
  · simp [hb] at h
  simp only [hb] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hlen hrest
  rcases hys : absStack bs wstack (rest.drop f') lens with _ | ys
  · simp [hys] at h
  simp only [hys, Option.some.injEq] at h
  exact ⟨w, rest, bits, ys, rfl, hb, by simpa using hlen, by omega, hys, h.symm⟩

/-- Exact HOL `stack_rel_cons_LEN_NONE` (`word_to_stackProofScript.sml:5409-5423`).
HOL's free variables are explicit; the target handler word has its own
dimension, as in `stack_rel_def`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_cons_LEN_NONE"
  (words_as_type_indexed_bitvec)]
theorem stackRelConsLenNone {width : Nat} {handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (wstack : List (WordSemStackFrame width)) (shandler : Option (WordLocW handlerWidth))
    (sstack : List (WordLocW width)) (len : Nat) (bs : List (BitVec width)) (f' : Nat)
    (lens : List Nat) :
    stackRel k whandler (.stackFrame n l0 l none :: wstack) shandler sstack len bs (f' :: lens) →
      f' + 1 ≤ sstack.length := by
  rintro ⟨-, astack, habs, -, -⟩
  obtain ⟨w, rest, bits, ys, rfl, -, -, hle, -, -⟩ :=
    absStack_cons_none bs n l0 l wstack sstack f' lens astack habs
  simp only [List.length_cons]
  omega

/-- Exact HOL `stack_rel_cons_locals_size` (`word_to_stackProofScript.sml:5425-5440`).
HOL `the (f' + 1) n` is `n.getD (f' + 1)`; the head frame's handler is arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_cons_locals_size"
  (words_as_type_indexed_bitvec)]
theorem stackRelConsLocalsSize {width : Nat} {handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (opt : Option (Nat × Nat × Nat)) (t'' : List (WordSemStackFrame width))
    (shandler : Option (WordLocW handlerWidth)) (restOfStack : List (WordLocW width))
    (len : Nat) (bitmaps : List (BitVec width)) (f' : Nat) (lens : List Nat) :
    stackRel k whandler (.stackFrame n l0 l opt :: t'') shandler restOfStack len bitmaps
        (f' :: lens) →
      n.getD (f' + 1) = f' + 1 := by
  rintro ⟨-, astack, habs, -, haux⟩
  rcases opt with _ | ⟨h1, l1, l2⟩
  · obtain ⟨w, rest, bits, ys, rfl, -, -, hle, -, rfl⟩ :=
      absStack_cons_none bitmaps n l0 l t'' restOfStack f' lens astack habs
    simp only [stackRelAux] at haux
    have := haux.2.2.1
    rwa [List.length_take, Nat.min_eq_left hle] at this
  · rcases restOfStack with _ | ⟨w, rest⟩
    · rw [absStack.eq_def] at habs; simp at habs
    rw [absStack.eq_def] at habs
    simp only at habs
    split at habs
    · simp at habs
    rcases rest with _ | ⟨loc, _ | ⟨hv, _ | ⟨w', stack⟩⟩⟩ <;> simp only [reduceCtorEq] at habs
    rcases hb : StackSem.fullReadBitmap bitmaps w' with _ | bits
    · simp [hb] at habs
    simp only [hb] at habs
    split at habs
    · simp at habs
    split at habs
    · simp at habs
    rename_i hlen hrest
    rcases hys : absStack bitmaps t'' (stack.drop f') lens with _ | ys
    · simp [hys] at habs
    simp only [hys, Option.some.injEq] at habs
    subst habs
    simp only [stackRelAux] at haux
    have := haux.2.2.2.2.1
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this

/-- Exact HOL `stack_rel_DROP_NONE` (`word_to_stackProofScript.sml:5368-5396`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_DROP_NONE"
  (words_as_type_indexed_bitvec)]
theorem stackRelDropNone {width : Nat} {handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (wstack : List (WordSemStackFrame width)) (shandler : Option (WordLocW handlerWidth))
    (sstack : List (WordLocW width)) (len : Nat) (bs : List (BitVec width)) (f' : Nat)
    (lens : List Nat) :
    stackRel k whandler (.stackFrame n l0 l none :: wstack) shandler sstack len bs (f' :: lens) →
      stackRel k whandler wstack shandler (sstack.drop (f' + 1)) len bs lens := by
  rintro ⟨hsorted, astack, habs, hH, haux⟩
  obtain ⟨w, rest, bits, ys, rfl, -, -, hle, hys, rfl⟩ :=
    absStack_cons_none bs n l0 l wstack _ f' lens astack habs
  have hysLen : ys.length = wstack.length := (absStackImpLength _ _ _ _ _ hys).1
  simp only [stackRelAux] at haux
  refine ⟨?_, ys, by simpa using hys, ?_, haux.2.2.2⟩
  · simp only [List.all_cons, Bool.and_eq_true] at hsorted
    exact hsorted.2
  · intro hlt hhf
    have hH' := hH (by simp; omega) (by
      simp only [List.length_cons]
      rw [show wstack.length + 1 - (whandler + 1) = (wstack.length - (whandler + 1)) + 1 by omega,
        holEl_cons_succ]
      exact hhf)
    rw [hH']
    simp only [List.length_cons]
    rw [show ys.length + 1 - (whandler + 1) = (ys.length - (whandler + 1)) + 1 by omega,
      List.drop_succ_cons]

theorem holLast_mem {α : Type} [Nonempty α] : ∀ l : List α, l ≠ [] → holLast l ∈ l
  | [], h => absurd rfl h
  | [x], _ => by simp [holLast]
  | x :: y :: z, _ => by
      rw [holLastCons.2]
      exact List.mem_cons_of_mem x (holLast_mem (y :: z) (by simp))

/-- Exact HOL `LAST_GENLIST_evens` (`word_to_stackProofScript.sml:5398-5407`). HOL
`GENLIST f n` is `(List.range n).map f`, `LAST` is the `holLast` port and `EVEN`
is `% 2 = 0`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LAST_GENLIST_evens"]
theorem lastGenlistEvens (n : Nat) :
    n ≠ 0 →
      let reg := holLast ((List.range n).map (fun x => 2 * (x + 1)))
      reg ≠ 0 ∧ reg % 2 = 0 := by
  intro hn
  have hne : (List.range n).map (fun x => 2 * (x + 1)) ≠ [] := by
    simp [List.range_eq_nil, hn]
  obtain ⟨x, -, hx⟩ := List.mem_map.mp (holLast_mem _ hne)
  simp only
  rw [← hx]
  omega

end Flapjack.WordToStackProofs.CallReturnSupport
