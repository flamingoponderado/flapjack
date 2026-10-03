import Flapjack.Compiler.Backend.StackRemove.Proofs.MemVal
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryWrites
import Flapjack.Compiler.Backend.StackRemove.StoreListCode
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Misc.WordList
import Flapjack.FiniteMap.MapKeys

/-! Execution of the initializer's store-list code,
`stack_removeProofScript.sml` (2636-2725).
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.StoreListCodeThm
open Flapjack Flapjack.Compiler.Backend.StackLang

-- This supplies only HOL type inhabitedness. Undefined FAPPLY results remain
-- the opaque holFapplyOutside; this instance does not choose a missing value.
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about the executed state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

set_option linter.unusedSimpArgs false in
/-- Native execution of one literal-word store step. Local factoring of the
original induction; no separate HOL declaration. -/
theorem inlStepRun {width : Nat} [NeZero width] {C F : Type}
    (a t : Nat) (value w : BitVec width) (s : StackSemStateFiniteExact width C F)
    (distinct : a ≠ t) (read : s.regs.lookup a = some (.word w)) (domain : s.mdomain w = true) :
    StackSemEvaluate.evaluate
      (listSeqHOL [.inst (.const t value), .inst (.mem .store t (.addr a 0)),
        addBytesInWordInst a], s) =
      (none, {s with
        memory := fun key => if key = w then .word value else s.memory key
        regs := (s.regs.updateEq (t, .word value)).updateEq (a, .word (w + bytesInWord width))}) := by
  simp [listSeqHOL, addBytesInWordInst,
    StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm,
    Encoders.Asm.HolRegImm.toWordRegImm, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    StackSemControl.fixClock, wordOpHOL, wordOp, read, distinct, Ne.symm distinct,
    StackSemStateOps.memStore, domain, wordSemBytesInWord, bytesInWord]

set_option linter.unusedSimpArgs false in
/-- Native execution of one register store step. Local factoring of the
original induction; no separate HOL declaration. -/
theorem inrStepRun {width : Nat} [NeZero width] {C F : Type}
    (a i : Nat) (value : WordLocW width) (w : BitVec width) (s : StackSemStateFiniteExact width C F)
    (read : s.regs.lookup a = some (.word w)) (source : s.regs.lookup i = some value)
    (domain : s.mdomain w = true) :
    StackSemEvaluate.evaluate
      (listSeqHOL [.inst (.mem .store i (.addr a 0)), addBytesInWordInst a], s) =
      (none, {s with
        memory := fun key => if key = w then value else s.memory key
        regs := s.regs.updateEq (a, .word (w + bytesInWord width))}) := by
  simp [listSeqHOL, addBytesInWordInst,
    StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm,
    Encoders.Asm.HolRegImm.toWordRegImm, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    StackSemControl.fixClock, wordOpHOL, wordOp, read, source,
    StackSemStateOps.memStore, domain, wordSemBytesInWord, bytesInWord]

/-- A sequence whose first part runs normally without changing the clock
continues with the second part. Local factoring; no separate HOL declaration. -/
theorem evaluateSeqNormal {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (s post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (first, s) = (none, post)) (clock : post.clock = s.clock) :
    StackSemEvaluate.evaluate (.seq first second, s) = StackSemEvaluate.evaluate (second, post) := by
  rw [StackSemEvaluate.evaluate_seq, run]
  cases post
  simp_all [StackSemControl.fixClock]

/-- `mem_val` agrees on register maps that agree on every register named by
the list. Local factoring; no separate HOL declaration. -/
theorem mapMemValCongr {width : Nat} [NeZero width]
    (regs regs' : HolFiniteMapExact Nat (WordLocW width)) (xs : List (BitVec width ⊕ Nat))
    (same : ∀ n, Sum.inr n ∈ xs → regs'.lookup n = regs.lookup n) :
    xs.map (MemVal.memVal regs') = xs.map (MemVal.memVal regs) := by
  apply List.map_congr_left
  intro x member
  cases x with
  | inl w => rfl
  | inr n => simp only [MemVal.memVal, holFapply, same n member]

/-- `write_fun2set` with the word-key decidable conditional used by the native
memory store. Local factoring; no separate HOL declaration. -/
private theorem writeWord {width : Nat} [NeZero width] (newValue oldValue : WordLocW width)
    (address : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (h : SetSep.star (SetSep.one (address, oldValue)) frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star frame (SetSep.one (address, newValue))
      (SetSep.fun2Set ((fun key => if key = address then newValue else memory key), domain)) := by
  have written := SetSep.writeFun2Set newValue address oldValue frame memory domain h
  convert written using 4
  rename_i key
  by_cases same : key = address <;> simp [same]

private theorem starRotate {α : Type} (one list frame : (α → Prop) → Prop) :
    SetSep.star (SetSep.star one list) frame = SetSep.star list (SetSep.star frame one) := by
  rw [← SetSep.starAssoc, SetSep.starComm one, SetSep.starAssoc]

/-- Complete original store-list execution theorem. Registers `a` and `t`,
the list, state, base word, frame, old payloads, memory and domain are
arbitrary; all original side conditions are kept, including the equations
naming the state memory and domain. The conclusion is the original existential
over the final temporary register value and memory, with the exact framed
heap of the stored values and the exact normal post-state. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "store_list_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem storeListCodeThm {width : Nat} [NeZero width] {C F : Type} (a t : Nat) :
    ∀ (xs : List (BitVec width ⊕ Nat)) (s : StackSemStateFiniteExact width C F)
      (w : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
      (ys : List (WordLocW width)) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Prop),
      SetSep.star (Misc.wordList w ys) frame (SetSep.fun2Set (m, dm)) ∧
        m = s.memory ∧ dm = (fun x => s.mdomain x = true) ∧
        ys.length = xs.length ∧ a ≠ t ∧
        StackSemStateOps.getVar a s = some (.word w) ∧ s.regs.lookup t ≠ none ∧
        (∀ x ∈ xs, ∀ n, Sum.inr n = x → n ≠ a ∧ n ≠ t ∧ s.regs.lookup n ≠ none) →
      ∃ r1 m1,
        SetSep.star (Misc.wordList w (xs.map (MemVal.memVal s.regs))) frame
          (SetSep.fun2Set (m1, fun x => s.mdomain x = true)) ∧
        StackSemEvaluate.evaluate (storeListCode a t xs, s) =
          (none, {s with
            memory := m1
            regs := s.regs.updateListEq
              [(a, .word (w + bytesInWord width * BitVec.ofNat width xs.length)), (t, r1)]}) := by
  intro xs
  induction xs with
  | nil =>
    rintro s w frame ys m dm ⟨heap, rfl, rfl, length, _, read, present, _⟩
    have ysNil : ys = [] := List.length_eq_zero_iff.mp length
    subst ysNil
    obtain ⟨value, tRead⟩ := Option.ne_none_iff_exists'.mp present
    refine ⟨value, s.memory, heap, ?_⟩
    have regsEq : s.regs.updateListEq
        [(a, .word (w + bytesInWord width *
          BitVec.ofNat width ([] : List (BitVec width ⊕ Nat)).length)), (t, value)] = s.regs := by
      apply HolFiniteMapExact.ext_lookup
      intro key
      simp only [StackSemStateOps.getVar] at read
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
        FUPDATE_HOL, List.length_nil, BitVec.mul_zero, BitVec.add_zero]
      by_cases kt : key = t
      · subst kt; simp [tRead]
      · by_cases ka : key = a
        · subst ka; simp [kt, read]
        · simp [kt, ka]
    rw [regsEq]
    simp only [storeListCode, StackSemEvaluate.evaluate_skip]
  | cons x xs ih =>
    rintro s w frame ys m dm ⟨heap, rfl, rfl, length, distinct, read, present, guard⟩
    cases ys with
    | nil => simp at length
    | cons y ys =>
    have tailLength : ys.length = xs.length := by simpa using length
    simp only [StackSemStateOps.getVar] at read
    rw [Misc.wordList, ← SetSep.starAssoc] at heap
    have inDomain : s.mdomain w = true := by
      rcases heap with ⟨left, right, partition, single, _⟩
      have member : SetSep.fun2Set (s.memory, fun x => s.mdomain x = true) (w, y) := by
        rw [← partition.1]
        exact Or.inl (by rw [single])
      exact ((SetSep.fun2SetThm _ _ w y).mp member).2
    have addressEq : w + bytesInWord width + bytesInWord width * BitVec.ofNat width xs.length =
        w + bytesInWord width * BitVec.ofNat width (xs.length + 1) := by
      rw [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one]
      ac_rfl
    have tailGuard : ∀ x' ∈ xs, ∀ n, Sum.inr n = x' → n ≠ a ∧ n ≠ t ∧ s.regs.lookup n ≠ none :=
      fun x' member => guard x' (List.mem_cons_of_mem x member)
    cases x with
    | inl v =>
      have written := writeWord (.word v) y w _ s.memory (fun x => s.mdomain x = true) heap
      rw [← SetSep.starAssoc] at written
      have run := inlStepRun a t v w s distinct read inDomain
      obtain ⟨r1, m1, tailHeap, tailRun⟩ := ih
        {s with
          memory := fun key => if key = w then .word v else s.memory key
          regs := (s.regs.updateEq (t, .word v)).updateEq (a, .word (w + bytesInWord width))}
        (w + bytesInWord width) _ ys _ _
        ⟨written, by rfl, by rfl, tailLength, distinct,
          by simp [StackSemStateOps.getVar, FUPDATE_HOL],
          by simp [FUPDATE_HOL, Ne.symm distinct],
          fun x' member n eq => by
            obtain ⟨na, nt, present⟩ := tailGuard x' member n eq
            exact ⟨na, nt, by simpa [FUPDATE_HOL, na, nt] using present⟩⟩
      refine ⟨r1, m1, ?_, ?_⟩
      · have same := mapMemValCongr s.regs
          ((s.regs.updateEq (t, .word v)).updateEq (a, .word (w + bytesInWord width))) xs
          (fun n member => by
            obtain ⟨na, nt, _⟩ := tailGuard _ member n rfl
            simp [FUPDATE_HOL, na, nt])
        rw [same] at tailHeap
        simp only [List.map_cons, MemVal.memVal, Misc.wordList, starRotate]
        exact tailHeap
      · simp only [storeListCode]
        rw [evaluateSeqNormal _ _ s _ run rfl, tailRun]
        have regsEq : (((s.regs.updateEq (t, .word v)).updateEq
            (a, .word (w + bytesInWord width))).updateListEq
              [(a, .word (w + bytesInWord width + bytesInWord width *
                BitVec.ofNat width xs.length)), (t, r1)]) =
            s.regs.updateListEq
              [(a, .word (w + bytesInWord width *
                BitVec.ofNat width (Sum.inl v :: xs).length)), (t, r1)] := by
          apply HolFiniteMapExact.ext_lookup
          intro key
          simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
            HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, List.length_cons, addressEq]
          by_cases kt : key = t
          · simp [kt]
          · by_cases ka : key = a
            · simp [ka]
            · simp [kt, ka]
        rw [regsEq]
    | inr i =>
      obtain ⟨ia, it, iPresent⟩ := guard (.inr i) List.mem_cons_self i rfl
      obtain ⟨value, source⟩ := Option.ne_none_iff_exists'.mp iPresent
      have written := writeWord value y w _ s.memory (fun x => s.mdomain x = true) heap
      rw [← SetSep.starAssoc] at written
      have run := inrStepRun a i value w s read source inDomain
      obtain ⟨r1, m1, tailHeap, tailRun⟩ := ih
        {s with
          memory := fun key => if key = w then value else s.memory key
          regs := s.regs.updateEq (a, .word (w + bytesInWord width))}
        (w + bytesInWord width) _ ys _ _
        ⟨written, by rfl, by rfl, tailLength, distinct,
          by simp [StackSemStateOps.getVar, FUPDATE_HOL],
          by simpa [FUPDATE_HOL, Ne.symm distinct] using present,
          fun x' member n eq => by
            obtain ⟨na, nt, present⟩ := tailGuard x' member n eq
            exact ⟨na, nt, by simpa [FUPDATE_HOL, na] using present⟩⟩
      refine ⟨r1, m1, ?_, ?_⟩
      · have same := mapMemValCongr s.regs
          (s.regs.updateEq (a, .word (w + bytesInWord width))) xs
          (fun n member => by
            obtain ⟨na, _, _⟩ := tailGuard _ member n rfl
            simp [FUPDATE_HOL, na])
        rw [same] at tailHeap
        have head : MemVal.memVal s.regs (.inr i) = value := holFapply_of_lookup source
        simp only [List.map_cons, head, Misc.wordList, starRotate]
        exact tailHeap
      · simp only [storeListCode]
        rw [evaluateSeqNormal _ _ s _ run rfl, tailRun]
        have regsEq : ((s.regs.updateEq (a, .word (w + bytesInWord width))).updateListEq
              [(a, .word (w + bytesInWord width + bytesInWord width *
                BitVec.ofNat width xs.length)), (t, r1)]) =
            s.regs.updateListEq
              [(a, .word (w + bytesInWord width *
                BitVec.ofNat width (Sum.inr i :: xs).length)), (t, r1)] := by
          apply HolFiniteMapExact.ext_lookup
          intro key
          simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
            HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, List.length_cons, addressEq]
          by_cases kt : key = t
          · simp [kt]
          · by_cases ka : key = a
            · simp [ka]
            · simp [kt, ka]
        rw [regsEq]

end Flapjack.Compiler.Backend.StackRemove.Proofs.StoreListCodeThm
