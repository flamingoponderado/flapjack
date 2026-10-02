import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreHeapWrites
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
namespace Flapjack.Compiler.Backend.StackRemove.StackHeapWrites
open Flapjack Flapjack.Compiler.Backend.StackRemove
/-- Flapjack source-local factoring: expose a bounded forward-list slot and
retain exactly the same heap frame for every replacement value. No separately
named HOL declaration is claimed. -/
theorem wordListSlotSurgery {width : Nat} [NeZero width] {β : Type}
    (base : BitVec width) (values : List β) (index : Nat)
    (bound : index < values.length) :
    ∃ frame,
      Misc.wordList base values =
        SetSep.star (SetSep.one (base + bytesInWord width * BitVec.ofNat width index, values[index])) frame ∧
      ∀ value, Misc.wordList base (values.set index value) =
        SetSep.star (SetSep.one (base + bytesInWord width * BitVec.ofNat width index, value)) frame := by
  induction values generalizing base index with
  | nil => simp at bound
  | cons head values ih =>
    cases index with
    | zero =>
      refine ⟨Misc.wordList (base + bytesInWord width) values, ?_, ?_⟩
      · simp [Misc.wordList]
      · intro value
        simp [Misc.wordList]
    | succ index =>
      have smaller : index < values.length := by simpa using bound
      obtain ⟨frame, original, replacements⟩ := ih (base + bytesInWord width) index smaller
      have addressEq : base + bytesInWord width + bytesInWord width * BitVec.ofNat width index =
          base + bytesInWord width * BitVec.ofNat width (index + 1) := by
        simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_comm, BitVec.add_assoc]
      rw [addressEq] at original replacements
      refine ⟨SetSep.star (SetSep.one (base, head)) frame, ?_, ?_⟩
      · simp only [Misc.wordList, List.getElem_cons_succ, original]
        rw [SetSep.starAssoc, SetSep.starComm (SetSep.one (base, head)), ← SetSep.starAssoc]
      · intro value
        simp only [List.set_cons_succ, Misc.wordList, replacements]
        rw [SetSep.starAssoc, SetSep.starComm (SetSep.one (base, head)), ← SetSep.starAssoc]

open Classical in
/-- Full original framed stack-list write on arbitrary payloads, memory functions,
domains and predicate heaps. The old heap supplies all functional-frame facts. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_write"
  (words_as_type_indexed_bitvec)]
theorem stackWrite {width : Nat} [NeZero width] {β : Type}
    (values : List β) (base : BitVec width)
    (frame : ((BitVec width × β) → Prop) → Prop)
    (memory : BitVec width → β) (domain : BitVec width → Prop)
    (index : Nat) (value : β)
    (hypothesis : SetSep.star (Misc.wordList base values) frame (SetSep.fun2Set (memory, domain)) ∧
      index < values.length) :
    SetSep.star (Misc.wordList base (values.set index value)) frame
      (SetSep.fun2Set ((fun key => if key = base + bytesInWord width * BitVec.ofNat width index
        then value else memory key), domain)) := by
  rcases hypothesis with ⟨heaps, bound⟩
  obtain ⟨rest, original, replacements⟩ := wordListSlotSurgery base values index bound
  rw [original, ← SetSep.starAssoc] at heaps
  rw [replacements value, ← SetSep.starAssoc]
  have written := SetSep.writeFun2Set value (base + bytesInWord width * BitVec.ofNat width index)
    values[index] (SetSep.star rest frame) memory domain heaps
  rw [SetSep.starComm] at written
  have functionEq : (fun key => if key = base + bytesInWord width * BitVec.ofNat width index
      then value else memory key) =
      (fun key => @ite β (key = base + bytesInWord width * BitVec.ofNat width index)
        (Classical.propDecidable _) value (memory key)) := by
    funext key
    by_cases same : key = base + bytesInWord width * BitVec.ofNat width index <;>
      simp only [same, ite_true, ite_false]
  rw [← functionEq] at written
  exact written
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original stack-store relation transition, retaining all five original
hypothesis conjuncts and deriving every post-state relation conjunct. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_stack_store"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelStackStore {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (stack : List (WordLocW width)) (pointerWord address : BitVec width) (value : WordLocW width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧ stack = source.stack ∧
      target.regs.lookup pointer = some (.word pointerWord) ∧
      source.stackSpace + count < stack.length ∧
      pointerWord + bytesInWord width * BitVec.ofNat width count = address) :
    stateRelHOL jump bounds pointer {source with stack := stack.set (count + source.stackSpace) value}
      {target with memory := fun key => if key = address then value else target.memory key} := by
  rcases hypothesis with ⟨relation, stackEq, pointerLookup, safe, addressEq⟩
  subst stack
  obtain ⟨base, baseLookup, lower, upper, originalPointer, heaps⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at originalPointer
  have pointerEq : pointerWord = base + bytesInWord width * BitVec.ofNat width source.stackSpace :=
    WordLocW.word.inj (Option.some.inj (pointerLookup.symm.trans originalPointer))
  have writtenAddress : base + bytesInWord width * BitVec.ofNat width (count + source.stackSpace) = address := by
    rw [← addressEq, pointerEq]
    simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
    rw [BitVec.add_comm (bytesInWord width * BitVec.ofNat width count)]
  rw [SetSep.starComm] at heaps
  have written := stackWrite source.stack base _ target.memory
    (fun key => target.mdomain key = true) (count + source.stackSpace) value
    ⟨heaps, by simpa only [Nat.add_comm] using safe⟩
  rw [SetSep.starComm, writtenAddress] at written
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  simp only [stateRelHOL, List.length_set, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,
    h25.1,lower,upper,originalPointer,written⟩
end Flapjack.Compiler.Backend.StackRemove.StackHeapWrites
