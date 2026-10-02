import Flapjack.Compiler.Backend.StackRemove.Proofs.StackPointer
namespace Flapjack.Compiler.Backend.StackRemove.StackHeap
open Flapjack Flapjack.Compiler.Backend.StackRemove
/-- Flapjack proof factoring for the empty-prefix case of the append theorem;
no standalone HOL declaration is claimed. -/
theorem starEmptyLeft {α : Type} (p : (α → Prop) → Prop) : SetSep.star SetSep.emp p = p := by
  funext heap
  apply propext
  constructor
  · rintro ⟨first, second, partition, empty, assertion⟩
    rw [empty] at partition
    have same : second = heap := by
      funext entry
      simpa using congrFun partition.1 entry
    simpa only [same] using assertion
  · intro assertion
    exact ⟨(fun _ => False), heap, ⟨by funext entry; simp, by simp⟩, rfl, assertion⟩
/-- Full original forward-list heap append equality, for arbitrary payloads
and predicate heaps, with only the reviewed positive word-width translation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_APPEND"
  (words_as_type_indexed_bitvec)]
theorem wordListAppend {width : Nat} [NeZero width] {β : Type}
    (first second : List β) (base : BitVec width) :
    Misc.wordList base (first ++ second) =
      SetSep.star (Misc.wordList base first)
        (Misc.wordList (base + bytesInWord width * BitVec.ofNat width first.length) second) := by
  induction first generalizing base with
  | nil => simp [Misc.wordList, starEmptyLeft]
  | cons head tail ih =>
    simp only [List.cons_append, Misc.wordList, ih, List.length_cons]
    rw [← SetSep.starAssoc]
    congr 2
    congr 1
    simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, BitVec.add_comm]
/-- Source-local extraction from the original forward word-list heap, retaining
modular addresses and arbitrary payloads; no standalone HOL theorem is claimed. -/
theorem wordListNth {width : Nat} [NeZero width] {β : Type}
    (base : BitVec width) (values : List β)
    (heap : (BitVec width × β) → Prop) (index : Nat)
    (bound : index < values.length) (assertion : Misc.wordList base values heap) :
    heap (base + bytesInWord width * BitVec.ofNat width index, values[index]) := by
  induction values generalizing base heap index with
  | nil => simp at bound
  | cons value values ih =>
    rcases assertion with ⟨head, tail, partition, singleton, rest⟩
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero]
      have member : head (base, value) := by rw [singleton]
      rw [← partition.1]
      simpa using Or.inl member
    | succ index =>
      have smaller : index < values.length := by simpa using bound
      have member := ih (base + bytesInWord width) tail index smaller rest
      have addressEq : base + bytesInWord width + bytesInWord width * BitVec.ofNat width index =
          base + bytesInWord width * BitVec.ofNat width (index + 1) := by
        simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, BitVec.add_comm]
      rw [addressEq] at member
      rw [← partition.1]
      exact Or.inr member
/-- Source-local factoring for StackLoad and StackLoadAny: the original full
state relation derives all bounded native stack reads and the pointer lookup.
No standalone HOL declaration corresponds to this helper. -/
theorem stateRelStackReads {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ base : BitVec width,
      StackSemStateOps.getVar pointer target =
        some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) ∧
      ∀ (index : Nat) (bound : index < source.stack.length),
        StackSemStateOps.memLoad (base + wordOffset index) target = some source.stack[index] := by
  obtain ⟨base, _lookup, _lower, _upper, pointerLookup, heaps⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  refine ⟨base, pointerLookup, ?_⟩
  intro index bound
  rcases heaps with ⟨heap4, heapStack, partition, _rest, stack⟩
  have member := wordListNth base source.stack heapStack index bound stack
  have addressEq : base + bytesInWord width * BitVec.ofNat width index = base + wordOffset index := by
    simp [bytesInWord, wordOffset, BitVec.ofNat_mul]
  rw [addressEq] at member
  have inTarget : SetSep.fun2Set (target.memory, fun address => target.mdomain address = true)
      (base + wordOffset index, source.stack[index]) := by
    rw [← partition.1]
    exact Or.inr member
  have loadFacts := (SetSep.fun2SetThm target.memory (fun address => target.mdomain address = true)
    (base + wordOffset index) source.stack[index]).mp inTarget
  simp only [StackSemStateOps.memLoad, loadFacts.1, loadFacts.2, ite_true]
end Flapjack.Compiler.Backend.StackRemove.StackHeap
