import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists

/-! Execution of the constructor's consecutive word stores. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack

/-- Addresses visited by the emitted `storeEach` program. -/
def storeEachAddresses {width : Nat} [NeZero width] (base offset : BitVec width) : Nat → List (BitVec width)
  | 0 => []
  | n + 1 => (base + offset) :: storeEachAddresses base (offset + BitVec.ofNat width (width / 8)) n

/-- Memory produced by consecutive stores, retaining the word machine's
last-write-wins behavior even if addresses wrap around. -/
def storeEachMemory {width : Nat} [NeZero width] (base offset : BitVec width) :
    List (WordLocW width) → (BitVec width → WordLocW width) → BitVec width → WordLocW width
  | [], memory => memory
  | value :: values, memory =>
      storeEachMemory base (offset + BitVec.ofNat width (width / 8)) values
        (fun address => if address = base + offset then value else memory address)

/-- Every address the store loop visits is represented in an existential
word-list assertion of the same length. -/
theorem storeEachAddresses_in_wordListExists {width : Nat} [NeZero width] {β : Type}
    (base offset : BitVec width) (count : Nat) (heap : (BitVec width × β) → Prop)
    (assertion : Misc.wordListExists (base + offset) count heap) :
    ∀ address ∈ storeEachAddresses base offset count, ∃ value, heap (address, value) := by
  induction count generalizing offset heap with
  | zero => simp [storeEachAddresses]
  | succ count ih =>
    rw [(Flapjack.Compiler.Backend.StackRemove.WordListExists.wordListExistsThm (base + offset) count).2] at assertion
    obtain ⟨value, first, rest, split, singleton, tail⟩ := assertion
    intro address member
    simp only [storeEachAddresses, List.mem_cons] at member
    rcases member with same | later
    · subst address
      refine ⟨value, ?_⟩
      rw [← split.1]
      left
      simpa [SetSep.one] using congrFun singleton (base + offset, value)
    · have tail' : Misc.wordListExists (base + (offset + BitVec.ofNat width (width / 8))) count rest := by
        simpa [Flapjack.Compiler.Backend.StackRemove.bytesInWord, BitVec.add_assoc] using tail
      obtain ⟨item, inRest⟩ := ih _ rest tail' address later
      refine ⟨item, ?_⟩
      rw [← split.1]
      exact Or.inr inRest

/-- A separated free region supplies the destination-domain facts required
by the actual generated stores. -/
theorem storeEachAddresses_in_domain {width : Nat} [NeZero width]
    (base offset : BitVec width) (count : Nat) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (separated : SetSep.star (Misc.wordListExists (base + offset) count) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∀ address ∈ storeEachAddresses base offset count, domain address = true := by
  obtain ⟨region, rest, split, regionInv, _⟩ := separated
  intro address member
  obtain ⟨value, inRegion⟩ := storeEachAddresses_in_wordListExists base offset count region regionInv address member
  have inMemory : SetSep.fun2Set (memory, fun address => domain address = true) (address, value) := by
    rw [← split.1]
    exact Or.inl inRegion
  exact ((SetSep.fun2SetThm memory (fun address => domain address = true) address value).mp inMemory).2

/-- Executing `storeEach` performs exactly the corresponding consecutive
writes, preserving all state fields other than memory. The result permits
repeated registers and modular address wraparound. This is Flapjack-specific
execution infrastructure, not a separate HOL theorem port. -/
theorem evaluate_storeEach {width : Nat} [NeZero width] {C F : Type}
    (baseName : Nat) (names : List Nat) (offset base : BitVec width)
    (values : List (WordLocW width)) (state : WordSemStateFiniteExact width C F)
    (baseRun : WordSemStateFiniteExact.getVar baseName state = some (.word base))
    (valuesRun : WordSemStateFiniteExact.getVars names state = some values)
    (inDomain : ∀ address ∈ storeEachAddresses base offset names.length, state.mdomain address = true) :
    WordSemStateFiniteExact.evaluate (storeEach baseName names offset) state =
      (none, { state with memory := storeEachMemory base offset values state.memory }) := by
  induction names generalizing offset values state with
  | nil =>
    simp [WordSemStateFiniteExact.getVars] at valuesRun
    subst values
    simp [storeEach, storeEachMemory, WordSemStateFiniteExact.evaluate]
  | cons name names ih =>
    cases valueRun : WordSemStateFiniteExact.getVar name state with
    | none => simp [WordSemStateFiniteExact.getVars, valueRun] at valuesRun
    | some value =>
      cases restRun : WordSemStateFiniteExact.getVars names state with
      | none => simp [WordSemStateFiniteExact.getVars, valueRun, restRun] at valuesRun
      | some rest =>
        have valuesEq : values = value :: rest := by
          simpa [WordSemStateFiniteExact.getVars, valueRun, restRun] using valuesRun.symm
        subst values
        have firstDomain : state.mdomain (base + offset) = true := by
          apply inDomain
          simp [storeEachAddresses]
        let next := { state with memory := fun address => if address = base + offset then value else state.memory address }
        have nextBase : WordSemStateFiniteExact.getVar baseName next = some (.word base) := by
          simpa [next, WordSemStateFiniteExact.getVar] using baseRun
        have nextValues : WordSemStateFiniteExact.getVars names next = some rest := by
          have same : ∀ ns, WordSemStateFiniteExact.getVars ns next = WordSemStateFiniteExact.getVars ns state := by
            intro ns
            induction ns with
            | nil => rfl
            | cons n ns ih => simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, next, ih]
          rw [same]
          exact restRun
        have nextDomain : ∀ address ∈ storeEachAddresses base (offset + BitVec.ofNat width (width / 8)) names.length,
            next.mdomain address = true := by
          intro address member
          apply inDomain address
          simp only [List.length_cons, storeEachAddresses, List.mem_cons]
          exact Or.inr member
        have first : WordSemStateFiniteExact.evaluate (.store (.op .add [.var baseName, .const offset]) name) state =
            (none, next) := by
          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, baseRun, valueRun,
            WordSemStateFiniteExact.memStore, firstDomain, next, wordOpHOL, wordOp, theWords]
        have fix : WordSemStateFiniteExact.fixClock state ((none : Option (WordSemResult width)), next) = (none, next) := by
          simp [WordSemStateFiniteExact.fixClock, next]
        have tail := ih (offset + BitVec.ofNat width (width / 8)) rest next nextBase nextValues nextDomain
        simpa only [storeEach, WordSemStateFiniteExact.evaluate, first, fix, storeEachMemory, next] using tail

/-- A free region in the separated machine heap supplies every destination
needed to execute the compiler's consecutive store loop. -/
theorem evaluate_storeEach_of_freeRegion {width : Nat} [NeZero width] {C F : Type}
    (baseName : Nat) (names : List Nat) (offset base : BitVec width)
    (values : List (WordLocW width)) (state : WordSemStateFiniteExact width C F)
    (baseRun : WordSemStateFiniteExact.getVar baseName state = some (.word base))
    (valuesRun : WordSemStateFiniteExact.getVars names state = some values)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (free : SetSep.star (Misc.wordListExists (base + offset) names.length) frame
      (SetSep.fun2Set (state.memory, fun address => state.mdomain address = true))) :
    WordSemStateFiniteExact.evaluate (storeEach baseName names offset) state =
      (none, { state with memory := storeEachMemory base offset values state.memory }) := by
  exact evaluate_storeEach baseName names offset base values state baseRun valuesRun
    (storeEachAddresses_in_domain base offset names.length state.memory state.mdomain frame free)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
