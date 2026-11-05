import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorHeap

/-! Generated scratch-register setup for constructor allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Updating a scratch register outside a list leaves all its variable
lookups unchanged. This is Flapjack execution infrastructure. -/
theorem getVars_setVar_disjoint {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (scratch : Nat) (word : WordLocW width)
    (state : WordSemStateFiniteExact width C F) (distinct : ∀ n ∈ names, n ≠ scratch) :
    WordSemStateFiniteExact.getVars names (WordSemStateFiniteExact.setVar scratch word state) =
      WordSemStateFiniteExact.getVars names state := by
  induction names with
  | nil => rfl
  | cons n ns ih =>
    have ne := distinct n (by simp)
    have tail : ∀ n ∈ ns, n ≠ scratch := by
      intro n member
      exact distinct n (by simp [member])
    simp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVarSetVar, if_neg ne, ih tail]

/-- The compiler's adjusted registers never alias either constructor scratch
register, even when the source argument list contains repeated registers. -/
theorem adjustedArgs_setScratch {width : Nat} [NeZero width] {C F : Type}
    (args : List Nat) (word1 word3 : WordLocW width) (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVars (args.map adjustVar)
        (WordSemStateFiniteExact.setVar 3 word3 (WordSemStateFiniteExact.setVar 1 word1 state)) =
      WordSemStateFiniteExact.getVars (args.map adjustVar) state := by
  rw [getVars_setVar_disjoint, getVars_setVar_disjoint]
  all_goals
    intro n member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    simp only [adjustVar]
    omega

/-- Executing the generated base/header setup followed by the constructor
stores yields the same memory relation as the abstract allocation. The final
pointer assignment and `nextFree` instruction are not yet included. -/
theorem constructorSetup_storeEach {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (fields vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (next tag space : Nat) (be : Bool) (header : BitVec width)
    (state : WordSemStateFiniteExact width C F) (args : List Nat)
    (nonempty : fields ≠ []) (enough : fields.length + 1 ≤ space)
    (encoded : encodeHeader conf (4 * tag) fields.length = some header)
    (related : memoryRel conf be next refs space state.store state.memory state.mdomain (fields ++ vars))
    (argsRun : WordSemStateFiniteExact.getVars (args.map adjustVar) state = some (fields.map Prod.snd)) :
    ∃ (curr : BitVec width) (index : Nat),
      let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
      let nextFree := curr + StackRemove.bytesInWord width * BitVec.ofNat width (index + (fields.length + 1))
      let prepared := WordSemStateFiniteExact.setVar 3 (.word header)
        (WordSemStateFiniteExact.setVar 1 (.word base) state)
      WordSemStateFiniteExact.evaluate
        (.seq (.assign 1 (.lookup .nextFree)) (.seq (.assign 3 (.const header))
          (storeEach 1 (3 :: args.map adjustVar) 0))) state =
        (none, { prepared with memory := storeEachMemory base 0 (.word header :: fields.map Prod.snd) state.memory }) ∧
      memoryRel conf be (next + 1) refs (space - (fields.length + 1))
        (state.store.updateEq (.nextFree, .word nextFree))
        (storeEachMemory base 0 (.word header :: fields.map Prod.snd) state.memory) state.mdomain
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) :: fields ++ vars) := by
  obtain ⟨curr, index, nextStore, result⟩ := memoryRel_allocateBlock conf fields vars refs next tag space be header
    state.store state.memory state.mdomain nonempty enough encoded related
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
  let first := WordSemStateFiniteExact.setVar 1 (.word base) state
  let prepared := WordSemStateFiniteExact.setVar 3 (.word header) first
  have related' : memoryRel conf be next refs space prepared.store prepared.memory prepared.mdomain (fields ++ vars) := by
    simpa [prepared, first, WordSemStateFiniteExact.setVar] using related
  have preparedBase : WordSemStateFiniteExact.getVar 1 prepared = some (.word base) := by
    simp [prepared, first, WordSemStateFiniteExact.getVarSetVar]
  have baseRun : WordSemStateFiniteExact.getVar 1 prepared = prepared.store.lookup .nextFree := by
    simpa [prepared, first, WordSemStateFiniteExact.setVar, nextStore, base] using preparedBase
  have valuesRun : WordSemStateFiniteExact.getVars (3 :: args.map adjustVar) prepared =
      some (.word header :: fields.map Prod.snd) := by
    simp only [WordSemStateFiniteExact.getVars, prepared, WordSemStateFiniteExact.getVarSetVar, ↓reduceIte]
    rw [adjustedArgs_setScratch]
    simp [argsRun]
  obtain ⟨curr', index', baseValue, loop, result'⟩ := memoryRel_allocateBlock_storeEach conf fields vars refs
    next tag space be header prepared 1 (3 :: args.map adjustVar) nonempty enough encoded related' baseRun valuesRun
  have sameBase : curr' + StackRemove.bytesInWord width * BitVec.ofNat width index' = base := by
    have eq := baseValue.symm.trans preparedBase
    exact WordLocW.word.inj (Option.some.inj eq)
  have loop' : WordSemStateFiniteExact.evaluate (storeEach 1 (3 :: args.map adjustVar) 0) prepared =
      (none, { prepared with memory := storeEachMemory base 0 (.word header :: fields.map Prod.snd) state.memory }) := by
    simpa [sameBase, prepared, first, WordSemStateFiniteExact.setVar] using loop
  have firstRun : WordSemStateFiniteExact.evaluate (.assign 1 (.lookup .nextFree)) state = (none, first) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
      nextStore, first, base]
  have secondRun : WordSemStateFiniteExact.evaluate (.assign 3 (.const header)) first = (none, prepared) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, prepared]
  have fixFirst : WordSemStateFiniteExact.fixClock state ((none : Option (WordSemResult width)), first) = (none, first) := by
    simp [WordSemStateFiniteExact.fixClock, first, WordSemStateFiniteExact.setVar]
  have fixSecond : WordSemStateFiniteExact.fixClock first ((none : Option (WordSemResult width)), prepared) = (none, prepared) := by
    simp [WordSemStateFiniteExact.fixClock, prepared, first, WordSemStateFiniteExact.setVar]
  refine ⟨curr, index, ?_, result⟩
  simp only [WordSemStateFiniteExact.evaluate, firstRun, fixFirst, secondRun, fixSecond, loop', prepared, first, base]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
