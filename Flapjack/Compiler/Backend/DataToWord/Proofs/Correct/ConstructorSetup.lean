import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorHeap
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address

/-! Generated scratch-register setup for constructor allocation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The inline pointer bits used by the generated constructor match the
abstract heap address annotation. -/
theorem constructor_pointerBits {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) :
    pointerBits (width := width) conf tag len = ptrBits conf tag len := by
  rw [ptrBits_eq_inlined]
  rfl

/-- Computing the pointer from `nextFree - currHeap` gives the abstract
constructor address on supported word widths. -/
theorem constructor_pointerValue {width : Nat} [NeZero width] (conf : Config)
    (tag len index : Nat) (curr : BitVec width) (good : goodDimindex width)
    (shiftBound : wordShiftAmount width ≤ shiftLength conf) :
    (((curr + StackRemove.bytesInWord width * BitVec.ofNat width index - curr) <<<
        (shiftLength conf - wordShiftAmount width)) |||
      getLowerBits conf (.word (pointerBits conf tag len))) =
      getAddr conf index (.word (ptrBits conf tag len)) := by
  rw [constructor_pointerBits]
  simp only [getAddr, BitVec.add_comm curr, BitVec.add_sub_cancel]
  rw [BitVec.mul_comm, ← shiftWordBytes good, ← BitVec.shiftLeft_add]
  have shiftEq : wordShiftAmount width + (shiftLength conf - wordShiftAmount width) = shiftLength conf := by omega
  rw [shiftEq]

/-- The generated pointer and `nextFree` instructions install the abstract
constructor pointer and advance the allocation address by its word size. -/
theorem constructorFinish_evaluate {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (dest tag len index : Nat) (curr : BitVec width) (state : WordSemStateFiniteExact width C F)
    (good : goodDimindex width) (shiftBound : wordShiftAmount width ≤ shiftLength conf)
    (shiftFits : shiftLength conf < width)
    (baseRun : WordSemStateFiniteExact.getVar 1 state =
      some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width index)))
    (currRun : state.store.lookup .currHeap = some (.word curr)) :
    let pointer := getAddr conf index (.word (ptrBits conf tag len))
    let nextFree := curr + StackRemove.bytesInWord width * BitVec.ofNat width (index + (len + 1))
    WordSemStateFiniteExact.evaluate
      (.seq (.assign (adjustVar dest) (.op .or [
        shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
        .const (getLowerBits conf (.word (pointerBits conf tag len)))]))
        (.set .nextFree (.op .add [.var 1, .const (BitVec.ofNat width (width / 8) * BitVec.ofNat width (len + 1))]))) state =
      (none, WordSemStateFiniteExact.setStore .nextFree (.word nextFree)
        (WordSemStateFiniteExact.setVar (adjustVar dest) (.word pointer) state)) := by
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
  let pointer : BitVec width := getAddr conf index (.word (ptrBits conf tag len))
  let after := WordSemStateFiniteExact.setVar (adjustVar dest) (.word pointer) state
  have shiftSmall : shiftLength conf - wordShiftAmount width < width := by omega
  have shiftMod : (BitVec.ofNat width (shiftLength conf - wordShiftAmount width)).toNat =
      shiftLength conf - wordShiftAmount width := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have power : width < 2 ^ width := Nat.lt_two_pow_self
    omega
  have shiftValid : ¬ (shiftLength conf - wordShiftAmount width ≠ 0 ∧
      width ≤ shiftLength conf - wordShiftAmount width) := by omega
  have ptrEq := constructor_pointerValue conf tag len index curr good shiftBound
  have ptrEq' : ((StackRemove.bytesInWord width * BitVec.ofNat width index) <<<
      (shiftLength conf - wordShiftAmount width)) ||| getLowerBits conf (.word (pointerBits conf tag len)) = pointer := by
    simpa only [BitVec.add_comm curr, BitVec.add_sub_cancel, pointer] using ptrEq
  have pointerRun : WordSemStateFiniteExact.evaluate (.assign (adjustVar dest) (.op .or [
      shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
      .const (getLowerBits conf (.word (pointerBits conf tag len)))])) state = (none, after) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, shiftN,
      WordSemStateFiniteExact.getStore, baseRun, currRun, wordOpHOL, wordOp, theWords,
      wordShiftHOL, shiftMod, shiftValid, after, OrOp.or, BitVec.or_zero]
    rw [ptrEq']
  have scratch : adjustVar dest ≠ 1 := by simp [adjustVar]
  have getBase : WordSemStateFiniteExact.getVar 1 after = some (.word base) := by
    simpa [after, WordSemStateFiniteExact.getVarSetVar, Ne.symm scratch, base] using baseRun
  have nextRun : WordSemStateFiniteExact.evaluate
      (.set .nextFree (.op .add [.var 1, .const (BitVec.ofNat width (width / 8) * BitVec.ofNat width (len + 1))])) after =
      (none, WordSemStateFiniteExact.setStore .nextFree
        (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (index + (len + 1)))) after) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, getBase,
      wordOpHOL, wordOp, theWords, base, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  have fix : WordSemStateFiniteExact.fixClock state ((none : Option (WordSemResult width)), after) = (none, after) := by
    simp [WordSemStateFiniteExact.fixClock, after, WordSemStateFiniteExact.setVar]
  simp only [WordSemStateFiniteExact.evaluate, pointerRun, fix, nextRun, after, pointer]

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
      state.store.lookup .currHeap = some (.word curr) ∧
      state.store.lookup .nextFree = some (.word base) ∧
      WordSemStateFiniteExact.evaluate
        (.seq (.assign 1 (.lookup .nextFree)) (.seq (.assign 3 (.const header))
          (storeEach 1 (3 :: args.map adjustVar) 0))) state =
        (none, { prepared with memory := storeEachMemory base 0 (.word header :: fields.map Prod.snd) state.memory }) ∧
      memoryRel conf be (next + 1) refs (space - (fields.length + 1))
        (state.store.updateEq (.nextFree, .word nextFree))
        (storeEachMemory base 0 (.word header :: fields.map Prod.snd) state.memory) state.mdomain
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) :: fields ++ vars) := by
  obtain ⟨curr, index, currStore, nextStore, result⟩ := memoryRel_allocateBlock conf fields vars refs next tag space be header
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
  refine ⟨curr, index, currStore, nextStore, ?_, result⟩
  simp only [WordSemStateFiniteExact.evaluate, firstRun, fixFirst, secondRun, fixSecond, loop', prepared, first, base]

/-- All instructions in the nonempty constructor sequence execute and leave
the resulting memory relation, starting from the original word state. -/
theorem constructorSequence_evaluate {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (fields vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (next tag space dest : Nat) (be : Bool) (header : BitVec width)
    (state : WordSemStateFiniteExact width C F) (args : List Nat)
    (good : goodDimindex width) (nonempty : fields ≠ []) (enough : fields.length + 1 ≤ space)
    (encoded : encodeHeader conf (4 * tag) fields.length = some header)
    (related : memoryRel conf be next refs space state.store state.memory state.mdomain (fields ++ vars))
    (argsRun : WordSemStateFiniteExact.getVars (args.map adjustVar) state = some (fields.map Prod.snd)) :
    ∃ (index : Nat) (final : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.lookup .nextFree), .assign 3 (.const header),
        storeEach 1 (3 :: args.map adjustVar) 0,
        .assign (adjustVar dest) (.op .or [
          shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
          .const (getLowerBits conf (.word (pointerBits conf tag fields.length)))]),
        .set .nextFree (.op .add [.var 1, .const (BitVec.ofNat width (width / 8) * BitVec.ofNat width (fields.length + 1))])]) state =
        (none, final) ∧
      WordSemStateFiniteExact.getVar (adjustVar dest) final =
        some (wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) ∧
      memoryRel conf be (next + 1) refs (space - (fields.length + 1)) final.store final.memory final.mdomain
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) :: fields ++ vars) := by
  obtain ⟨curr, index, currStore, nextStore, prefixRun, result⟩ :=
    constructorSetup_storeEach conf fields vars refs next tag space be header state args nonempty enough encoded related argsRun
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
  let pointer : BitVec width := getAddr conf index (.word (ptrBits conf tag fields.length))
  let nextFree := curr + StackRemove.bytesInWord width * BitVec.ofNat width (index + (fields.length + 1))
  let first := WordSemStateFiniteExact.setVar 1 (.word base) state
  let prepared := WordSemStateFiniteExact.setVar 3 (.word header) first
  let written := { prepared with memory := storeEachMemory base 0 (.word header :: fields.map Prod.snd) state.memory }
  let after := WordSemStateFiniteExact.setVar (adjustVar dest) (.word pointer) written
  let final := WordSemStateFiniteExact.setStore .nextFree (.word nextFree) after
  obtain ⟨_, _, _, _, _, _, heapMem, _, _, _⟩ := related
  have shiftBound : wordShiftAmount width ≤ shiftLength conf := heapMem.2.2.1
  have shiftFits : shiftLength conf < width := heapMem.2.2.2.2.2.1
  have firstRun : WordSemStateFiniteExact.evaluate (.assign 1 (.lookup .nextFree)) state = (none, first) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
      nextStore, first, base]
  have secondRun : WordSemStateFiniteExact.evaluate (.assign 3 (.const header)) first = (none, prepared) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, prepared]
  have fixFirst : WordSemStateFiniteExact.fixClock state ((none : Option (WordSemResult width)), first) = (none, first) := by
    simp [WordSemStateFiniteExact.fixClock, first, WordSemStateFiniteExact.setVar]
  have fixSecond : WordSemStateFiniteExact.fixClock first ((none : Option (WordSemResult width)), prepared) = (none, prepared) := by
    simp [WordSemStateFiniteExact.fixClock, prepared, first, WordSemStateFiniteExact.setVar]
  have loopRun : WordSemStateFiniteExact.evaluate (storeEach 1 (3 :: args.map adjustVar) 0) prepared = (none, written) := by
    simpa only [WordSemStateFiniteExact.evaluate, firstRun, fixFirst, secondRun, fixSecond, first, prepared, written, base] using prefixRun
  have baseRun : WordSemStateFiniteExact.getVar 1 written = some (.word base) := by
    simp [written, prepared, first, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
  have currRun : written.store.lookup .currHeap = some (.word curr) := by
    simpa [written, prepared, first, WordSemStateFiniteExact.setVar] using currStore
  have finish := constructorFinish_evaluate conf dest tag fields.length index curr written good shiftBound shiftFits
    (by simpa [base] using baseRun) currRun
  simp only [WordSemStateFiniteExact.evaluate] at finish
  have fixWritten : WordSemStateFiniteExact.fixClock prepared ((none : Option (WordSemResult width)), written) = (none, written) := by
    simp [WordSemStateFiniteExact.fixClock, written]
  have finalRun : WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.lookup .nextFree), .assign 3 (.const header),
        storeEach 1 (3 :: args.map adjustVar) 0,
        .assign (adjustVar dest) (.op .or [
          shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
          .const (getLowerBits conf (.word (pointerBits conf tag fields.length)))]),
        .set .nextFree (.op .add [.var 1, .const (BitVec.ofNat width (width / 8) * BitVec.ofNat width (fields.length + 1))])]) state = (none, final) := by
    simp only [wordListSeq, WordSemStateFiniteExact.evaluate, firstRun, fixFirst, secondRun, fixSecond, loopRun, fixWritten]
    simpa [final, after, pointer, nextFree] using finish
  refine ⟨index, final, finalRun, ?_, ?_⟩
  · simp [final, after, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, wordAddr, sptLookup_sptInsert_same, pointer]
  · simpa [final, after, written, prepared, first, WordSemStateFiniteExact.setStore,
      WordSemStateFiniteExact.setVar, nextFree, base] using result

/-- The checked compiler emits the inline allocation sequence for a nonempty
constructor whose header can be encoded. This is Flapjack infrastructure. -/
theorem compileControl_cons_sequence {width : Nat} [NeZero width] (conf : Config)
    (secn label dest tag : Nat) (args : List Nat) (names : Option (Spt Unit))
    (header : BitVec width) (nonempty : args ≠ [])
    (encoded : encodeHeader conf (4 * tag) args.length = some header) :
    compileControl? (width := width) conf secn label (.assign dest (.blockOp (.cons tag)) args names) =
      some (wordListSeq [
        .assign 1 (.lookup .nextFree), .assign 3 (.const header),
        storeEach 1 (3 :: args.map adjustVar) 0,
        .assign (adjustVar dest) (.op .or [
          shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
          .const (getLowerBits conf (.word (pointerBits conf tag args.length)))]),
        .set .nextFree (.op .add [.var 1, .const (BitVec.ofNat width (width / 8) * BitVec.ofNat width (args.length + 1))])], label) := by
  cases args with
  | nil => contradiction
  | cons arg rest =>
    simp only [compileControl?]
    change some (match encodeHeader conf (4 * tag) (arg :: rest).length with
      | none => (giveUp, label)
      | some h => (wordListSeq [
        .assign 1 (.lookup .nextFree), .assign 3 (.const h),
        storeEach 1 (3 :: (arg :: rest).map adjustVar) 0,
        .assign (adjustVar dest) (.op .or [
          shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
          .const (getLowerBits conf (.word (pointerBits conf tag (arg :: rest).length)))]),
        .set .nextFree (.op .add [.var 1, .const (BitVec.ofNat width (width / 8) * BitVec.ofNat width ((arg :: rest).length + 1))])], label)) = _
    rw [encoded]

/-- The checked compiler's nonempty constructor output executes from a
related heap and produces the allocated pointer and updated heap relation.
This is Flapjack execution infrastructure, not the complete pass theorem. -/
theorem compileControl_cons_evaluate {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (secn label dest tag : Nat) (args : List Nat) (names : Option (Spt Unit))
    (fields vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (next space : Nat) (be : Bool) (header : BitVec width)
    (state : WordSemStateFiniteExact width C F)
    (good : goodDimindex width) (nonempty : fields ≠ []) (enough : fields.length + 1 ≤ space)
    (encoded : encodeHeader conf (4 * tag) fields.length = some header)
    (related : memoryRel conf be next refs space state.store state.memory state.mdomain (fields ++ vars))
    (argsRun : WordSemStateFiniteExact.getVars (args.map adjustVar) state = some (fields.map Prod.snd)) :
    ∃ (program : WordLangProgHOL (BitVec width)) (index : Nat) (final : WordSemStateFiniteExact width C F),
      compileControl? conf secn label (.assign dest (.blockOp (.cons tag)) args names) = some (program, label) ∧
      WordSemStateFiniteExact.evaluate program state = (none, final) ∧
      WordSemStateFiniteExact.getVar (adjustVar dest) final =
        some (wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) ∧
      memoryRel conf be (next + 1) refs (space - (fields.length + 1)) final.store final.memory final.mdomain
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) :: fields ++ vars) := by
  have lengthEq : args.length = fields.length := by
    have lengths := WordSemStateFiniteExact.getVarsLengthLemma (args.map adjustVar) state _ argsRun
    simpa using lengths.symm
  have argsNonempty : args ≠ [] := by
    intro empty
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa [empty] using lengthEq.symm
  have compiled := compileControl_cons_sequence conf secn label dest tag args names header argsNonempty
    (by simpa [lengthEq] using encoded)
  obtain ⟨index, final, run, pointer, result⟩ := constructorSequence_evaluate conf fields vars refs next tag space dest be
    header state args good nonempty enough encoded related argsRun
  refine ⟨_, index, final, ?_, run, pointer, result⟩
  simpa [lengthEq] using compiled

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
