import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FindCode
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocalUpdates
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery
import Flapjack.Compiler.Backend.Semantics.DataSem.Control

/-! Stack and argument observations needed at data-to-word call entry. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Related data and word stacks have exactly the same optional accounted
size, including exception-frame overhead. -/
theorem stackRel_sizeOfStack {width : Nat} [NeZero width]
    {source : List DataSem.Stack} {target : List (WordSemStackFrame width)}
    (related : List.Forall₂ stackRel source target) :
    wordSemStackSize target = DataSem.sizeOfStack source := by
  induction related with
  | nil => rfl
  | @cons frame wordFrame rest wordRest head tail ih =>
    have frameSize : wordSemStackSizeFrame wordFrame = DataSem.sizeOfStackFrame frame := by
      cases wordFrame with
      | stackFrame wordSize nonGc gc handler =>
        cases frame with
        | env size env =>
          cases handler with
          | none => simpa [stackRel, stackEnvRel, wordSemStackSizeFrame, DataSem.sizeOfStackFrame] using head.2.1.symm
          | some info => simp [stackRel] at head
        | exc size env saved =>
          cases handler with
          | none => simp [stackRel] at head
          | some info =>
            obtain ⟨h, a, b⟩ := info
            simp only [stackRel] at head
            simp [wordSemStackSizeFrame, DataSem.sizeOfStackFrame, head.1.2.1]
    change wordSemOptionAdd (wordSemStackSizeFrame wordFrame) (wordSemStackSize wordRest) =
      Option.map₂ (· + ·) (DataSem.sizeOfStackFrame frame) (DataSem.sizeOfStack rest)
    rw [frameSize, ih]
    cases DataSem.sizeOfStackFrame frame <;> cases DataSem.sizeOfStack rest <;> rfl

private theorem fromListCursor {α : Type} (values : List α) (start : Nat) (tree : Spt α) :
    (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 1, sptInsert acc.1 value acc.2))
      (start, tree)).1 = start + values.length := by
  induction values generalizing start tree with
  | nil => simp
  | cons value values ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    omega

/-- Consecutive source call locals look up the same indexed list element. -/
theorem lookupFromList {α : Type} (values : List α) (key : Nat) :
    sptLookup key (sptFromList values) = values[key]? := by
  induction values using List.reverseRecOn with
  | nil => simp [sptFromList]
  | append_singleton values value ih =>
    have inserted : sptFromList (values ++ [value]) =
        sptInsert values.length value (sptFromList values) := by
      simp only [sptFromList, List.foldl_append, List.foldl_cons, List.foldl_nil, fromListCursor, Nat.zero_add]
    rw [inserted]
    by_cases equal : key = values.length
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne values.length key value (sptFromList values) equal, ih]
      by_cases bound : key < values.length
      · simp [List.getElem?_append, bound]
      · have beyond : values.length < key := by omega
        simp [List.getElem?_append, bound, List.getElem?_eq_none, show 1 ≤ key - values.length by omega]

/-- The first even word local is the return location. -/
theorem callEnv_returnLocation (ret : WordLocW 64) (words : List (WordLocW 64)) :
    sptLookup 0 (sptFromList2 (ret :: words)) = some ret := by
  simp [WordToStackProofs.fromList2Lookup]

/-- Each adjusted source argument key points at the matching word argument. -/
theorem callEnv_argumentLookup (words : List (WordLocW 64)) (ret : WordLocW 64) (index : Nat) :
    sptLookup (adjustVar index) (sptFromList2 (ret :: words)) = words[index]? := by
  simp [WordToStackProofs.fromList2Lookup, adjustVar]

/-- Matching indexed elements are members of the paired argument list. -/
theorem mem_zip_of_index {α β : Type} (xs : List α) (ys : List β) (index : Nat) (x : α) (y : β)
    (hx : xs[index]? = some x) (hy : ys[index]? = some y) : (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys index with
  | nil => simp at hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases index with
      | zero => simp at hx hy; subst a; subst b; simp
      | succ index =>
        simp only [List.getElem?_cons_succ] at hx hy
        exact List.mem_cons_of_mem _ (ih ys index hx hy)

/-- Every joined callee local is one of the source/word argument pairs. -/
theorem callEnv_joined_subset (values : List DataSem.Value) (words : List (WordLocW 64))
    (ret : WordLocW 64) :
    joinEnv (sptFromList values) (sptToAList (sptInter (sptFromList2 (ret :: words)) (adjustSet (sptFromList values)))) ⊆
      values.zip words := by
  intro ⟨value, word⟩ member
  obtain ⟨index, source, target⟩ := joinEnv_localPair (sptFromList values) (sptFromList2 (ret :: words)) value word member
  rw [lookupFromList] at source
  rw [callEnv_argumentLookup] at target
  exact mem_zip_of_index values words index value word source target

/-- Equal-length argument lists give corresponding live local domains. -/
theorem callEnv_argument_present (values : List DataSem.Value) (words : List (WordLocW 64))
    (ret : WordLocW 64) (sameLength : values.length = words.length) (index : Nat)
    (present : (sptLookup index (sptFromList values)).isSome = true) :
    (sptLookup (adjustVar index) (sptFromList2 (ret :: words))).isSome = true := by
  rw [lookupFromList] at present
  rw [callEnv_argumentLookup]
  cases source : values[index]? with
  | none => simp [source] at present
  | some value =>
    have bound : index < values.length := by
      by_contra bad
      have absent : values[index]? = none := List.getElem?_eq_none (by omega)
      rw [source] at absent
      contradiction
    have targetBound : index < words.length := by omega
    simp [List.getElem?_eq_getElem targetBound]

/-- Entering a call with related arguments and a chosen return location
preserves the production-backed candidate state relation. -/
theorem stateRel64_callEnv {C F : Type} (conf : Config) (l1 l2 r1 r2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (values : List DataSem.Value) (words : List (WordLocW 64)) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words) :
    stateRel64 conf r1 r2 (DataSem.callEnv values size (DataSem.decClock source))
      (WordSemStateFiniteExact.callEnv (.loc r1 r2 :: words) size (WordSemStateFiniteExact.decClock target)) none locs := by
  obtain ⟨words', targetRun, sameLength⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  rw [wordRun] at targetRun
  have eq : words = words' := Option.some.inj targetRun
  subst words'
  have zipped := getVars_zip_mem_joinEnv source target names values words sourceRun wordRun
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals,
    zero, locals, stack, locations, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  have stackEq := stackRel_sizeOfStack stack
  refine ⟨ffi, ?_, handler, gc, code, oracle, dimension, shift, timestamps, globals, ?_, ?_, stack, locations,
    ?_, ?_, stackSize, rfl, limits, ?_⟩
  · simp [DataSem.callEnv, WordSemStateFiniteExact.callEnv, DataSem.decClock, WordSemStateFiniteExact.decClock, clock]
  · intro _
    exact callEnv_returnLocation (.loc r1 r2) words
  · intro n present
    exact callEnv_argument_present values words (.loc r1 r2) sameLength n present
  · change BackendProps.optionLe (wordSemOptionAdd (wordSemStackSize target.stack) size)
      (wordSemOptionMax target.stackMax (wordSemOptionAdd (wordSemStackSize target.stack) size))
    cases target.stackMax <;> cases wordSemStackSize target.stack <;> cases size <;>
      simp [wordSemOptionAdd, wordSemOptionMax, BackendProps.optionLe]
  · change BackendProps.optionLe (wordSemOptionMax target.stackMax (wordSemOptionAdd (wordSemStackSize target.stack) size))
      (Option.map₂ max source.stackMax (Option.map₂ (· + ·) (DataSem.sizeOfStack source.stack) size))
    rw [stackEq]
    have addEq : wordSemOptionAdd (DataSem.sizeOfStack source.stack) size =
        Option.map₂ (· + ·) (DataSem.sizeOfStack source.stack) size := by
      cases DataSem.sizeOfStack source.stack <;> cases size <;> rfl
    rw [addEq]
    have maxMono : ∀ a b x, BackendProps.optionLe a b →
        BackendProps.optionLe (wordSemOptionMax a x) (Option.map₂ max b x) := by
      intro a b x h
      cases a <;> cases b <;> cases x <;> simp_all [wordSemOptionMax, BackendProps.optionLe]
      omega
    exact maxMono _ _ _ maxBound
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain _ _ ?_ memory
    intro pair member
    change pair ∈ joinEnv (sptFromList values) (sptToAList (sptInter (sptFromList2 (.loc r1 r2 :: words)) (adjustSet (sptFromList values)))) ++
      [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack at member
    simp only [Option.getD_none, List.nil_append, List.mem_append] at member ⊢
    rcases member with (localRoot | globalRoot) | stackRoot
    · exact Or.inl (Or.inl (zipped pair (callEnv_joined_subset values words (.loc r1 r2) localRoot)))
    · exact Or.inl (Or.inr globalRoot)
    · exact Or.inr stackRoot

/-- Direct calls both find the compiled body and enter it in related states.
The word-side argument list includes the chosen return location. -/
theorem stateRel64_findCode_direct_callEnv {C F : Type} (conf : Config) (l1 l2 r1 r2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (names : List Nat) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some label) values source.code source.stackFrameSizes = some (values, body, size)) :
    ∃ words,
      WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words ∧
      wordSemFindCode (some label) (.loc r1 r2 :: words) target.code target.stackSize =
        some (.loc r1 r2 :: words, (compileControl64 conf label 2 body).1, size) ∧
      stateRel64 conf r1 r2 (DataSem.callEnv values size (DataSem.decClock source))
        (WordSemStateFiniteExact.callEnv (.loc r1 r2 :: words) size (WordSemStateFiniteExact.decClock target)) none locs := by
  obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  exact ⟨words, wordRun, stateRel64_findCode_direct conf l1 l2 source target locs related r1 r2 label values words body size lengths found,
    stateRel64_callEnv conf l1 l2 r1 r2 source target locs related names values words size sourceRun wordRun⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
