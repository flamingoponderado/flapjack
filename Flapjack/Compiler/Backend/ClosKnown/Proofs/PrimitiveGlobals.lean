import Flapjack.Compiler.Backend.ClosKnown.Proofs.MappedGlobals
import Flapjack.Compiler.Backend.ClosInterp.Proofs.PrimitiveRelation
import Flapjack.Compiler.Backend.Semantics.ClosProps.GlobalSafety
import Aesop

/-! Runtime global changes made by closure primitives. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem ClosProps

/-- A single list update can only affect the updated index. This helper has
no separate HOL declaration. -/
private theorem mglobalsExtendSet {α : Type} (globals : List (Option α))
    (index : Nat) (value : α) :
    mglobalsExtend globals {index} (globals.set index (some value)) := by
  constructor
  · intro k ⟨v, found⟩
    by_cases same : k = index
    · exact Or.inr same
    · left
      exact ⟨v, by simpa [getGlobal, List.getElem?_set_ne (Ne.symm same)] using found⟩
  · intro k v ⟨found, outside⟩
    have different : index ≠ k := by
      intro same
      apply outside
      change k = index
      exact same.symm
    simpa [getGlobal, List.getElem?_set_ne different] using found

/-- Appending uninitialized slots preserves all initialized globals. This
helper has no separate HOL declaration. -/
private theorem mglobalsExtendAlloc {α : Type} (globals : List (Option α)) (count : Nat) :
    mglobalsExtend globals ∅ (globals ++ List.replicate count none) := by
  have unchanged : ∀ k v, getGlobal k (globals ++ List.replicate count none) = some (some v) →
      getGlobal k globals = some (some v) := by
    intro k v found
    by_cases bound : k < globals.length
    · simpa [getGlobal, List.getElem?_append_left bound] using found
    · simp [getGlobal, List.getElem?_append_right (Nat.le_of_not_gt bound),
        List.getElem?_replicate] at found
  constructor
  · intro k ⟨v, found⟩; exact Or.inl ⟨v, unchanged k v found⟩
  · intro k v h; exact unchanged k v h.1

/-- A successful global primitive initializes only a global named by its
write bag. This is proof infrastructure for HOL `do_app_ssgc`. -/
private theorem applyGlobalMglobals {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (s0 s : State C F) (v : Value) (run : applyGlobal op args s0 = some (v, s)) :
    mglobalsExtend s0.globals {k | opGlobalBag (.globOp op) k ≠ 0} s.globals := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all [opGlobalBag, FlatProps.emptyGlobalBag, mglobalsExtendRefl]
  all_goals rcases run with ⟨_, rfl⟩
  all_goals first | exact mglobalsExtendSet _ _ _ | exact mglobalsExtendAlloc _ _

/-- Successful closure primitives change initialized globals only at indices
in their write bag. This unconditional frame lemma supports the stronger HOL
`do_app_ssgc` result and is not itself a HOL theorem port. -/
theorem doAppMglobals {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s0 s : State C F) (v : Value) (run : doApp op args s0 = .val (v, s)) :
    mglobalsExtend s0.globals {k | opGlobalBag op k ≠ 0} s.globals := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args s0 with
    | none => simp [doApp, h] at run
    | some pair =>
      have eq : pair = (v, s) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobalMglobals operation args s0 s v h
  | blockOp operation =>
    cases h : applyBlock operation args s0 with
    | none => simp [doApp, h] at run
    | some pair =>
      have eq : pair = (v, s) := by simpa [doApp, h] using run
      subst pair
      rw [ClosInterp.applyBlock_globals operation args s0 s v h]
      exact mglobalsExtendRefl _ _
  | memOp operation =>
    cases h : applyMemory operation args s0 with
    | none => simp [doApp, h] at run
    | some pair =>
      have eq : pair = (v, s) := by simpa [doApp, h] using run
      subst pair
      rw [ClosInterp.applyMemory_globals operation args s0 s v h]
      exact mglobalsExtendRefl _ _
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args s0 with
    | none => simp [doApp, h] at run
    | some pair =>
      have eq : pair = (v, s) := by simpa [doApp, h] using run
      subst pair
      rw [ClosInterp.applyNumeric_globals _ args s0 s v h]
      exact mglobalsExtendRefl _ _
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args s0 with
    | none => simp [doApp, h] at run
    | some pair =>
      have eq : pair = (v, s) := by simpa [doApp, h] using run
      subst pair
      rw [ClosInterp.applyNumeric_globals _ args s0 s v h]
      exact mglobalsExtendRefl _ _
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals rcases run with ⟨_, rfl⟩
    all_goals exact mglobalsExtendRefl _ _
  | label | install => simp [doApp] at run

namespace DoAppSafety
open ClosProps.StateGlobalSafety Flapjack.SemanticPrimitivesHOL

/-- The closure state roundtrips through its canonical finite-map view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The integer-constant case of primitive safety retains both the successful
result and raised-exception conclusions of the source theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcIntConst {C F : Type} (i : Int) (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : doApp (.intOp (.const i)) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.intOp (.const i)) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, _, stateSafe⟩
  cases args with
  | nil =>
    simp [ClosSem.doApp, applyNumeric, doIntApp, vsgcFree, stateSafe, mglobalsExtendRefl]
  | cons x xs => simp [ClosSem.doApp, applyNumeric, doIntApp]

/-- The constructor case builds a safe block from safe arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcCons {C F : Type} (tag : Nat) (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : doApp (.blockOp (.cons tag)) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.blockOp (.cons tag)) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, argsSafe, stateSafe⟩
  simp [ClosSem.doApp, applyBlock, vsgcFree, stateSafe, mglobalsExtendRefl]
  exact argsSafe

/-- A successful read returns a safe initialized global and leaves the state
unchanged. This is proof infrastructure for the source primitive case. -/
private theorem globalReadSafe {C F : Type} (index : Nat) (args : List ClosSem.Value)
    (s0 s : State C F) (value : ClosSem.Value) (safe : ssgcFree s0)
    (run : applyGlobal (.global index) args s0 = some (value, s)) :
    vsgcFree value ∧ s = s0 := by
  unfold applyGlobal at run
  repeat' split at run
  all_goals simp_all [Option.map_eq_some_iff, Option.join_eq_some_iff]
  all_goals obtain ⟨_, found, _, _⟩ := run
  all_goals exact safe.2.2.2.1 _ (List.mem_of_getElem? (by assumption))

/-- Reading globals preserves the full primitive safety conclusion, including
dynamic-index reads and the source's raised-exception clause. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcGlobal {C F : Type} (index : Nat) (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : ClosSem.doApp (.globOp (.global index)) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.globOp (.global index)) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, _, stateSafe⟩
  cases found : applyGlobal (.global index) args s0 with
  | none => simp [ClosSem.doApp, found]
  | some pair =>
    rcases pair with ⟨value, next⟩
    obtain ⟨valueSafe, rfl⟩ := globalReadSafe index args s0 next value stateSafe found
    simp [ClosSem.doApp, found, valueSafe, stateSafe, mglobalsExtendRefl]

/-- Updating one global with a safe value preserves state safety. This helper
has no separate HOL declaration. -/
private theorem ssgcFreeSetGlobal {C F : Type} (s : State C F) (index : Nat)
    (value : ClosSem.Value) (stateSafe : ssgcFree s) (valueSafe : vsgcFree value) :
    ssgcFree {s with globals := s.globals.set index (some value)} := by
  rcases stateSafe with ⟨code, refs, thunks, globals, oracle⟩
  refine ⟨code, refs, thunks, ?_, oracle⟩
  intro v member
  rcases List.mem_or_eq_of_mem_set member with old | new
  · exact globals v old
  · cases new; exact valueSafe

/-- Appending empty global slots preserves state safety. This helper has no
separate HOL declaration. -/
private theorem ssgcFreeAllocGlobal {C F : Type} (s : State C F) (count : Nat)
    (stateSafe : ssgcFree s) :
    ssgcFree {s with globals := s.globals ++ List.replicate count none} := by
  rcases stateSafe with ⟨code, refs, thunks, globals, oracle⟩
  refine ⟨code, refs, thunks, ?_, oracle⟩
  intro v member
  simp only [List.mem_append, List.mem_replicate] at member
  rcases member with old | ⟨_, impossible⟩
  · exact globals v old
  · cases impossible

/-- Global writes preserve state safety because the written argument is safe. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcSetGlobal {C F : Type} (index : Nat) (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : ClosSem.doApp (.globOp (.setGlobal index)) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.globOp (.setGlobal index)) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, argsSafe, stateSafe⟩
  cases args with
  | nil => simp [ClosSem.doApp, applyGlobal]
  | cons value values =>
    cases values with
    | cons other tail => simp [ClosSem.doApp, applyGlobal]
    | nil =>
      have valueSafe := argsSafe value (by simp)
      cases slot : getGlobal index s0.globals with
      | none => simp [ClosSem.doApp, applyGlobal, slot]
      | some old =>
        cases old with
        | some old => simp [ClosSem.doApp, applyGlobal, slot]
        | none =>
          have newSafe := ssgcFreeSetGlobal s0 index value stateSafe valueSafe
          have frame := mglobalsExtendSet s0.globals index value
          simp [ClosSem.doApp, applyGlobal, slot, vsgcFreeUnit, newSafe,
            opGlobalBag]
          exact frame

/-- Global allocation adds only empty slots, so it preserves state safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcAllocGlobal {C F : Type} (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : ClosSem.doApp (.globOp .allocGlobal) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.globOp .allocGlobal) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, _, stateSafe⟩
  cases args with
  | nil => simp [ClosSem.doApp, applyGlobal]
  | cons value values =>
    cases values with
    | cons other tail => simp [ClosSem.doApp, applyGlobal]
    | nil =>
      cases value with
      | number count =>
        by_cases negative : count < 0
        · simp [ClosSem.doApp, applyGlobal, negative]
        · have newSafe := ssgcFreeAllocGlobal s0 count.toNat stateSafe
          have frame := mglobalsExtendAlloc s0.globals count.toNat
          simp [ClosSem.doApp, applyGlobal, negative, vsgcFreeUnit, newSafe,
            opGlobalBag, FlatProps.emptyGlobalBag, frame]
      | _ => simp [ClosSem.doApp, applyGlobal]

/-- The closure evaluator rejects the global-pointer read operation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcGlobalsPtr {C F : Type} (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : ClosSem.doApp (.globOp .globalsPtr) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.globOp .globalsPtr) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, _, _⟩
  cases args <;> simp [ClosSem.doApp, applyGlobal]

/-- The closure evaluator rejects the global-pointer update operation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcSetGlobalsPtr {C F : Type} (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : ClosSem.doApp (.globOp .setGlobalsPtr) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.globOp .setGlobalsPtr) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  rcases h with ⟨rfl, _, _⟩
  cases args <;> simp [ClosSem.doApp, applyGlobal]

/-- Every global operation satisfies the complete primitive safety result. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_ssgc"
  (fmap_as_finite_support := [refs, code])]
theorem doAppSsgcGlobOp {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (s0 : State C F) (res : Result (ClosSem.Value × State C F) ClosSem.Value)
    (h : ClosSem.doApp (.globOp op) args s0 = res ∧
      (∀ value ∈ args, vsgcFree value) ∧ ssgcFree s0) :
    (∀ v s, res = .val (v, s) →
      vsgcFree v ∧ ssgcFree s ∧ s.compileOracle = s0.compileOracle ∧
        mglobalsExtend s0.globals {k | opGlobalBag (.globOp op) k ≠ 0} s.globals) ∧
    (∀ v, res = .err (.raise v) → vsgcFree v) := by
  cases op with
  | global index => exact doAppSsgcGlobal index args s0 res h
  | setGlobal index => exact doAppSsgcSetGlobal index args s0 res h
  | allocGlobal => exact doAppSsgcAllocGlobal args s0 res h
  | globalsPtr => exact doAppSsgcGlobalsPtr args s0 res h
  | setGlobalsPtr => exact doAppSsgcSetGlobalsPtr args s0 res h

end DoAppSafety

end Flapjack.Compiler.Backend.ClosKnown
