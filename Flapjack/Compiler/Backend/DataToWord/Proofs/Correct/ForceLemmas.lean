module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallReturn
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.CutEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.JoinEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.OddInter

@[expose] public section

/-! State-relation steps for the forced-value results of the `Force` case of
the data-to-word evaluator simulation (`data_to_wordProofScript.sml` lines
391-742). Flapjack-specific case infrastructure for `data_compile_correct`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The memory roots of the complete relation for an unchanged source state. -/
noncomputable abbrev stateRoots {width : Nat} [NeZero width] {C F : Type}
    (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F) :
    List (DataSem.Value × WordLocW width) :=
  joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++
    ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)

/-- Returning a single forced value: the flushed states are related with
that value as the pending root. -/
theorem stateRel_flush_single {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (x : DataSem.Value) (w : WordLocW width)
    (rel : stateRel c l1 l2 s t none locs)
    (root : memoryRel c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
      ((x, w) :: stateRoots s t)) :
    stateRel c l1 l2 (DataSem.flushState false s) (WordSemStateFiniteExact.flushState false t)
      (some [(x, w)]) locs := by
  rcases rel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, _, _, hstack, hlocs, hacc, hmax, hsizes, _, hlim, _⟩
  have newMemory : memoryRel c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
      ([(x, w)] ++ [(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack) := by
    apply memoryRel_rearrange c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain _ _ ?_ root
    intro pair member
    simp only [stateRoots, List.mem_append, List.mem_cons] at member ⊢
    tauto
  have newBound : BackendProps.optionLe
      (Option.map₂ (fun x y => x + y) (wordSemStackSize t.stack) (some 0)) t.stackMax := by
    cases hsize : wordSemStackSize t.stack <;> cases hlocal : t.localsSize <;> cases hmax' : t.stackMax
    all_goals simp [hsize, hlocal, hmax', BackendProps.optionLe] at hacc ⊢
    all_goals omega
  simp only [stateRel, DataSem.flushState, Bool.false_eq_true, ↓reduceIte,
    WordSemStateFiniteExact.flushState]
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp,
    hglobal, ?_, ?_, hstack, hlocs, newBound, hmax, hsizes, trivial, hlim, ?_⟩
  · simp
  · simp [sptLookup]
  · simpa [sptInter, sptToAList, sptFoldi, joinEnv_nil, List.append_assoc] using newMemory

/-- Storing a forced value after cutting the source environment; the target
keeps its locals and only updates the destination. -/
theorem stateRel_cutEnv_setVar {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (env : Spt DataSem.Value) (dest : Nat)
    (x : DataSem.Value) (w : WordLocW width)
    (rel : stateRel c l1 l2 s t none locs)
    (cut : DataSem.cutEnv names s.locals = some env)
    (root : memoryRel c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
      ((x, w) :: stateRoots s t)) :
    stateRel c l1 l2 (DataSem.setVar dest x { s with locals := env })
      (WordSemStateFiniteExact.setVar (adjustVar dest) w t) none locs := by
  obtain ⟨_, _, cutRel, _⟩ := stateRel_cutEnv_imp_cutEnv t s locs l2 l1 names c env ⟨rel, cut⟩
  apply stateRel_insertRoot c l1 l2 { s with locals := env } t locs dest x w cutRel
  apply memoryRel_rearrange c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain _ _ ?_ root
  intro pair member
  have key := fun h => mem_joinEnv_cutEnv env pair t.locals names s.locals ⟨h, cut⟩
  simp only [stateRoots, List.mem_append, List.mem_cons] at member key ⊢
  tauto

/-- Odd scratch registers do not change the memory roots of the relation. -/
theorem stateRoots_insertOdd {width : Nat} [NeZero width] {C F : Type}
    (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width)
    (odd : k % 2 = 1) :
    stateRoots s { t with locals := sptInsert k v t.locals } = stateRoots s t := by
  simp only [stateRoots, inter_insertOdd_adjustSet k v t.locals s.locals odd]

/-- Adding pending roots that are present in memory. -/
theorem stateRel_withRoots {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (roots : List (DataSem.Value × WordLocW width))
    (rel : stateRel c l1 l2 s t none locs)
    (mem : memoryRel c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
      (roots ++ stateRoots s t)) :
    stateRel c l1 l2 s t (some roots) locs := by
  rcases rel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, _, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
  · intro h
    exact absurd h (by simp)
  simpa [stateRoots, List.append_assoc] using mem

private theorem optionMapAdd' (a b : Option Nat) :
    Option.map₂ (· + ·) a b = wordSemOptionAdd a b := by
  cases a <;> cases b <;> rfl

/-- Entering a tail callee whose arguments are pending roots. Generalizes
`state_rel_call_env` from variable reads to arbitrary related values. -/
theorem stateRel_callEnv_values {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 l5 l6 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (words : List (WordLocW width)) (size : Option Nat)
    (lens : values.length = words.length)
    (related : stateRel conf l5 l6 source target (some (values.zip words)) locs) :
    stateRel conf l1 l2 (DataSem.callEnv values size (DataSem.decClock source))
      (WordSemStateFiniteExact.callEnv (.loc l1 l2 :: words) size
        (WordSemStateFiniteExact.decClock target)) none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, _, _, hstack, hlocs, hacc, hmax, hsizes, _, hlim, hmem⟩
  refine ⟨hffi, ?_, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, ?_, hstack, hlocs, ?_, ?_, hsizes, rfl, hlim, ?_⟩
  · simpa [DataSem.callEnv, DataSem.decClock, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.decClock] using congrArg (fun n : Nat => n - 1) hclock
  · intro _
    simp [WordSemStateFiniteExact.callEnv, WordToStackProofs.fromList2Lookup]
  · intro key present
    change (sptLookup key (sptFromList values)).isSome = true at present
    change (sptLookup (adjustVar key) (sptFromList2 (.loc l1 l2 :: words))).isSome = true
    rw [lookup_adjustVar_fromList2]
    rw [sptLookupFromList_getElem?] at present ⊢
    apply Option.isSome_iff_exists.mpr
    have inRange : key < values.length := by simpa using present
    have wordRange : key < words.length := by omega
    exact ⟨words[key], by simp [wordRange]⟩
  · change optionLe (Option.map₂ (· + ·) (wordSemStackSize target.stack) size)
      (wordSemOptionMax target.stackMax (wordSemOptionAdd (wordSemStackSize target.stack) size))
    rw [optionMapAdd', WordSemStateFiniteExact.wordSemOptionMax_eq, optionLe_max_right]
    exact Or.inr (optionLe_refl _)
  · change optionLe (wordSemOptionMax target.stackMax (wordSemOptionAdd (wordSemStackSize target.stack) size))
      (Option.map₂ max source.stackMax (Option.map₂ (· + ·) (DataSem.sizeOfStack source.stack) size))
    have stackEq := stackRel_sizeOfStack hstack
    rw [WordSemStateFiniteExact.wordSemOptionMax_eq, stackEq, ← optionMapAdd', optionLe_max]
    constructor
    · rw [optionLe_max_right]
      exact Or.inl hmax
    · rw [optionLe_max_right]
      exact Or.inr (optionLe_refl _)
  · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv (sptFromList values) (sptToAList
        (sptInter (sptFromList2 (.loc l1 l2 :: words)) (adjustSet (sptFromList values)))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    refine memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ ?_ hmem
    intro pair member
    have joined : pair ∈ joinEnv (sptFromList values) (sptToAList
        (sptInter (sptFromList2 (.loc l1 l2 :: words)) (adjustSet (sptFromList values)))) →
        pair ∈ values.zip words := callJoin_mem values words (.loc l1 l2) pair
    simp only [Option.getD_some, List.mem_append] at member ⊢
    tauto

/-- An odd scratch register update does not affect the relation. -/
theorem stateRel_setVar_odd {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (v : Option (List (DataSem.Value × WordLocW width))) (locs : List (Nat × Nat))
    (k : Nat) (x : WordLocW width) (odd : k % 2 = 1) :
    stateRel c l1 l2 s (WordSemStateFiniteExact.setVar k x t) v locs ↔ stateRel c l1 l2 s t v locs := by
  simp only [WordSemStateFiniteExact.setVar]
  rw [stateRel_insertOdd c l1 l2 s t v locs k x odd]

/-- An odd scratch register update does not change the memory roots. -/
theorem stateRoots_setVar_odd {width : Nat} [NeZero width] {C F : Type}
    (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F) (k : Nat) (x : WordLocW width)
    (odd : k % 2 = 1) :
    stateRoots s (WordSemStateFiniteExact.setVar k x t) = stateRoots s t :=
  stateRoots_insertOdd s t k x odd

end Flapjack.Compiler.Backend.DataToWord.Proofs
