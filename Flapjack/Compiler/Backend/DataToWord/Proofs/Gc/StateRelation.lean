import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeOracle
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Limits
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Compiler.Backend.BackendProps
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

/-! Production-backed candidate for the 64-bit data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions

/-- A 64-bit state relation with the same components as HOL's state relation,
but using the actual compiler's candidate code and oracle relations. It is not
tagged as a HOL port: agreement of those relations with HOL's unrestricted
compiler remains open. -/
noncomputable def stateRel64 {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (extra : Option (List (DataSem.Value × WordLocW 64))) (locs : List (Nat × Nat)) : Prop :=
  target.ffi = source.ffi ∧ target.clock = source.clock ∧ target.handler = source.handler ∧
  target.gcFun = wordGcFun conf ∧ codeRel64 conf source.code target.code ∧
  codeOracleRel64 conf source.compile source.compileOracle target.store target.compile
    target.compileOracle target.codeBuffer target.dataBuffer ∧
  goodDimindex 64 ∧ shiftLength conf < 64 ∧ source.tstamps.isSome = true ∧
  target.store.lookup .globals ≠ none ∧
  (extra = none → sptLookup 0 target.locals = some (.loc l1 l2)) ∧
  (∀ n, (sptLookup n source.locals).isSome = true →
    (sptLookup (adjustVar n) target.locals).isSome = true) ∧
  List.Forall₂ stackRel source.stack target.stack ∧ List.Forall₂ containsLoc target.stack locs ∧
  BackendProps.optionLe (wordSemOptionAdd (wordSemStackSize target.stack) target.localsSize) target.stackMax ∧
  BackendProps.optionLe target.stackMax source.stackMax ∧ target.stackSize = source.stackFrameSizes ∧
  target.localsSize = source.localsSize ∧
  limitsInv source.limits (target.store.lookup .heapLength) target.stackLimit conf.lenSize conf.hasFpOps conf.hasFpTern ∧
  Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain
    (extra.getD [] ++ joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
      [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)

/-- Changing both clocks together preserves the candidate relation. -/
theorem stateRel64_withClock {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (extra : Option (List (DataSem.Value × WordLocW 64))) (locs : List (Nat × Nat)) (clock : Nat)
    (related : stateRel64 conf l1 l2 source target extra locs) :
    stateRel64 conf l1 l2 { source with clock := clock } { target with clock := clock } extra locs := by
  rcases related with ⟨ffi, _, rest⟩
  exact ⟨ffi, rfl, rest⟩

/-- The candidate relation does not inspect the target floating-point registers. -/
theorem stateRel64_withFpRegs {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (extra : Option (List (DataSem.Value × WordLocW 64))) (locs : List (Nat × Nat))
    (regs : HolFiniteMapExact Nat (BitVec 64)) (related : stateRel64 conf l1 l2 source target extra locs) :
    stateRel64 conf l1 l2 source { target with fpRegs := regs } extra locs := by
  simpa [stateRel64] using related

/-- Source space-safety bookkeeping is not observed by the relation. -/
theorem stateRel64_withSafeForSpace {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (extra : Option (List (DataSem.Value × WordLocW 64))) (locs : List (Nat × Nat)) (flag : Bool) :
    stateRel64 conf l1 l2 { source with safeForSpace := flag } target extra locs ↔
      stateRel64 conf l1 l2 source target extra locs := by
  rfl

/-- A live source local has a corresponding target local. This is the
production-backed counterpart of the lookup consequence of the HOL relation. -/
theorem stateRel64_getVar {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (extra : Option (List (DataSem.Value × WordLocW 64))) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target extra locs)
    (n : Nat) (value : DataSem.Value) (found : DataSem.getVar n source.locals = some value) :
    ∃ word, WordSemStateFiniteExact.getVar (adjustVar n) target = some word := by
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, names, _⟩
  have found' : sptLookup n source.locals = some value := found
  have present := names n (by rw [found']; rfl)
  cases h : sptLookup (adjustVar n) target.locals with
  | none => simp [h] at present
  | some word => exact ⟨word, h⟩

/-- Successful source local lookup of a list gives target values of the same
length at the adjusted names. -/
theorem stateRel64_getVars {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (extra : Option (List (DataSem.Value × WordLocW 64))) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target extra locs)
    (names : List Nat) (values : List DataSem.Value) (found : DataSem.getVars names source.locals = some values) :
    ∃ words, WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words ∧ values.length = words.length := by
  induction names generalizing values with
  | nil =>
    simp [DataSem.getVars] at found
    subst values
    exact ⟨[], rfl, rfl⟩
  | cons name names ih =>
    cases one : DataSem.getVar name source.locals with
    | none => simp [DataSem.getVars, one] at found
    | some value =>
      cases rest : DataSem.getVars names source.locals with
      | none => simp [DataSem.getVars, one, rest] at found
      | some values' =>
        simp [DataSem.getVars, one, rest] at found
        subst values
        obtain ⟨word, wordRun⟩ := stateRel64_getVar conf l1 l2 source target extra locs related name value one
        obtain ⟨words, wordsRun, size⟩ := ih values' rest
        refine ⟨word :: words, ?_, by simp [size]⟩
        simp [WordSemStateFiniteExact.getVars, wordRun, wordsRun]

/-- With no extra roots, register zero holds the return location before the
translated source locals. -/
theorem stateRel64_zero_getVars {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (values : List DataSem.Value) (found : DataSem.getVars names source.locals = some values) :
    ∃ words, WordSemStateFiniteExact.getVars (0 :: names.map adjustVar) target = some (.loc l1 l2 :: words) ∧
      values.length = words.length := by
  obtain ⟨words, wordsRun, size⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values found
  have zero : sptLookup 0 target.locals = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  refine ⟨words, ?_, size⟩
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, zero, wordsRun]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
