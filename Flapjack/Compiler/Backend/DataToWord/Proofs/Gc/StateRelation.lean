module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeOracleRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Limits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.WordGcFunctions
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Misc.FiniteMapApply
public import Flapjack.Misc.GoodDimindex

@[expose] public section

/-! Complete data-to-word state relation, pending compiler source review. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps

/-- The full relation between data and word states, including compiled code,
callbacks, stack shape, resource limits, and the GC-compatible memory
abstraction. This follows the typed `state_rel_thm` source statement. It is
untagged while the oracle relation and its carriers remain unreviewed against
HOL. -/
noncomputable def stateRel {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) : Prop :=
  target.ffi = source.ffi ∧
  target.clock = source.clock ∧
  target.handler = source.handler ∧
  target.gcFun = WordGcFunctions.wordGcFun conf ∧
  codeRel conf source.code target.code ∧
  codeOracleRel conf source.compile source.compileOracle target.store target.compile
    target.compileOracle target.codeBuffer target.dataBuffer ∧
  goodDimindex width ∧ shiftLength conf < width ∧ source.tstamps.isSome ∧
  (∀ key ∈ [WordStore.globals], (target.store.lookup key).isSome) ∧
  (values = none → sptLookup 0 target.locals = some (.loc l1 l2)) ∧
  (∀ n, (sptLookup n source.locals).isSome →
    (sptLookup (adjustVar n) target.locals).isSome) ∧
  List.Forall₂ stackRel source.stack target.stack ∧
  List.Forall₂ containsLoc target.stack locs ∧
  optionLe (Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize) target.stackMax ∧
  optionLe target.stackMax source.stackMax ∧
  target.stackSize = source.stackFrameSizes ∧
  target.localsSize = source.localsSize ∧
  limitsInv source.limits (target.store.lookup .heapLength) target.stackLimit
    conf.lenSize conf.hasFpOps conf.hasFpTern ∧
  Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain
    (values.getD [] ++
      joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
      [(theGlobal source.global, holFapply target.store .globals)] ++
      flatStack source.stack target.stack)

/-- Replacing both clocks by the same value preserves the complete relation.
The HOL tag is pending review of `stateRel`'s compiler dependencies. -/
theorem stateRel_withClock {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (clock : Nat)
    (related : stateRel conf l1 l2 source target values locs) :
    stateRel conf l1 l2 { source with clock := clock } { target with clock := clock } values locs := by
  exact ⟨related.1, rfl, related.2.2⟩

/-- The complete relation does not constrain the word state's FP registers.
The HOL tag is pending review of `stateRel`'s compiler dependencies. -/
theorem stateRel_withFpRegs {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (fpRegs : HolFiniteMapExact Nat (BitVec 64))
    (related : stateRel conf l1 l2 source target values locs) :
    stateRel conf l1 l2 source { target with fpRegs := fpRegs } values locs := by
  exact related

/-- A present source local has an adjusted target local under the complete
relation. The HOL tag is pending review of `stateRel`'s compiler dependencies. -/
theorem stateRel_getVar {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (n : Nat) (value : DataSem.Value)
    (related : stateRel conf l1 l2 source target values locs)
    (found : DataSem.getVar n source.locals = some value) :
    ∃ word, WordSemStateFiniteExact.getVar (adjustVar n) target = some word := by
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, targetPresent, _⟩
  have present : (sptLookup n source.locals).isSome := by
    change sptLookup n source.locals = some value at found
    simp [found]
  obtain ⟨word, hword⟩ := Option.isSome_iff_exists.mp (targetPresent n present)
  exact ⟨word, hword⟩

/-- Reading a list of source locals yields a same-length list of adjusted
target locals. The HOL tag is pending review of `stateRel`'s dependencies. -/
theorem stateRel_getVars {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : List Nat) (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (found : DataSem.getVars names source.locals = some values) :
    ∃ words, WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words ∧
      values.length = words.length := by
  induction names generalizing values with
  | nil =>
    simp [DataSem.getVars] at found
    subst values
    exact ⟨[], rfl, rfl⟩
  | cons name names ih =>
    cases head : DataSem.getVar name source.locals with
    | none => simp [DataSem.getVars, head] at found
    | some value =>
      cases tail : DataSem.getVars names source.locals with
      | none => simp [DataSem.getVars, head, tail] at found
      | some rest =>
        have valuesEq : values = value :: rest := by
          simpa [DataSem.getVars, head, tail] using found.symm
        subst values
        obtain ⟨word, wordFound⟩ := stateRel_getVar conf l1 l2 source target none locs name value related head
        obtain ⟨words, wordsFound, lengths⟩ := ih rest tail
        refine ⟨word :: words, ?_, ?_⟩
        · simp [WordSemStateFiniteExact.getVars, wordFound, wordsFound]
        · simpa using lengths

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
