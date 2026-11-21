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

/-! Complete data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps

namespace stateRelMap
/-- Canonical roundtrip for the target state's finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state roundtrip for relations with additional map inputs. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end stateRelMap

/-- The full relation between data and word states, including compiled code,
callbacks, stack shape, resource limits, and the GC-compatible memory
abstraction. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_thm" 4503
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def stateRel {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
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

/-- Replacing both clocks by the same value preserves the complete relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_withClock {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (clock : Nat)
    (related : stateRel conf l1 l2 source target values locs) :
    stateRel conf l1 l2 { source with clock := clock } { target with clock := clock } values locs := by
  exact ⟨related.1, rfl, related.2.2⟩

/-- The complete relation does not constrain the word state's FP registers. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_with_fp_regs"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, fpRegs]) (words_as_type_indexed_bitvec)]
theorem stateRel_withFpRegs {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (fpRegs : HolFiniteMapExact Nat (BitVec 64))
    (related : stateRel conf l1 l2 source target values locs) :
    stateRel conf l1 l2 source { target with fpRegs := fpRegs } values locs := by
  exact related

/-- A present source local has an adjusted target local under the complete relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_get_var_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_getVar {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (n : Nat) (value : Flapjack.Compiler.Backend.DataSem.Value)
    (related : stateRel conf l1 l2 source target values locs)
    (found : DataSem.getVar n source.locals = some value) :
    ∃ word, WordSemStateFiniteExact.getVar (adjustVar n) target = some word := by
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, targetPresent, _⟩
  have present : (sptLookup n source.locals).isSome := by
    change sptLookup n source.locals = some value at found
    simp [found]
  obtain ⟨word, hword⟩ := Option.isSome_iff_exists.mp (targetPresent n present)
  exact ⟨word, hword⟩

/-- Reading a list of source locals yields a same-length list of adjusted target locals. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_get_vars_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_getVars {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value)
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

/-- Reading the reserved return location followed by adjusted source locals. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_0_get_vars_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_zero_getVars {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (found : DataSem.getVars names source.locals = some values) :
    ∃ words, WordSemStateFiniteExact.getVars (0 :: names.map adjustVar) target =
      some (.loc l1 l2 :: words) ∧ values.length = words.length := by
  obtain ⟨words, read, length⟩ := stateRel_getVars conf l1 l2 source target locs names values related found
  have zero := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  refine ⟨words, ?_, length⟩
  simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, zero, read]


/-- Updating AllocSize leaves the complete data-to-word state relation unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_set_store_AllocSize"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_setStore_allocSize {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (locs : List (Nat × Nat)) (w : BitVec width) :
    stateRel conf l1 l2 s (WordSemStateFiniteExact.setStore .allocSize (.word w) t) v locs =
      stateRel conf l1 l2 s t v locs := by
  simp [stateRel, WordSemStateFiniteExact.setStore, codeOracleRel, Memory.memoryRel,
    Memory.heapInMemoryStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, holFapply]

/-- Exact HOL `blocks_unique_empty` (`data_to_word_gcProofScript.sml:4600-4606`,
a `[local]` theorem): no value lies in the empty heap and stack. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "blocks_unique_empty"]
theorem blocksUnique_empty {v : Nat} :
    Memory.blocksUnique v (Memory.allValues Spt.ln []) := by
  intro stamp tag1 xs1 tag2 xs2 ⟨h, _⟩
  exfalso
  simp [Memory.allValues, sptLookup, Memory.valueListValues] at h

/-- Exact HOL `state_rel_imp_clock` (`data_to_word_gcProofScript.sml:8598-8602`); HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_imp_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem state_rel_imp_clock {width : Nat} [NeZero width] {C F : Type} {c : Config}
    {l1 l2 : Nat} {s : DataSem.State C F} {t : WordSemStateFiniteExact width C F}
    {locs : List (Nat × Nat)} :
    stateRel c l1 l2 s t none locs → s.clock = t.clock :=
  fun h => h.2.1.symm

/-- Exact HOL `state_rel_with_clock_0` (`data_to_word_gcProofScript.sml:8564-8570`); HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_with_clock_0"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem state_rel_with_clock_0 {width : Nat} [NeZero width] {C F : Type} {c : Config}
    {r1 r2 : Nat} {s : DataSem.State C F} {t : WordSemStateFiniteExact width C F}
    {x : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))}
    {locs : List (Nat × Nat)} :
    stateRel c r1 r2 s t x locs → stateRel c r1 r2 { s with space := 0 } t x locs := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    heap, limit, a, sp, sp1, gens, m1, m2, m3, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    heap, limit, a, sp, sp1, gens, m1, m2, m3, Nat.zero_le _⟩

/-- Exact HOL `state_rel_def` (`data_to_word_gcProofScript.sml:4541-4542`): the original relation with `memory_rel` unfolded; HOL free
variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem state_rel_def {width : Nat} [NeZero width] {C F : Type} :
    ∀ (c : Config) (l1 l2 : Nat) (s : DataSem.State C F)
      (t : WordSemStateFiniteExact width C F)
      (v1 : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
      (locs : List (Nat × Nat)),
      stateRel c l1 l2 s t v1 locs ↔
        t.ffi = s.ffi ∧
        t.clock = s.clock ∧
        t.handler = s.handler ∧
        t.gcFun = WordGcFunctions.wordGcFun c ∧
        codeRel c s.code t.code ∧
        codeOracleRel c s.compile s.compileOracle t.store t.compile
          t.compileOracle t.codeBuffer t.dataBuffer ∧
        goodDimindex width ∧ shiftLength c < width ∧ s.tstamps.isSome ∧
        (∀ key ∈ [WordStore.globals], (t.store.lookup key).isSome) ∧
        (v1 = none → sptLookup 0 t.locals = some (.loc l1 l2)) ∧
        (∀ n, (sptLookup n s.locals).isSome →
          (sptLookup (adjustVar n) t.locals).isSome) ∧
        List.Forall₂ stackRel s.stack t.stack ∧
        List.Forall₂ containsLoc t.stack locs ∧
        optionLe (Option.map₂ (· + ·) (wordSemStackSize t.stack) t.localsSize) t.stackMax ∧
        optionLe t.stackMax s.stackMax ∧
        t.stackSize = s.stackFrameSizes ∧
        t.localsSize = s.localsSize ∧
        limitsInv s.limits (t.store.lookup .heapLength) t.stackLimit
          c.lenSize c.hasFpOps c.hasFpTern ∧
        ∃ heap limit a sp sp1 gens,
          Memory.heapInMemoryStore heap a sp sp1 gens c t.store t.memory t.mdomain limit ∧
          Memory.wordMlInv (heap, t.be, a, sp, sp1, gens) limit (holThe s.tstamps) c s.refs
            (v1.getD [] ++
              joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++
              [(theGlobal s.global, holFapply t.store .globals)] ++
              flatStack s.stack t.stack) ∧
          (limit + 3) * (width / 8) + 1 < 2 ^ width ∧ s.space ≤ sp :=
  fun _ _ _ _ _ _ _ => Iff.rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
