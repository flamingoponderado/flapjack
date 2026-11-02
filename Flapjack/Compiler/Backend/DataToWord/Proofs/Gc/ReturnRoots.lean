import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
import Mathlib.Tactic

/-! Local values as roots of the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A matched pair of source and target locals occurs in the joined root list. -/
theorem localPair_mem_joinEnv (source : Spt DataSem.Value) (target : Spt (WordLocW 64))
    (n : Nat) (value : DataSem.Value) (word : WordLocW 64)
    (sourceLookup : sptLookup n source = some value) (targetLookup : sptLookup (adjustVar n) target = some word) :
    (value, word) ∈ joinEnv source (sptToAList (sptInter target (adjustSet source))) := by
  have adjusted : sptLookup (adjustVar n) (adjustSet source) = some () := by
    rw [lookup_adjustSet_map, sourceLookup]
    rfl
  have intersection : sptLookup (adjustVar n) (sptInter target (adjustSet source)) = some word := by
    rw [sptLookup_sptInterCases, targetLookup, adjusted]
  have member := (sptMemToAList (sptInter target (adjustSet source)) (adjustVar n) word).mpr intersection
  apply List.mem_map.mpr
  refine ⟨(adjustVar n, word), List.mem_filter.mpr ⟨member, ?_⟩, ?_⟩
  · simp [adjustVar]
  · simp [adjustVar, sourceLookup, holThe]

/-- Looking up matching local lists yields paired roots already represented in
`joinEnv`, including repeated source names. -/
theorem getVars_zip_mem_joinEnv {C F : Type} (source : DataSem.State C F)
    (target : WordSemStateFiniteExact 64 C F) (names : List Nat)
    (values : List DataSem.Value) (words : List (WordLocW 64))
    (sourceRun : DataSem.getVars names source.locals = some values)
    (targetRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words) :
    ∀ pair ∈ values.zip words, pair ∈ joinEnv source.locals
      (sptToAList (sptInter target.locals (adjustSet source.locals))) := by
  induction names generalizing values words with
  | nil =>
    simp [DataSem.getVars] at sourceRun
    subst values
    simp
  | cons name names ih =>
    cases one : DataSem.getVar name source.locals with
    | none => simp [DataSem.getVars, one] at sourceRun
    | some value =>
      cases rest : DataSem.getVars names source.locals with
      | none => simp [DataSem.getVars, one, rest] at sourceRun
      | some values' =>
        simp [DataSem.getVars, one, rest] at sourceRun
        subst values
        cases word : WordSemStateFiniteExact.getVar (adjustVar name) target with
        | none => simp [WordSemStateFiniteExact.getVars, word] at targetRun
        | some w =>
          cases more : WordSemStateFiniteExact.getVars (names.map adjustVar) target with
          | none => simp [WordSemStateFiniteExact.getVars, word, more] at targetRun
          | some ws =>
            simp [WordSemStateFiniteExact.getVars, word, more] at targetRun
            subst words
            intro pair member
            simp only [List.zip_cons_cons, List.mem_cons] at member
            rcases member with rfl | tail
            · exact localPair_mem_joinEnv source.locals target.locals name value w one word
            · exact ih values' ws rest more pair tail

/-- Returning matched locals adds their paired values to the roots without
changing either machine state. -/
theorem stateRel64_returnRoots {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (values : List DataSem.Value) (words : List (WordLocW 64))
    (sourceRun : DataSem.getVars names source.locals = some values)
    (targetRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words) :
    stateRel64 conf l1 l2 source target (some (values.zip words)) locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals,
    zero, locals, stack, locations, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  refine ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals, ?_, locals,
    stack, locations, stackBound, maxBound, stackSize, localSize, limits, ?_⟩
  · intro impossible
    cases impossible
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    · intro pair member
      simp only [Option.getD_some, List.mem_append] at member ⊢
      rcases member with ((returned | joined) | global) | stack
      · exact Or.inl (Or.inl (getVars_zip_mem_joinEnv source target names values words sourceRun targetRun pair returned))
      · exact Or.inl (Or.inl joined)
      · exact Or.inl (Or.inr global)
      · exact Or.inr stack
    · simpa using memory

/-- Flushing locals after return retains the paired return roots and the
memory invariant; the stack-size obligation weakens as locals are cleared. -/
theorem stateRel64_flushReturn {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (roots : List (DataSem.Value × WordLocW 64))
    (related : stateRel64 conf l1 l2 source target (some roots) locs) :
    stateRel64 conf l1 l2 (DataSem.flushState false source) (WordSemStateFiniteExact.flushState false target)
      (some roots) locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals,
    zero, locals, stack, locations, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  refine ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals, ?_, ?_,
    stack, locations, ?_, maxBound, stackSize, rfl, limits, ?_⟩
  · intro impossible
    cases impossible
  · intro n present
    simp [DataSem.flushState] at present
  · have reduced : ∀ a b c, BackendProps.optionLe (wordSemOptionAdd a b) c →
        BackendProps.optionLe (wordSemOptionAdd a (some 0)) c := by
      intro a b c bound
      cases a <;> cases b <;> cases c <;> simp_all [wordSemOptionAdd, BackendProps.optionLe]
      omega
    exact reduced _ _ _ stackBound
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (roots ++ joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    · intro pair member
      change pair ∈ roots ++ joinEnv (.ln : Spt DataSem.Value)
        (sptToAList (sptInter (.ln : Spt (WordLocW 64)) (adjustSet (.ln : Spt DataSem.Value)))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack at member
      have emptyJoin : joinEnv (.ln : Spt DataSem.Value)
          (sptToAList (sptInter (.ln : Spt (WordLocW 64)) (adjustSet (.ln : Spt DataSem.Value)))) = [] := by
        simp [joinEnv, sptInter, sptToAList, sptFoldi]
      rw [emptyJoin] at member
      simp only [List.append_nil, List.mem_append] at member ⊢
      rcases member with (inRoots | global) | inStack
      · exact Or.inl (Or.inl (Or.inl inRoots))
      · exact Or.inl (Or.inr global)
      · exact Or.inr inStack
    · simpa using memory

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
