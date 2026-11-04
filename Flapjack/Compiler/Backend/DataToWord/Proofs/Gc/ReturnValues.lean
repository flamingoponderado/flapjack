import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PopEnv
import Flapjack.Misc.Sptree.UnionAlgebra

/-! Installing multiple returned values in the restored caller. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Installing one represented pair preserves all separately tracked roots. -/
theorem stateRel64_setNewLocal_withRoots {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (roots : List (DataSem.Value × WordLocW 64)) (dest : Nat) (value : DataSem.Value) (word : WordLocW 64)
    (present : (value, word) ∈ roots)
    (memory : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (roots ++ joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) :
    stateRel64 conf l1 l2 (DataSem.setVar dest value source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) none locs ∧
    Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (roots ++ joinEnv (DataSem.setVar dest value source).locals
        (sptToAList (sptInter (WordSemStateFiniteExact.setVar (adjustVar dest) word target).locals
          (adjustSet (DataSem.setVar dest value source).locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) := by
  have installed : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((value, word) :: (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) := by
    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain _ _ ?_ memory
    intro pair member
    simp only [List.mem_cons, List.mem_append] at member ⊢
    rcases member with same | (old | global) | stack
    · subst pair
      exact Or.inl (Or.inl (Or.inl present))
    · exact Or.inl (Or.inl (Or.inr old))
    · exact Or.inl (Or.inr global)
    · exact Or.inr stack
  refine ⟨stateRel64_setNewLocal conf l1 l2 source target locs related dest value word installed, ?_⟩
  apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain _ _ ?_ memory
  intro pair member
  change pair ∈ roots ++ joinEnv (sptInsert dest value source.locals)
    (sptToAList (sptInter (sptInsert (adjustVar dest) word target.locals) (adjustSet (sptInsert dest value source.locals)))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack at member
  simp only [List.mem_append] at member ⊢
  rcases member with ((root | newLocal) | global) | stack
  · exact Or.inl (Or.inl (Or.inl root))
  · have inNew := joinEnv_insert_subset source.locals target.locals dest value word pair newLocal
    simp only [List.mem_cons] at inNew
    rcases inNew with same | old
    · subst pair
      exact Or.inl (Or.inl (Or.inl present))
    · exact Or.inl (Or.inl (Or.inr old))
  · exact Or.inl (Or.inr global)
  · exact Or.inr stack

/-- Inserting a head association before a tree union is a literal insertion
into the union, including malformed sparse trees. -/
theorem sptUnion_insert_left {α : Type} (key : Nat) (value : α) (left right : Spt α) :
    sptUnion (sptInsert key value left) right = sptInsert key value (sptUnion left right) := by
  rw [sptInsert_union key value left, ← sptUnion_assoc, sptUnion_insert_ln]

/-- Setting a nonempty list has the same first-match order as setting its tail
and then its head, on both evaluators. -/
theorem dataSetVars_cons {C F : Type} (name : Nat) (names : List Nat) (value : DataSem.Value)
    (values : List DataSem.Value) (source : DataSem.State C F) :
    DataSem.setVars (name :: names) (value :: values) source =
      DataSem.setVar name value (DataSem.setVars names values source) := by
  simp [DataSem.setVars, DataSem.setVar, sptFromAList, sptUnion_insert_left]

theorem wordSetVars_cons {C F : Type} (name : Nat) (names : List Nat) (value : WordLocW 64)
    (values : List (WordLocW 64)) (target : WordSemStateFiniteExact 64 C F) :
    WordSemStateFiniteExact.setVars (name :: names) (value :: values) target =
      WordSemStateFiniteExact.setVar name value (WordSemStateFiniteExact.setVars names values target) := by
  rfl

/-- A list of represented return pairs can be installed with the same
first-match semantics on both sides. All supplied roots remain represented. -/
theorem stateRel64_setNewLocals_withRoots {C F : Type} (conf : Config) (l1 l2 : Nat)
    (names : List Nat) (values : List DataSem.Value) (words : List (WordLocW 64))
    (sameNames : names.length = values.length) (sameValues : values.length = words.length)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (roots : List (DataSem.Value × WordLocW 64)) (included : values.zip words ⊆ roots)
    (memory : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (roots ++ joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) :
    stateRel64 conf l1 l2 (DataSem.setVars names values source)
      (WordSemStateFiniteExact.setVars (names.map adjustVar) words target) none locs ∧
    Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (roots ++ joinEnv (DataSem.setVars names values source).locals
        (sptToAList (sptInter (WordSemStateFiniteExact.setVars (names.map adjustVar) words target).locals
          (adjustSet (DataSem.setVars names values source).locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) := by
  induction names generalizing values words with
  | nil =>
    cases values with
    | cons value values => simp at sameNames
    | nil =>
      cases words with
      | cons word words => simp at sameValues
      | nil => simpa [DataSem.setVars, WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert, sptFromAList, sptUnion] using And.intro related memory
  | cons name names ih =>
    cases values with
    | nil => simp at sameNames
    | cons value values =>
      cases words with
      | nil => simp at sameValues
      | cons word words =>
        have tailIncluded : values.zip words ⊆ roots := by
          intro pair member
          apply included
          exact List.mem_cons_of_mem _ member
        have headIncluded : (value, word) ∈ roots := included (List.mem_cons_self)
        have tail := ih values words (by simpa using sameNames) (by simpa using sameValues) tailIncluded
        have result := stateRel64_setNewLocal_withRoots conf l1 l2
          (DataSem.setVars names values source) (WordSemStateFiniteExact.setVars (names.map adjustVar) words target)
          locs tail.1 roots name value word headIncluded (by simpa [DataSem.setVars, WordSemStateFiniteExact.setVars] using tail.2)
        rw [dataSetVars_cons, List.map_cons, wordSetVars_cons]
        simpa [DataSem.setVars, WordSemStateFiniteExact.setVars, DataSem.setVar, WordSemStateFiniteExact.setVar] using result

/-- Returning any equal-length sequence of values restores the caller's
relation after the corresponding local assignments. -/
theorem stateRel64_popEnv_setVars {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (names : List Nat) (values : List DataSem.Value) (words : List (WordLocW 64))
    (sameNames : names.length = values.length) (sameValues : values.length = words.length)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target (some (values.zip words)) locs)
    (pop : DataSem.popEnv source = some next) :
    ∃ targetNext return1 return2 remaining,
      WordSemStateFiniteExact.popEnv target = some targetNext ∧
      locs = (return1, return2) :: remaining ∧
      stateRel64 conf return1 return2 (DataSem.setVars names values next)
        (WordSemStateFiniteExact.setVars (names.map adjustVar) words targetNext) none remaining := by
  obtain ⟨targetNext, r1, r2, remaining, targetPop, locations, after, carried⟩ :=
    stateRel64_popEnv conf l1 l2 source next target (values.zip words) locs related pop
  refine ⟨targetNext, r1, r2, remaining, targetPop, locations, ?_⟩
  exact (stateRel64_setNewLocals_withRoots conf r1 r2 names values words sameNames sameValues
    next targetNext remaining after (values.zip words) (List.Subset.refl _) carried).1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
