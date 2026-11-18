module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvInsert
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! The `Move` case of the data-to-word evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Updating matching locals preserves the state relation when their pair is
already represented in the memory roots. This shared proof step supports the
HOL Move and constant-assignment cases; it has no standalone HOL declaration. -/
theorem stateRel_insertRoot {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (value : DataSem.Value) (word : WordLocW width)
    (related : stateRel conf l1 l2 source target none locs)
    (root : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((value, word) :: joinEnv source.locals
        (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) :
    stateRel conf l1 l2 (DataSem.setVar dest value source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, ?_, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
  · intro _
    change sptLookup 0 (sptInsert (adjustVar dest) word target.locals) = some (.loc l1 l2)
    rw [sptLookup_sptInsert_ne (adjustVar dest) 0 word target.locals (by simp [adjustVar])]
    exact hzero rfl
  · intro key hsource
    change (sptLookup key (sptInsert dest value source.locals)).isSome at hsource
    change (sptLookup (adjustVar key) (sptInsert (adjustVar dest) word target.locals)).isSome
    by_cases same : key = dest
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne dest key value source.locals same] at hsource
      have adjustNe : adjustVar key ≠ adjustVar dest := by
        simp only [adjustVar]
        omega
      rw [sptLookup_sptInsert_ne (adjustVar dest) (adjustVar key) word target.locals adjustNe]
      exact hpresent key hsource
  · change memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv (sptInsert dest value source.locals)
        (sptToAList (sptInter (sptInsert (adjustVar dest) word target.locals)
          (adjustSet (sptInsert dest value source.locals)))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := root
    refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
    let rest := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
    have updated := wordMlInv_insert heap target.be a sp sp1 gens limit (holThe source.tstamps)
      conf source.refs source.locals target.locals dest value word rest (by simpa [rest] using hinv)
    simpa [rest] using updated

/-- The Move case obtains its new root from the matching source and word
lookups before applying the shared state-update argument. -/
private theorem stateRel_move {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest src : Nat) (value : DataSem.Value) (word : WordLocW width)
    (related : stateRel conf l1 l2 source target none locs)
    (sourceFound : DataSem.getVar src source.locals = some value)
    (targetFound : WordSemStateFiniteExact.getVar (adjustVar src) target = some word) :
    stateRel conf l1 l2 (DataSem.setVar dest value source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) none locs := by
  apply stateRel_insertRoot conf l1 l2 source target locs dest value word related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
  refine ⟨heap, limit, a, sp, sp1, gens, hstore, ?_, hbound, hspace⟩
  let rest := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have added := wordMlInv_lookup heap target.be a sp sp1 gens limit (holThe source.tstamps)
    conf source.refs [] rest source.locals target.locals src value word
      ⟨by simpa [rest] using hinv, sourceFound, targetFound⟩
  simpa [rest] using added

/-- The full HOL `Move` simulation case, including every result branch. The
HOL tag is pending compiler and state-relation dependency review. The word
evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
theorem dataCompileCorrect_move {width : Nat} [NeZero width] {C F : Type}
    (source : DataSem.State C F) (conf : Config) (n l l1 l2 dest src : Nat)
    (res : Option (Result (List DataSem.Value) DataSem.Value)) (source1 : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (run : DataSem.evaluate (.move dest src) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.move dest src)).1 target = (res1, target1) ∧
      optionLe target1.stackMax source1.stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix source1.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → source1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => stateRel conf l1 l2 source1 target1 none locs ∧ res1 = none
        | some (.val values) =>
            ∃ words, words.length = values.length ∧
              stateRel conf l1 l2 source1 target1 (some (values.zip words)) locs ∧
              res1 = some (.result (.loc l1 l2) words)
        | some (.err (.raise value)) =>
            target1.ffi = source1.ffi ∧
            ∃ word l5 l6 rest,
              res1 = some (.exception (mkLoc (WordSemStateFiniteExact.jumpExc target)) word) ∧
              (WordSemStateFiniteExact.jumpExc target ≠ none →
                wordSemLastN (source1.stack.length + 1) locs = (l5, l6) :: rest ∧
                ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source1)
                  (WordSemStateFiniteExact.setVar (adjustVar i) word target1) none rest)
        | some (.err (.abort (.ffiError event))) =>
            res1 = some (.finalFfi event) ∧ target1.ffi = source1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi) := by
  cases sourceFound : DataSem.getVar src source.locals with
  | none =>
    have bad : res = some (.err (.abort .typeError)) := by
      have h : (some (.err (.abort .typeError)), source) = (res, source1) := by
        simpa [DataSem.evaluate, sourceFound, DataSem.typeError] using run
      exact (congrArg Prod.fst h).symm
    exact (notTypeError bad).elim
  | some value =>
    obtain ⟨word, targetFound⟩ := stateRel_getVar conf l1 l2 source target none locs src value related sourceFound
    have sourceEq : res = none ∧ source1 = DataSem.setVar dest value source := by
      simpa [DataSem.evaluate, sourceFound] using run.symm
    rcases sourceEq with ⟨resEq, sourceEq⟩
    subst res
    subst source1
    have updated := stateRel_move conf l1 l2 source target locs dest src value word related sourceFound targetFound
    have compiled : compileControl (width := width) conf n l (.move dest src) =
        (.move 0 [(adjustVar dest, adjustVar src)], l) := by
      have h := compileControl_option (width := width) conf n l (.move dest src)
      simpa [compileControl?] using h.symm
    have bound : optionLe target.stackMax source.stackMax := by
      rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bound, _⟩
      exact bound
    refine ⟨WordSemStateFiniteExact.setVar (adjustVar dest) word target, none, ?_, bound, ?_, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
        targetFound, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
        LoopSemStateFiniteExact.sptAlistInsert]
    · simp
    · simp [updated]

end Flapjack.Compiler.Backend.DataToWord.Proofs
