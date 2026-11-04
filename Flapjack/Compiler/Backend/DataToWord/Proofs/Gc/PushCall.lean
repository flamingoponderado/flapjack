import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnv

/-! State relation at non-tail call entry after saving the caller. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

private theorem optionMaxMono (a b x : Option Nat) (rel : BackendProps.optionLe a b) :
    BackendProps.optionLe (wordSemOptionMax a x) (Option.map₂ max b x) := by
  cases a <;> cases b <;> cases x <;> simp_all [wordSemOptionMax, BackendProps.optionLe]
  omega

private theorem optionAdd_eq (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
  cases a <;> cases b <;> rfl

/-- Cutting and saving caller locals followed by call entry preserves the
candidate data-to-word state relation for either optional handler. -/
theorem stateRel64_pushCall {C F : Type} (conf : Config) (l1 l2 r1 r2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (names : List Nat) (values : List DataSem.Value) (words : List (WordLocW 64)) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    stateRel64 conf r1 r2
      (DataSem.callEnv values size (DataSem.pushEnv saved handler.isSome (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc r1 r2 :: words) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          handler (WordSemStateFiniteExact.decClock target))) none ((l1, l2) :: locs) := by
  let sp := DataSem.pushEnv saved handler.isSome (DataSem.decClock source)
  let tp := WordSemStateFiniteExact.pushEnv
    (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) handler (WordSemStateFiniteExact.decClock target)
  have pushFacts := stateRel64_pushEnv_stacks conf l1 l2 source target locs related live saved cut handler
  have stackRel : List.Forall₂ stackRel sp.stack tp.stack := by
    cases handler with
    | none => simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock] using pushFacts.1
    | some info =>
      obtain ⟨a, b, c, d⟩ := info
      simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock] using pushFacts.1
  have locations : List.Forall₂ containsLoc tp.stack ((l1, l2) :: locs) := by
    cases handler with
    | none => simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock] using pushFacts.2.1
    | some info =>
      obtain ⟨a, b, c, d⟩ := info
      simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock] using pushFacts.2.1
  have roots : flatStack sp.stack tp.stack ⊆
      joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ flatStack source.stack target.stack := by
    cases handler with
    | none => simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock] using pushFacts.2.2.2
    | some info =>
      obtain ⟨a, b, c, d⟩ := info
      simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock] using pushFacts.2.2.2
  have stackEq := stackRel_sizeOfStack stackRel
  have handlers : tp.handler = sp.handler := by
    have lengths := related.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
    have equal := related.2.2.1
    cases handler with
    | none => simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.decClock] using equal
    | some info =>
      obtain ⟨a, b, c, d⟩ := info
      simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.decClock] using lengths.symm
  have pushBound : BackendProps.optionLe tp.stackMax sp.stackMax := by
    have h : BackendProps.optionLe (wordSemOptionMax target.stackMax (wordSemStackSize tp.stack))
        (Option.map₂ max source.stackMax (DataSem.sizeOfStack sp.stack)) := by
      rw [stackEq]
      exact optionMaxMono _ _ _ related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cases handler with
    | none => simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.decClock] using h
    | some info =>
      obtain ⟨a, b, c, d⟩ := info
      simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.decClock] using h
  obtain ⟨words', targetRun, sameLength⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  rw [wordRun] at targetRun
  have equal : words = words' := Option.some.inj targetRun
  subst words'
  have zipped := getVars_zip_mem_joinEnv source target names values words sourceRun wordRun
  have oldFfi := related.1
  have oldClock := related.2.1
  have oldGc := related.2.2.2.1
  have oldCode := related.2.2.2.2.1
  have oldOracle := related.2.2.2.2.2.1
  have dim := related.2.2.2.2.2.2.1
  have shift := related.2.2.2.2.2.2.2.1
  have stamps := related.2.2.2.2.2.2.2.2.1
  have globals := related.2.2.2.2.2.2.2.2.2.1
  have sizeEq := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have memory := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  change stateRel64 conf r1 r2 (DataSem.callEnv values size sp)
    (WordSemStateFiniteExact.callEnv (.loc r1 r2 :: words) size tp) none ((l1, l2) :: locs)
  refine ⟨?_, ?_, handlers, ?_, ?_, ?_, dim, shift, ?_, ?_, ?_, ?_, stackRel, locations, ?_, ?_, ?_, rfl, ?_, ?_⟩
  all_goals try { cases handler with
    | none => simp_all [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock, DataSem.callEnv, WordSemStateFiniteExact.callEnv]
    | some info => obtain ⟨a, b, c, d⟩ := info; simp_all [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock, WordSemStateFiniteExact.decClock, DataSem.callEnv, WordSemStateFiniteExact.callEnv] }
  · intro _
    exact callEnv_returnLocation (.loc r1 r2) words
  · intro n present
    exact callEnv_argument_present values words (.loc r1 r2) sameLength n present
  · change BackendProps.optionLe (wordSemOptionAdd (wordSemStackSize tp.stack) size)
      (wordSemOptionMax tp.stackMax (wordSemOptionAdd (wordSemStackSize tp.stack) size))
    cases tp.stackMax <;> cases wordSemStackSize tp.stack <;> cases size <;>
      simp [wordSemOptionAdd, wordSemOptionMax, BackendProps.optionLe]
  · change BackendProps.optionLe (wordSemOptionMax tp.stackMax (wordSemOptionAdd (wordSemStackSize tp.stack) size))
      (Option.map₂ max sp.stackMax (Option.map₂ (· + ·) (DataSem.sizeOfStack sp.stack) size))
    rw [stackEq, optionAdd_eq]
    exact optionMaxMono _ _ _ pushBound
  · have finalMemory : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        (joinEnv (sptFromList values) (sptToAList (sptInter (sptFromList2 (.loc r1 r2 :: words)) (adjustSet (sptFromList values)))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack sp.stack tp.stack) := by
      apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain _ _ ?_ memory
      intro pair member
      simp only [Option.getD_none, List.nil_append, List.mem_append] at member ⊢
      rcases member with (localRoot | globalRoot) | stackRoot
      · exact Or.inl (Or.inl (zipped pair (callEnv_joined_subset values words (.loc r1 r2) localRoot)))
      · exact Or.inl (Or.inr globalRoot)
      · have oldRoot := roots stackRoot
        simp only [List.mem_append] at oldRoot
        exact oldRoot.elim (fun root => Or.inl (Or.inl root)) Or.inr
    cases handler with
    | none => simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.decClock, DataSem.callEnv, WordSemStateFiniteExact.callEnv] using finalMemory
    | some info =>
      obtain ⟨a, b, c, d⟩ := info
      simpa [sp, tp, DataSem.pushEnv, WordSemStateFiniteExact.pushEnv, DataSem.decClock,
        WordSemStateFiniteExact.decClock, DataSem.callEnv, WordSemStateFiniteExact.callEnv] using finalMemory

/-- A direct non-tail call finds the compiled body, cuts the target live
sets, and starts the callee in related states after saving the caller. -/
theorem stateRel64_findCode_direct_pushCall {C F : Type} (conf : Config) (l1 l2 r1 r2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (names : List Nat) (values : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (found : DataSem.findCode (some label) values source.code source.stackFrameSizes = some (values, body, size))
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    ∃ words,
      WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words ∧
      wordSemFindCode (some label) (.loc r1 r2 :: words) target.code target.stackSize =
        some (.loc r1 r2 :: words, (compileControl64 conf label 2 body).1, size) ∧
      wordSemCutEnvs (adjustSets live) target.locals =
        some (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) ∧
      stateRel64 conf r1 r2
        (DataSem.callEnv values size (DataSem.pushEnv saved handler.isSome (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv (.loc r1 r2 :: words) size
          (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
            handler (WordSemStateFiniteExact.decClock target))) none ((l1, l2) :: locs) := by
  obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  exact ⟨words, wordRun,
    stateRel64_findCode_direct conf l1 l2 source target locs related r1 r2 label values words body size lengths found,
    stateRel64_cutEnvs conf l1 l2 source target locs related live saved cut,
    stateRel64_pushCall conf l1 l2 r1 r2 source target locs related names values words size sourceRun wordRun live saved cut handler⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
