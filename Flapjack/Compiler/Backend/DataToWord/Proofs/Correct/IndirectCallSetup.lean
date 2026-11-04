import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.IndirectPushCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallTimeout

/-! Source and target setup for an indirect returning call. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Successful indirect source setup determines the word code pointer,
argument list, live-set cut and related entry state. -/
theorem indirectCall64_setup {C F : Type} (conf : Config) (secn fresh l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    DataSem.getVars (names ++ [lastName]) source.locals = some (values ++ [.codePtr callee]) ∧
    WordSemStateFiniteExact.getVars ((names ++ [lastName]).map adjustVar) target = some (args ++ [.loc callee 0]) ∧
    DataSem.findCode none (values ++ [.codePtr callee]) source.code source.stackFrameSizes =
      some (values, body, sptLookup callee source.stackFrameSizes) ∧
    wordSemFindCode none ((.loc secn fresh :: args) ++ [.loc callee 0]) target.code target.stackSize =
      some (.loc secn fresh :: args, (compileControl64 conf callee 2 body).1, sptLookup callee source.stackFrameSizes) ∧
    wordSemCutEnvs (adjustSets live) target.locals =
      some (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) ∧
    ¬ sptDomainEmpty (.ls () : NumSet) ∧ (returns.map adjustVar).Nodup ∧
    stateRel64 conf secn fresh
      (DataSem.callEnv values (sptLookup callee source.stackFrameSizes) (DataSem.pushEnv saved handler.isSome (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn fresh :: args) (sptLookup callee source.stackFrameSizes)
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) handler
          (WordSemStateFiniteExact.decClock target))) none ((l1, l2) :: locs) := by
  obtain ⟨words, sourceAll, wordAll, sourceCode, wordCode, wordCut, entered⟩ :=
    stateRel64_findCode_indirect_pushCall conf l1 l2 secn fresh source target locs related callee names lastName values body
      sourceRun pointer lookup live saved cut handler
  have ptr := stateRel64_getCodePtr conf l1 l2 source target locs related lastName callee pointer
  have expectedAll := wordGetVars_snoc (names.map adjustVar) args (adjustVar lastName) (.loc callee 0) target wordRun ptr
  have equalArgs : words = args := by
    have eq : some (words ++ [.loc callee 0]) = some (args ++ [.loc callee 0]) := by
      calc
        some (words ++ [.loc callee 0]) = WordSemStateFiniteExact.getVars ((names ++ [lastName]).map adjustVar) target := wordAll.symm
        _ = some (args ++ [.loc callee 0]) := by simpa [List.map_append] using expectedAll
    simpa using Option.some.inj eq
  subst words
  refine ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, ?_, ?_, entered⟩
  · intro empty
    apply empty 0
    exact (sptMem_iff_lookup 0 (.ls ())).mpr ⟨(), rfl⟩
  · apply List.Nodup.map_on ?_ distinct
    intro x _ y _ eq
    simp only [adjustVar] at eq
    omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
