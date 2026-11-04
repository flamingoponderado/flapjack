import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.IndirectCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PushCall

/-! Non-tail call setup for indirect code-pointer calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Indirect lookup, live-set cutting and saving the caller together establish
related callee states, with or without an installed handler. -/
theorem stateRel64_findCode_indirect_pushCall {C F : Type} (conf : Config) (l1 l2 r1 r2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (label : Nat) (names : List Nat) (lastName : Nat) (values : List DataSem.Value) (body : DataLang.Prog)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr label))
    (lookup : sptLookup label source.code = some (values.length, body))
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    ∃ words,
      DataSem.getVars (names ++ [lastName]) source.locals = some (values ++ [.codePtr label]) ∧
      WordSemStateFiniteExact.getVars ((names ++ [lastName]).map adjustVar) target = some (words ++ [.loc label 0]) ∧
      DataSem.findCode none (values ++ [.codePtr label]) source.code source.stackFrameSizes =
        some (values, body, sptLookup label source.stackFrameSizes) ∧
      wordSemFindCode none ((.loc r1 r2 :: words) ++ [.loc label 0]) target.code target.stackSize =
        some (.loc r1 r2 :: words, (compileControl64 conf label 2 body).1, sptLookup label source.stackFrameSizes) ∧
      wordSemCutEnvs (adjustSets live) target.locals =
        some (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) ∧
      stateRel64 conf r1 r2
        (DataSem.callEnv values (sptLookup label source.stackFrameSizes)
          (DataSem.pushEnv saved handler.isSome (DataSem.decClock source)))
        (WordSemStateFiniteExact.callEnv (.loc r1 r2 :: words) (sptLookup label source.stackFrameSizes)
          (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
            handler (WordSemStateFiniteExact.decClock target))) none ((l1, l2) :: locs) := by
  obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  have codePtr := stateRel64_getCodePtr conf l1 l2 source target locs related lastName label pointer
  have sourceAll := dataGetVars_snoc names values lastName (.codePtr label) source.locals sourceRun pointer
  have wordAll := wordGetVars_snoc (names.map adjustVar) words (adjustVar lastName) (.loc label 0) target wordRun codePtr
  obtain ⟨_, _, _, sourceCode, _, _⟩ :=
    stateRel64_findCode_indirect_callEnv conf l1 l2 source target locs related label names lastName values body sourceRun pointer lookup
  refine ⟨words, sourceAll, ?_, sourceCode,
    stateRel64_findCode_indirect conf l1 l2 source target locs related r1 r2 label values.length body values words lengths rfl lookup,
    stateRel64_cutEnvs conf l1 l2 source target locs related live saved cut,
    stateRel64_pushCall conf l1 l2 r1 r2 source target locs related names values words _ sourceRun wordRun live saved cut handler⟩
  simpa [List.map_append] using wordAll

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
