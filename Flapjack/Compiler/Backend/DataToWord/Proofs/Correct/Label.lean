import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer

/-! Code-label assignments in the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A code pointer and its word-language location can be installed as locals. -/
theorem stateRel64_setCodePtr {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (dest label : Nat) :
    stateRel64 conf l1 l2 (DataSem.setVar dest (.codePtr label) source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.loc label 0) target) none locs := by
  apply stateRel64_setNewLocal conf l1 l2 source target locs related
  apply Memory.memoryRel_codePtr
  simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- A source code label remains present in the target by the production-backed
code relation, and the generated location assignment installs the same label. -/
theorem assignLabel64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest codeLabel arity : Nat) (body : DataLang.Prog)
    (code : sptLookup codeLabel source.code = some (arity, body)) :
    continues64 conf secn label l1 l2 (.assign dest (.label codeLabel) [] none) source target locs := by
  let op := ClosLang.Op.label codeLabel
  let middle := DataSem.doStack op [] (DataSem.doLimSafe source op [])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op []
  have sourceMem : sptDomain source.code codeLabel := (sptMem_iff_lookup codeLabel source.code).mpr ⟨(arity, body), code⟩
  have targetMem : sptMem codeLabel target.code := related.2.2.2.2.1.1 codeLabel |>.mpr (Or.inl sourceMem)
  refine ⟨DataSem.setVar dest (.codePtr codeLabel) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.loc codeLabel 0) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, code, DataSem.installSfs, op, middle]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate, targetMem]
  · exact stateRel64_setCodePtr conf l1 l2 middle target locs middleRel dest codeLabel

/-- Source safety ensures that the assigned code label exists. -/
theorem assignLabel64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) (dest codeLabel : Nat)
    (safe : (DataSem.evaluate (.assign dest (.label codeLabel) [] none) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.label codeLabel) [] none) source target locs := by
  cases code : sptLookup codeLabel source.code with
  | none =>
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, code] at safe
  | some pair =>
    obtain ⟨arity, body⟩ := pair
    exact assignLabel64 conf secn label l1 l2 source target locs related dest codeLabel arity body code

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
