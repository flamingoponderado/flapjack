import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Boolean
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Bool

/-! Boolean negation in the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A successfully decoded Boolean is recognized by the corresponding source
test, independently of the block timestamp. -/
theorem destBool_isBool (value : DataSem.Value) (b : Bool) (decoded : DataSem.destBool value = some b) :
    DataSem.isBool b value = true := by
  cases value with
  | block stamp tag values =>
    cases values with
    | nil =>
      cases b <;> simp [DataSem.destBool, DataSem.isBool, BackendCommon.boolToTag,
        BackendCommon.trueTag, BackendCommon.falseTag] at decoded ⊢ <;> omega
    | cons value values => simp [DataSem.destBool] at decoded
  | number n => simp [DataSem.destBool] at decoded
  | word64 w => simp [DataSem.destBool] at decoded
  | codePtr n => simp [DataSem.destBool] at decoded
  | refPtr flag n => simp [DataSem.destBool] at decoded

/-- A Boolean and its immediate representation may be installed in the
related local environments without allocating. -/
theorem stateRel64_setBool {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (dest : Nat) (b : Bool) :
    stateRel64 conf l1 l2 (DataSem.setVar dest (DataSem.boolValue b) source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if b then 18 else 2)) target) none locs := by
  apply stateRel64_setNewLocal conf l1 l2 source target locs related
  apply Memory.memoryRel_bool
  refine ⟨?_, Or.inr rfl, ?_, ?_⟩
  · simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro h; subst b; rfl
  · intro h; subst b; rfl

/-- Successful Boolean negation is implemented by xor with the immediate tag
bit, with source stack accounting reflected in the state relation. -/
theorem assignBoolNot64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (value : DataSem.Value) (b : Bool)
    (sourceRun : DataSem.getVar src source.locals = some value) (decoded : DataSem.destBool value = some b) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp .boolNot) [src] none) source target locs := by
  let op := ClosLang.Op.blockOp .boolNot
  let middle := DataSem.doStack op [value] (DataSem.doLimSafe source op [value])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [value]
  have targetRun := stateRel64_getBool conf l1 l2 source target locs related src value b sourceRun (destBool_isBool value b decoded)
  refine ⟨DataSem.setVar dest (DataSem.boolValue (!b)) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (if !b then 18 else 2)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, decoded, DataSem.installSfs, op, middle]
  · cases b <;> simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, targetRun, theWords,
      wordOpHOL, wordOp, WordSemStateFiniteExact.setVar]
  · exact stateRel64_setBool conf l1 l2 middle target locs middleRel dest (!b)

/-- Source type safety supplies the local lookup and successful Boolean
decoding required by negation. -/
theorem assignBoolNot64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat)
    (safe : (DataSem.evaluate (.assign dest (.blockOp .boolNot) [src] none) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp .boolNot) [src] none) source target locs := by
  cases sourceRun : DataSem.getVar src source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some value =>
    cases decoded : DataSem.destBool value with
    | none =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, decoded] at safe
    | some b => exact assignBoolNot64 conf secn label l1 l2 source target locs related dest src value b sourceRun decoded

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
