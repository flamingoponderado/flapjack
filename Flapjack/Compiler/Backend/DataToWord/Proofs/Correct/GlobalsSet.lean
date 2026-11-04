import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.GlobalStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GlobalsSet

/-! Globals-pointer initialization in the 64-bit data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A valid source globals-pointer update is simulated by the two generated
store updates and unit-result assignment. -/
theorem assignSetGlobalsPtr64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest name ptr : Nat) (sourceRun : DataSem.getVar name source.locals = some (.refPtr true ptr)) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp .setGlobalsPtr) [name] none) source target locs := by
  let op := ClosLang.Op.globOp .setGlobalsPtr
  let item := DataSem.Value.refPtr true ptr
  let middle := DataSem.doStack op [item] (DataSem.doLimSafe source op [item])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [item]
  have middleRun : DataSem.getVar name middle.locals = some item := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, item] using sourceRun
  obtain ⟨word, addr, wordRun, addressRun, installed⟩ :=
    stateRel64_installGlobals conf l1 l2 middle target locs middleRel name ptr middleRun
  let source1 := { middle with global := some ptr }
  let target1 := WordSemStateFiniteExact.setStore .globals (.word word) target
  let target2 := WordSemStateFiniteExact.setStore .globReal (.word addr) target1
  have rel : stateRel64 conf l1 l2 source1 target2 none locs := installed
  refine ⟨DataSem.setVar dest DataSem.unitValue source1,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target2, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, op, item, middle, source1]
  · have first : WordSemStateFiniteExact.evaluate (.set .globals (.var (adjustVar name))) target = (none, target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, wordRun, target1]
    have second : WordSemStateFiniteExact.evaluate (.set .globReal (realAddr conf (adjustVar name))) target1 =
        (none, target2) := by
      change WordSemStateFiniteExact.wordExp target1 (realAddr conf (adjustVar name)) = some (.word addr) at addressRun
      simp [WordSemStateFiniteExact.evaluate, addressRun, target2]
    have third : WordSemStateFiniteExact.evaluate (.assign (adjustVar dest) (.const 2)) target2 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
    have fix1 : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setStore]
    have fix2 : WordSemStateFiniteExact.fixClock target1 ((none : Option (WordSemResult 64)), target2) = (none, target2) := by
      simp [WordSemStateFiniteExact.fixClock, target2, WordSemStateFiniteExact.setStore]
    simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.seq (.set .globals (.var (adjustVar name)))
      (.seq (.set .globReal (realAddr conf (adjustVar name))) (.assign (adjustVar dest) (.const 2)))) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, fix1, second, fix2, third]
  · simpa [DataSem.unitValue] using stateRel64_setEmptyBlock conf l1 l2 source1 target2 locs rel dest 0 (by norm_num)

/-- Safety guarantees the installed pointer is an immutable reference. -/
theorem assignSetGlobalsPtr64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) (dest name : Nat)
    (safe : (DataSem.evaluate (.assign dest (.globOp .setGlobalsPtr) [name] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp .setGlobalsPtr) [name] none) source target locs := by
  cases sourceRun : DataSem.getVar name source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun] at safe
  | some item =>
    cases item <;>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, sourceRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe] at safe
    case refPtr bit ptr =>
      cases bit with
      | false => simp at safe
      | true => exact assignSetGlobalsPtr64 conf secn label l1 l2 source target locs related dest name ptr sourceRun

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
