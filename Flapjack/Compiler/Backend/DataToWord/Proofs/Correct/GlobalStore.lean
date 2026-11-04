import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ArrayStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GlobalStore

/-! Global writes in the 64-bit data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A valid global update is simulated by the generated word store. -/
theorem assignGlobalStore64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest ref index value : Nat) (values : List DataSem.Value) (item : DataSem.Value)
    (global : source.global = some ref) (found : sptLookup ref source.refs = some (.valueArray values))
    (bound : index < values.length) (valueRun : DataSem.getVar value source.locals = some item) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp (.setGlobal index)) [value] none) source target locs := by
  let op := ClosLang.Op.globOp (.setGlobal index)
  let middle := DataSem.doStack op [item] (DataSem.doLimSafe source op [item])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op [item]
  have middleGlobal : middle.global = some ref := by simpa [middle, DataSem.doStack, DataSem.doLimSafe, op] using global
  have middleFound : sptLookup ref middle.refs = some (.valueArray values) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op] using found
  have middleValue : DataSem.getVar value middle.locals = some item := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op] using valueRun
  obtain ⟨address, word, addressRun, wordRun, inDomain, storeRel⟩ :=
    stateRel64_storeGlobal conf l1 l2 middle target locs middleRel ref index value values item
      middleGlobal middleFound bound middleValue
  let source1 := { middle with refs := sptInsert ref (.valueArray (values.set index item)) middle.refs }
  let target1 := { target with memory := fun key => if key = address then word else target.memory key }
  have rel : stateRel64 conf l1 l2 source1 target1 none locs := storeRel
  refine ⟨DataSem.setVar dest DataSem.unitValue source1,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target1, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, global, found, bound,
      op, middle, source1]
  · have first : WordSemStateFiniteExact.evaluate
        (.store (.op .add [.lookup .globReal, .const (8 * BitVec.ofNat 64 (index + 1))]) (adjustVar value))
        target = (none, target1) := by
      simp only [WordSemStateFiniteExact.evaluate, addressRun, wordRun, WordSemStateFiniteExact.memStore,
        inDomain, ↓reduceIte, target1]
    have second : WordSemStateFiniteExact.evaluate (.assign (adjustVar dest) (.const 2)) target1 =
        (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
    have fix : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1]
    simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate (.seq
      (.store (.op .add [.lookup .globReal, .const (8 * BitVec.ofNat 64 (index + 1))]) (adjustVar value))
      (.assign (adjustVar dest) (.const 2))) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, fix, second]
  · simpa [DataSem.unitValue] using stateRel64_setEmptyBlock conf l1 l2 source1 target1 locs rel dest 0 (by norm_num)

/-- Every source-safe global assignment is simulated. -/
theorem assignGlobalStore64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) (dest index value : Nat)
    (safe : (DataSem.evaluate (.assign dest (.globOp (.setGlobal index)) [value] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp (.setGlobal index)) [value] none) source target locs := by
  cases valueRun : DataSem.getVar value source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun] at safe
  | some item =>
    cases global : source.global with
    | none =>
      simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
        DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
        DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global] at safe
    | some ref =>
      cases found : sptLookup ref source.refs with
      | none =>
        simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
          DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
          DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe
      | some entry =>
        cases entry with
        | valueArray values =>
          by_cases bound : index < values.length
          · exact assignGlobalStore64 conf secn label l1 l2 source target locs related dest ref index value values item global found bound valueRun
          · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
              DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
              DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found, bound] at safe
        | byteArray flag bytes =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe
        | thunk mode item =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe
        | mutBlock tag finalised left item right =>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, valueRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
