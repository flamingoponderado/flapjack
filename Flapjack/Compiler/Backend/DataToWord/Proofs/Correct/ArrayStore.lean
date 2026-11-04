import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ByteStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ArrayStore

/-! Dynamic value-array updates in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The compiled word store simulates a valid source value-array update. -/
theorem assignArrayStore64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index value ref n : Nat) (bit : Bool) (old : List DataSem.Value) (item : DataSem.Value)
    (baseRun : DataSem.getVar base source.locals = some (.refPtr bit ref))
    (indexRun : DataSem.getVar index source.locals = some (.number (Int.ofNat n)))
    (valueRun : DataSem.getVar value source.locals = some item)
    (bound : n < old.length) (found : sptLookup ref source.refs = some (.valueArray old)) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .update) [base, index, value] none) source target locs := by
  let op := ClosLang.Op.memOp .update
  let args : List DataSem.Value := [.refPtr bit ref, .number (Int.ofNat n), item]
  let middle := DataSem.doStack op args (DataSem.doLimSafe source op args)
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op args
  have middleBase : DataSem.getVar base middle.locals = some (.refPtr bit ref) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using baseRun
  have middleIndex : DataSem.getVar index middle.locals = some (.number (Int.ofNat n)) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using indexRun
  have middleValue : DataSem.getVar value middle.locals = some item := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using valueRun
  have middleFound : sptLookup ref middle.refs = some (.valueArray old) := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe, op, args] using found
  obtain ⟨address, word, addressRun, wordRun, inDomain, storeRel⟩ :=
    stateRel64_storeArrayElement conf l1 l2 middle target locs middleRel base index value ref n bit old item
      middleBase middleIndex middleValue middleFound bound
  let source1 := { middle with refs := sptInsert ref (.valueArray (old.set n item)) middle.refs }
  let target1 := { target with memory := fun key => if key = address then word else target.memory key }
  have rel : stateRel64 conf l1 l2 source1 target1 none locs := storeRel
  refine ⟨DataSem.setVar dest DataSem.unitValue source1,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) target1, ?_, ?_, ?_⟩
  · have nonnegative : ¬ ((n : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    have notge : ¬ old.length ≤ n := by omega
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun, valueRun,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, DataSem.doStack, DataSem.doLimSafe, found, op, args, middle,
      notge, nonnegative, source1]
  · have first : WordSemStateFiniteExact.evaluate
        (.store (.op .add [realAddr conf (adjustVar base),
          .op .add [.const 8, .shift .lsl (.var (adjustVar index)) (.const 1)]]) (adjustVar value))
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
      (.store (.op .add [realAddr conf (adjustVar base),
        .op .add [.const 8, .shift .lsl (.var (adjustVar index)) (.const 1)]]) (adjustVar value))
      (.assign (adjustVar dest) (.const 2))) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, fix, second]
  · simpa [DataSem.unitValue] using stateRel64_setEmptyBlock conf l1 l2 source1 target1 locs rel dest 0 (by norm_num)

/-- Every safe source value-array update is simulated. -/
theorem assignArrayStore64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest base index value : Nat)
    (safe : (DataSem.evaluate (.assign dest (.memOp .update) [base, index, value] none) source).1 ≠
      some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.memOp .update) [base, index, value] none) source target locs := by
  cases baseRun : DataSem.getVar base source.locals with
  | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun] at safe
  | some baseVal =>
    cases indexRun : DataSem.getVar index source.locals with
    | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun] at safe
    | some indexVal =>
      cases valueRun : DataSem.getVar value source.locals with
      | none => simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun, valueRun] at safe
      | some valueVal =>
        cases baseVal <;> cases indexVal <;>
          simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars, baseRun, indexRun, valueRun,
            DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
            DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe] at safe
        case refPtr.number bit ref idx =>
          cases idx with
          | negSucc n =>
            cases found : sptLookup ref source.refs <;> simp [found] at safe
            case some entry => cases entry <;> simp at safe
          | ofNat n =>
            cases found : sptLookup ref source.refs with
            | none => simp [found] at safe
            | some entry =>
              cases entry with
              | valueArray old =>
                by_cases bound : n < old.length
                · exact assignArrayStore64 conf secn label l1 l2 source target locs related dest base index value ref n bit old valueVal baseRun indexRun valueRun bound found
                · have ge : old.length ≤ n := Nat.le_of_not_gt bound
                  simp [found, ge] at safe
              | byteArray flag bytes => simp [found] at safe
              | thunk mode item => simp [found] at safe
              | mutBlock tag flag values => simp [found] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
