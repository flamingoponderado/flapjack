import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.NewLocal
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.SeqCases
import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers

/-! Integer constant assignments in the production-backed simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Source constant bounds fit the 64-bit immediate-number range. -/
theorem constant64_small (i : Int) (bound : BackendCommon.smallEnoughInt i) : smallInt 64 i := by
  simp [BackendCommon.smallEnoughInt] at bound
  norm_num [smallInt]
  omega

/-- Source stack accounting can increase the source maximum and change its
space-safety flag without disturbing the data-to-word relation. -/
theorem stateRel64_afterDoStack {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (op : ClosLang.Op) (values : List DataSem.Value) :
    stateRel64 conf l1 l2 (DataSem.doStack op values (DataSem.doLimSafe source op values)) target none locs := by
  let middle := DataSem.doStack op values (DataSem.doLimSafe source op values)
  have increases : BackendProps.optionLe source.stackMax middle.stackMax := by
    dsimp [middle, DataSem.doStack, DataSem.doLimSafe]
    generalize Option.map₂ (· + ·) (DataSem.stackConsumed source.stackFrameSizes source.limits op values)
      (Option.map₂ (· + ·) (DataSem.sizeOfStack source.stack) source.localsSize) = consumption
    cases h : source.stackMax <;> cases consumption <;> simp [BackendProps.optionLe]
  have h := stateRel64_sourceStackMax conf l1 l2 source target locs related middle.stackMax increases
  have h' := (stateRel64_withSafeForSpace conf l1 l2 { source with stackMax := middle.stackMax } target none locs middle.safeForSpace).mpr h
  simpa [middle, DataSem.doStack, DataSem.doLimSafe] using h'

/-- A source-bounded integer constant is compiled to the matching immediate
word and preserves the relation after source stack accounting. -/
theorem assignConst64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest : Nat) (i : Int) (bound : BackendCommon.smallEnoughInt i) :
    continues64 conf secn label l1 l2 (.assign dest (.intOp (.const i)) [] none) source target locs := by
  let op := ClosLang.Op.intOp (.const i)
  let middle := DataSem.doStack op [] (DataSem.doLimSafe source op [])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op []
  refine ⟨DataSem.setVar dest (.number i) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum i)) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doIntApp, DataSem.installSfs, bound, op, middle]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, smallnum_eq_inlined]
  · exact stateRel64_setSmallInt conf l1 l2 middle target locs middleRel dest i (constant64_small i bound)

/-- A source-safe constant assignment meets the source integer bound. -/
theorem assignConst64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest : Nat) (i : Int)
    (safe : (DataSem.evaluate (.assign dest (.intOp (.const i)) [] none) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.intOp (.const i)) [] none) source target locs := by
  by_cases bound : BackendCommon.smallEnoughInt i
  · exact assignConst64 conf secn label l1 l2 source target locs related dest i bound
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doIntApp, bound] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
