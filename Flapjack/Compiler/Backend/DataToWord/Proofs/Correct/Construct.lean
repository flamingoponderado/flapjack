import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Construct
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant

/-! Nullary constructor creation in the 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Creating an encodable nullary constructor installs its immediate word.
Out-of-range tags take the compiler's allocation-failure path and require the
separate garbage-collection simulation. -/
theorem assignEmptyCons64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest tag : Nat) (bound : tag < 2 ^ 64 / 16) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.cons tag)) [] none) source target locs := by
  let op := ClosLang.Op.blockOp (.cons tag)
  let middle := DataSem.doStack op [] (DataSem.doLimSafe source op [])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op []
  refine ⟨DataSem.setVar dest (.block 0 tag []) middle,
    WordSemStateFiniteExact.setVar (adjustVar dest) (.word (BitVec.ofNat 64 (16 * tag + 2))) target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.installSfs, op, middle]
  · simp only [compileControl64, compileControl?, Option.getD_some]
    change WordSemStateFiniteExact.evaluate
      ((if tag < 2 ^ 64 / 16 then (.assign (adjustVar dest) (.const (BitVec.ofNat 64 (16 * tag + 2))), label) else (giveUp, label)).1) target = _
    have bound' : tag < 1152921504606846976 := by simpa using bound
    simp [bound', WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
  · exact stateRel64_setEmptyBlock conf l1 l2 middle target locs middleRel dest tag bound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
