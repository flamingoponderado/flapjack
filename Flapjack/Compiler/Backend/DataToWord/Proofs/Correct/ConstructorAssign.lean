import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant

/-! Source and target execution of nonempty constructor assignments. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend Gc

/-- A nonempty constructor assignment is simulated when its header encodes
and the source has sufficient reserved space. The full safety-to-header
argument and the remaining constructor cases are separate obligations. -/
theorem assignCons64 {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (args : List Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVars args source.locals = some values)
    (nonempty : values ≠ []) (enough : values.length + 1 ≤ source.space)
    (header : BitVec 64) (encoded : encodeHeader conf (4 * tag) values.length = some header)
    (next : Nat) (stamps : source.tstamps = some next) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.cons tag)) args none) source target locs := by
  let op := ClosLang.Op.blockOp (.cons tag)
  let middle := DataSem.doStack op values (DataSem.doLimSafe source op values)
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op values
  have middleRun : DataSem.getVars args middle.locals = some values := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using sourceRun
  have middleSpace : values.length + 1 ≤ middle.space := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using enough
  have middleStamps : middle.tstamps = some next := by
    simpa [middle, DataSem.doStack, DataSem.doLimSafe] using stamps
  obtain ⟨program, final, compiled, wordRun, finalRel⟩ :=
    stateRel64_cons_compiled conf secn label l1 l2 dest tag middle target locs middleRel args none values
      middleRun nonempty middleSpace header encoded next middleStamps
  let allocated := { middle with tstamps := some (next + 1), space := middle.space - (values.length + 1) }
  let finalSource := DataSem.setVar dest (.block next tag values) (DataSem.checkLim allocated values.length)
  refine ⟨finalSource, final, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, sourceRun, DataSem.cutStateOpt,
      DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.consumeSpace, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp,
      DataSem.installSfs, nonempty, Nat.not_lt.mpr enough, stamps, finalSource, allocated,
      middle, op, DataSem.doStack, DataSem.doLimSafe]
  · simpa [compileControl64, compiled] using wordRun
  · have changed := (stateRel64_withSafeForSpace conf l1 l2
      (DataSem.setVar dest (.block next tag values) allocated) final none locs
      (DataSem.checkLim allocated values.length).safeForSpace).mpr (by simpa [allocated] using finalRel)
    simpa [finalSource, DataSem.checkLim, DataSem.setVar] using changed

/-- Source representation limits ensure the generated nonempty constructor
header can be encoded on the related 64-bit target. -/
theorem assignCons64_of_limSafe {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (args : List Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVars args source.locals = some values)
    (nonempty : values ≠ []) (enough : values.length + 1 ≤ source.space)
    (safe : DataSem.limSafe source.limits (.blockOp (.cons tag)) values) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.cons tag)) args none) source target locs := by
  have related' := related
  obtain ⟨_, _, _, _, _, _, _, _, present, _, _, _, _, _, _, _, _, _, limits, _⟩ := related'
  obtain ⟨_, lengthLimit, arch64, _, _, _, _⟩ := limits
  have bounds : values.length < 2 ^ conf.lenSize ∧ values.length < 2 ^ (64 - 4) ∧
      4 * tag < 2 ^ 64 / 16 ∧ 4 * tag < 2 ^ (64 - conf.lenSize - 2) := by
    simpa [DataSem.limSafe, nonempty, DataSem.archSize, arch64, lengthLimit] using safe
  have encoded : encodeHeader (width := 64) conf (4 * tag) values.length =
      some (makeHeader conf (BitVec.ofNat 64 (4 * tag)) values.length) := by
    unfold encodeHeader
    rw [if_pos ⟨bounds.2.2.2, bounds.2.2.1, bounds.2.1, bounds.1⟩]
  cases stamps : source.tstamps with
  | none => simp [stamps] at present
  | some next =>
    exact assignCons64 conf secn label l1 l2 dest tag source target locs related args values
      sourceRun nonempty enough _ encoded next stamps

/-- A successful, space-safe source constructor execution supplies both the
reserved-space and representation bounds needed by the simulation. -/
theorem assignCons64_of_execution_safe {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (args : List Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVars args source.locals = some values) (nonempty : values ≠ [])
    (typeSafe : (DataSem.evaluate (.assign dest (.blockOp (.cons tag)) args none) source).1 ≠
      some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.assign dest (.blockOp (.cons tag)) args none) source).2.safeForSpace = true) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.cons tag)) args none) source target locs := by
  have enough : values.length + 1 ≤ source.space := by
    by_contra insufficient
    have small : source.space < values.length + 1 := by omega
    simp [DataSem.evaluate, DataLang.opRequiresNames, sourceRun, DataSem.cutStateOpt,
      DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.consumeSpace, nonempty, small] at typeSafe
  have present : source.tstamps.isSome = true := related.2.2.2.2.2.2.2.2.1
  obtain ⟨next, stamps⟩ : ∃ next, source.tstamps = some next := by
    cases h : source.tstamps with
    | none => simp [h] at present
    | some next => exact ⟨next, rfl⟩
  have safe : DataSem.limSafe source.limits (.blockOp (.cons tag)) values := by
    by_contra bad
    simp [DataSem.evaluate, DataLang.opRequiresNames, sourceRun, DataSem.cutStateOpt,
      DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.consumeSpace, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.withFreshTimestamp,
      DataSem.installSfs, DataSem.checkLim, DataSem.doStack, DataSem.doLimSafe, DataSem.setVar,
      nonempty, Nat.not_lt.mpr enough, stamps, bad] at spaceSafe
  exact assignCons64_of_limSafe conf secn label l1 l2 dest tag source target locs related args values
    sourceRun nonempty enough safe

/-- Source type and space safety suffice for any nonempty constructor
argument list; successful source lookups provide the argument values. -/
theorem assignCons64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (args : List Nat) (nonempty : args ≠ [])
    (typeSafe : (DataSem.evaluate (.assign dest (.blockOp (.cons tag)) args none) source).1 ≠
      some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (.assign dest (.blockOp (.cons tag)) args none) source).2.safeForSpace = true) :
    continues64 conf secn label l1 l2 (.assign dest (.blockOp (.cons tag)) args none) source target locs := by
  cases sourceRun : DataSem.getVars args source.locals with
  | none =>
    simp [DataSem.evaluate, DataLang.opRequiresNames, sourceRun] at typeSafe
  | some values =>
    obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related args values sourceRun
    have targetLengths := WordSemStateFiniteExact.getVarsLengthLemma (args.map adjustVar) target words wordRun
    have valueNonempty : values ≠ [] := by
      intro empty
      apply nonempty
      apply List.eq_nil_of_length_eq_zero
      simp at targetLengths
      simpa [empty] using targetLengths.symm.trans lengths.symm
    exact assignCons64_of_execution_safe conf secn label l1 l2 dest tag source target locs related
      args values sourceRun valueNonempty typeSafe spaceSafe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
