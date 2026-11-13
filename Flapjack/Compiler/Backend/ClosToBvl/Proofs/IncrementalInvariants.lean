module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.VarsNone
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationDistinct
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.CodeLocations
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.CodeLocations

@[expose] public section

/-! Code-location and annotation invariants of incremental closure passes. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps

/-- Tick removal preserves the location list in incremental compilation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_locs_FST_ticks_compile_inc"]
theorem ticksCompileInc_codeLocations {α β : Type} (x : List ClosLang.Exp × β) :
    codeLocations ((ClosTicks.compileIncSource x : List ClosLang.Exp × List α).1) = codeLocations x.1 := by
  simpa [ClosTicks.compileIncSource] using ClosTicks.removeSource_codeLocations x.1

/-- Let-operation optimization preserves the location list in incremental compilation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_locs_FST_letop_compile_inc"]
theorem letopCompileInc_codeLocations {α β : Type} (x : List ClosLang.Exp × β) :
    codeLocations ((ClosLetop.compileIncSource x : List ClosLang.Exp × List α).1) = codeLocations x.1 := by
  simpa [ClosLetop.compileIncSource] using ClosLetop.compileSource_codeLocations x.1

/-- Incremental numbering produces distinct code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ncompile_inc_code_locs_distinct"]
theorem numberCompileInc_codeLocations_distinct (x : Nat) (y : List ClosLang.Exp) :
    (codeLocations (ClosNumber.compileInc x y).2).Nodup := by
  simpa [ClosNumber.compileInc, codeLocations, codeLocationsExp] using
    (ClosNumber.renumberList_codeLocations_distinct (makeEven (x + max y.length 1)) y).1

/-- Incremental numbering preserves absent captured-variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_vs_NONE_ncompile_inc"]
theorem numberCompileInc_everyFnVarsNone (x : Nat) (y : List ClosLang.Exp) :
    everyFnVarsNone (ClosNumber.compileInc x y).2 ↔ everyFnVarsNone y := by
  simpa [ClosNumber.compileInc, everyFnVarsNone, fnVarsNoneExp] using
    ClosNumber.renumberCodeLocs_everyFnVarsNone.1 (makeEven (x + max y.length 1)) y

/-- Incremental numbering assigns every function a location. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_SOME_ncompile_inc"]
theorem numberCompileInc_everyFnLocationSome (x : Nat) (y : List ClosLang.Exp) :
    everyFnLocationSome (ClosNumber.compileInc x y).2 := by
  simpa [ClosNumber.compileInc, everyFnLocationSome, fnLocationSomeExp] using
    ClosNumber.renumberCodeLocs_everyFnSome.1 (makeEven (x + max y.length 1)) y
end Flapjack.Compiler.Backend.ClosToBvl
