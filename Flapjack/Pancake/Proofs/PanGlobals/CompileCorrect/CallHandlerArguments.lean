import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerFreshNames
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocalEval

namespace Flapjack.PanGlobalsCallHandlerArguments
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Synthesized argument-transport proof step for the global Call-with-handler
lowering (pan_globalsScript.sml:118-125). HOL's compile_correct proof at
1313/1412 applies OPT_MMAP_eval_two_fresh_vars to these generated names.
There is no standalone HOL declaration for this specialized composition, so it
is untagged. Arbitrary scratch values are permitted; no freshness or successful
evaluation premise is added. The full Call simulation remains a separate task. -/
theorem callHandlerArgumentsUnderScratchLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (handlerVar : MlS)
    (compiledHandler : ProgHOL width) (compiledArguments : List (ExpHOL width))
    (resultValue flagValue : ValueHOL width) :
    let names := handlerVar :: freeVarIdsHOL compiledHandler ++
      compiledArguments.flatMap varExpHOL
    let resultName := freshNameMlS (ofString "") names
    let flagName := freshNameMlS (ofString "vn'") (resultName :: names)
    let scratchState := setVarHOLFinite flagName flagValue
      (setVarHOLFinite resultName resultValue state)
    @evalListHOLFinite width σ _ scratchState
      (fun a => Classical.propDecidable (scratchState.memaddrs a)) compiledArguments =
      @evalListHOLFinite width σ _ state
        (fun a => Classical.propDecidable (state.memaddrs a)) compiledArguments := by
  classical
  dsimp only
  obtain ⟨_, _, _, _, _, hr, hf⟩ :=
    PanGlobalsCallHandlerFreshNames.callHandlerScratchNamesFresh
      handlerVar compiledHandler compiledArguments
  apply PanGlobalsFreshLocalEval.evalListTwoFreshVars
  constructor
  · intro h
    obtain ⟨vars, hvars, hname⟩ := List.mem_flatten.mp h
    obtain ⟨argument, ha, rfl⟩ := List.mem_map.mp hvars
    exact hr argument ha hname
  · intro h
    obtain ⟨vars, hvars, hname⟩ := List.mem_flatten.mp h
    obtain ⟨argument, ha, rfl⟩ := List.mem_map.mp hvars
    exact hf argument ha hname

end Flapjack.PanGlobalsCallHandlerArguments
