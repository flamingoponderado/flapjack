import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
import Flapjack.Pancake.PanGlobals.CompileExpExact

namespace Flapjack.PanGlobalsCallHandlerFreshNames
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Synthesized freshness proof step for the global-destination Call-with-handler
lowering. The names are literal compile_def expressions; HOL's compile_correct
proof derives these facts with fresh_name_correct at 1414-1434. There is no
standalone HOL declaration for this conjunction, so it is untagged. This proves
only scratch-name freshness, not the Call simulation. -/
theorem callHandlerScratchNamesFresh {width : Nat} [NeZero width]
    (handlerVar : MlS) (compiledHandler : ProgHOL width)
    (compiledArguments : List (ExpHOL width)) :
    let names := handlerVar :: freeVarIdsHOL compiledHandler ++
      compiledArguments.flatMap varExpHOL
    let resultName := freshNameMlS (ofString "") names
    let flagName := freshNameMlS (ofString "vn'") (resultName :: names)
    resultName ∉ names ∧ flagName ∉ names ∧ resultName ≠ flagName ∧
      resultName ∉ freeVarIdsHOL compiledHandler ∧
      flagName ∉ freeVarIdsHOL compiledHandler ∧
      (∀ argument ∈ compiledArguments, resultName ∉ varExpHOL argument) ∧
      (∀ argument ∈ compiledArguments, flagName ∉ varExpHOL argument) := by
  dsimp only
  let names := handlerVar :: freeVarIdsHOL compiledHandler ++
    compiledArguments.flatMap varExpHOL
  let resultName := freshNameMlS (ofString "") names
  let flagName := freshNameMlS (ofString "vn'") (resultName :: names)
  have hr : resultName ∉ names := PanGlobalsDeclListExact.freshNameMlS_correct _ _
  have hf : flagName ∉ resultName :: names := PanGlobalsDeclListExact.freshNameMlS_correct _ _
  have hfn : flagName ∉ names := fun h => hf (List.mem_cons_of_mem _ h)
  have hne : resultName ≠ flagName := by
    intro h
    apply hf
    simp only [List.mem_cons, h, true_or]
  have handlerSubset : ∀ name ∈ freeVarIdsHOL compiledHandler, name ∈ names := by
    intro name h
    simp only [names, List.mem_cons, List.mem_append]
    exact Or.inl (Or.inr h)
  have argSubset : ∀ argument ∈ compiledArguments, ∀ name ∈ varExpHOL argument,
      name ∈ names := by
    intro argument ha name hn
    simp only [names, List.mem_cons, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨argument, ha, hn⟩)
  exact ⟨hr, hfn, hne, (fun h => hr (handlerSubset _ h)),
    (fun h => hfn (handlerSubset _ h)),
    (fun argument ha h => hr (argSubset argument ha _ h)),
    (fun argument ha h => hfn (argSubset argument ha _ h))⟩

end Flapjack.PanGlobalsCallHandlerFreshNames
