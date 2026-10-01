import Flapjack.Compiler.Backend.Parmove.StepsMapInj
import Flapjack.Compiler.Backend.Parmove.MapState

namespace Flapjack.Test.ParmoveStepsMapInjParity
open Compiler.Backend.Parmove

/-! Kernel checks for the literal HOL theorem `steps_MAP_INJ`
(`parmoveScript.sml:1179`): `map_state f` transports the primitive move relation
along any number of steps from an injective source endpoint. -/

-- The reflexive closure transported by `map_state`.
example {α β : Type} (f : Option α → Option β) (state : State α)
    (h : injOnState f state) :
    Steps (mapState f state) (mapState f state) :=
  stepsMapInj f state state Relation.ReflTransGen.refl h

-- Any single primitive step is transported by `map_state`.
example {α β : Type} (f : Option α → Option β) (source target : State α)
    (h : injOnState f source) (transition : Step source target) :
    Steps (mapState f source) (mapState f target) :=
  stepsMapInj f source target
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl transition) h

def runChecks : IO Bool := do
  IO.println "PASS parmove steps_MAP_INJ transports Steps under map_state (reflexive and one-step)"
  pure true
end Flapjack.Test.ParmoveStepsMapInjParity
