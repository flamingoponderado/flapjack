import Flapjack.Compiler.Backend.Parmove.StepMapInj

namespace Flapjack.Test.ParmoveStepMapInjParity
open Compiler.Backend.Parmove

/-! Full mapped source/target states from the original six rule observations
in `parmove_step_map_inj_probe.out`, paired with genuine Step theorem applications.
The collapsing map sentinel is injective only on its source state's endpoints. -/
private def rename : Option Bool → Option Nat
  | none => none
  | some false => some 10
  | some true => some 20

private theorem renameInjective (x y : Option Bool) (equal : rename x = rename y) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => cases y <;> simp [rename] at equal
  | some x =>
    cases y with
    | none => cases x <;> simp [rename] at equal
    | some y => cases x <;> cases y <;> simp_all [rename]

private theorem valid (state : State Bool) : injOnState rename state := by
  refine ⟨fun x y h => renameInjective x y h.2.2, ?_⟩
  intro x
  cases x with
  | none => simp [rename]
  | some x => cases x <;> simp [rename]

private def states : List (State Bool × State Bool) :=
  [ (([(some false, some false)], [], []), ([], [], [])),
    (([(some false, some true)], [], []), ([], [(some false, some true)], [])),
    (([(some true, some false)], [(some false, some true)], []),
      ([], [(some true, some false), (some false, some true)], [])),
    (([], [(some false, some true)], []),
      ([], [(some false, none)], [(none, some true)])),
    (([], [(some true, some false), (some false, some false)], []),
      ([], [(some false, some false)], [(some true, some false)])),
    (([], [(some false, some true)], []), ([], [], [(some false, some true)])) ]

example : states.map (Prod.map (mapState rename) (mapState rename)) =
  [ (([(some 10, some 10)], [], []), ([], [], [])),
    (([(some 10, some 20)], [], []), ([], [(some 10, some 20)], [])),
    (([(some 20, some 10)], [(some 10, some 20)], []),
      ([], [(some 20, some 10), (some 10, some 20)], [])),
    (([], [(some 10, some 20)], []), ([], [(some 10, none)], [(none, some 20)])),
    (([], [(some 20, some 10), (some 10, some 10)], []),
      ([], [(some 10, some 10)], [(some 20, some 10)])),
    (([], [(some 10, some 20)], []), ([], [], [(some 10, some 20)])) ] := by
  rfl

private theorem mapped (first second : State Bool) (step : Step first second) :
    Step (mapState rename first) (mapState rename second) :=
  stepMapInj rename first second step (valid first)

example : Step (mapState rename ([(some false, some false)], [], []))
    (mapState rename ([], [], [])) := mapped _ _ (Step.removeSelf _ [] [] [] [])
example : Step (mapState rename ([(some false, some true)], [], []))
    (mapState rename ([], [(some false, some true)], [])) :=
  mapped _ _ (Step.start _ _ [] [] [])
example : Step (mapState rename ([(some true, some false)], [(some false, some true)], []))
    (mapState rename ([], [(some true, some false), (some false, some true)], [])) :=
  mapped _ _ (Step.extend _ _ _ [] [] [] [])
example : Step (mapState rename ([], [(some false, some true)], []))
    (mapState rename ([], [(some false, none)], [(none, some true)])) :=
  mapped _ _ (Step.save _ _ [] [] [])
example : Step (mapState rename ([], [(some true, some false), (some false, some false)], []))
    (mapState rename ([], [(some false, some false)], [(some true, some false)])) :=
  mapped _ _ (Step.emitHead _ _ _ _ [] [] [] (by simp) (by decide +kernel))
example : Step (mapState rename ([], [(some false, some true)], []))
    (mapState rename ([], [], [(some false, some true)])) :=
  mapped _ _ (Step.emitLast _ _ [] [] (by simp))

private def collapse : Option Nat → Option Bool
  | none => none
  | some _ => some false

private theorem validCollapsed : injOnState collapse ([(some 3, some 3)], [], []) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    simp only [stateToList, List.append_nil, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at h
    exact h.1.trans h.2.1.symm
  · intro x; cases x <;> simp [collapse]

example : (mapState collapse ([(some 3, some 3)], [], []), decide (collapse (some 4) = collapse (some 5))) =
    (([(some false, some false)], [], []), true) := by rfl
example : injOnState collapse ([(some 3, some 3)], [], []) := validCollapsed
example : Step (mapState collapse ([(some 3, some 3)], [], []))
    (mapState collapse ([], [], [])) :=
  stepMapInj collapse _ _ (Step.removeSelf _ [] [] [] []) validCollapsed

example {α : Type} (r : Option α) :
    Step (mapState id ([(r, r)], [], [])) (mapState id ([], [], [])) :=
  stepMapInj id _ _ (Step.removeSelf _ [] [] [] [])
    ⟨fun _ _ h => h.2.2, fun _ => Iff.rfl⟩

end Flapjack.Test.ParmoveStepMapInjParity
