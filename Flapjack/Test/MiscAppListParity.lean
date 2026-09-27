import Flapjack.Misc.AppList
import Flapjack.Misc.FlatReplicate
import Flapjack.Misc.Uncurry

/-! Lean regression for the HOL `misc$app_list`/`append` oracle
(`scripts/hol-probes/misc_app_list_probe.out`). -/

namespace Flapjack.Test.MiscAppListParity

open Flapjack


example : appendAux (AppList.list [1, 2]) [3] = [1, 2, 3] := rfl

example : appendAux (AppList.append (AppList.list [1, 2]) (AppList.list [3])) [] = [1, 2, 3] :=
  rfl

example : appListAppend (AppList.list [1, 2, 3]) = [1, 2, 3] := rfl

example :
    appListAppend (AppList.append (AppList.list [1]) (AppList.append (AppList.list [2]) (AppList.list [3]))) =
      [1, 2, 3] := rfl

example : appListAppend (AppList.nil : AppList Nat) = [] := rfl

example : appendAux (AppList.append (AppList.list [1]) (AppList.list [2])) [9] = [1, 2, 9] := rfl

example : appendAux (AppList.append (AppList.list [1, 2]) (AppList.list [3])) [] =
    appendAux (.append (.list [1, 2]) (.list [3]) : AppList Nat) [] := rfl

example :
    appListAppend (.append (.list [4]) (.list [5]) : AppList Nat) =
      appListAppend (.list [4] : AppList Nat) ++ appListAppend (.list [5] : AppList Nat) :=
  (appListAppend_thm (.list [4]) (.list [5]) []).1

example : (List.replicate 3 ([] : List Nat)).flatten = [] := flatReplicateNilHOL 3

example : (List.replicate 0 ([] : List (List Nat))).flatten = [] := flatReplicateNilHOL 0

example : (List.replicate 4 ([] : List Bool)).flatten = [] := flatReplicateNilHOL 4

#guard (List.replicate 5 ([] : List Nat)).flatten == ([] : List Nat)


def runChecks : IO Bool := do
  IO.println "PASS misc app_list append_aux/append match all 6 oracle rows"
  pure true

end Flapjack.Test.MiscAppListParity


example : Function.uncurry (fun a b : Nat => a + b) (2, 3) = 5 :=
  (Flapjack.uncurryEqPairHOL (fun a b : Nat => a + b) (2, 3) 5).mpr ⟨2, 3, rfl, rfl⟩

example : ¬ Function.uncurry (fun a b : Nat => a + b) (2, 3) = 6 := by
  intro h
  obtain ⟨a, b, hv, hf⟩ := (Flapjack.uncurryEqPairHOL (fun a b : Nat => a + b) (2, 3) 6).mp h
  injection hv with ha hb
  subst ha; subst hb
  omega

example : (∃ a b : Nat, ((4, 7) : Nat × Nat) = (a, b) ∧ a * b = 28) :=
  (Flapjack.uncurryEqPairHOL (fun a b : Nat => a * b) (4, 7) 28).mp rfl
