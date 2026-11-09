import Flapjack.Compiler.Backend.ClosAnnotate.Shift.Original

/-! Agreement between source-shaped and executable shifting. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- Supporting map equation for the recursive-function traversal. -/
theorem shiftFuns_as_map (count k : Nat) (i : Spt Nat) (functions : List (Nat × Exp)) :
    shiftFuns count k i functions = functions.map (fun (n, x) => (n, shiftSing x k (n + count) i)) := by
  induction functions with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [shiftFuns, ih]

/-- The source recursion computes the optimized list traversal. -/
theorem shiftSource_eq_shiftList (expressions : List Exp) (m l : Nat) (i : Spt Nat) :
    shiftSource expressions m l i = shiftList expressions m l i := by
  induction expressions, m, l, i using shiftSource.induct <;>
    simp_all [shiftSource, shiftList, shiftSing, Flapjack.holHd, shiftFuns_as_map]
  case case10 =>
    rename_i name loc vs args x m l i k live ih
    dsimp [k, live] at ih
    simp_all
  case case11 =>
    rename_i names loc vs fs x m l i k live newI ihFuns ihBody
    dsimp [k, live, newI] at ihFuns
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
    apply List.map_congr_left
    intro entry member
    cases entry with
    | mk arity body => simp [*]

/-- Source and executable shifts agree for singleton expressions, expression
lists, and recursive-function groups. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_sing_eq"]
theorem shiftSource_sing_eq :
    (∀ expression m l i, shiftSource [expression] m l i = [shiftSing expression m l i]) ∧
    (∀ expressions m l i, shiftSource expressions m l i = shiftList expressions m l i) ∧
    (∀ count k i functions,
      (∀ entry ∈ functions, shiftSource [entry.2] k (entry.1 + count) i =
        [shiftSing entry.2 k (entry.1 + count) i]) ∧
      shiftFuns count k i functions = functions.map (fun (n, x) => (n, shiftSing x k (n + count) i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro expression m l i
    simpa [shiftList] using shiftSource_eq_shiftList [expression] m l i
  · exact shiftSource_eq_shiftList
  · intro count k i functions
    constructor
    · intro entry _
      simpa [shiftList] using shiftSource_eq_shiftList [entry.2] k (entry.1 + count) i
    · exact shiftFuns_as_map count k i functions

end Flapjack.Compiler.Backend.ClosAnnotate
