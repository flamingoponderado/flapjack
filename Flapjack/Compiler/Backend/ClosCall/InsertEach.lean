import Flapjack.Compiler.Backend.ClosCall

/-! Source-shaped insertion of successive closure code locations. -/
namespace Flapjack.Compiler.Backend.ClosCall

/-- Insert successive even-spaced locations while leaving the payload alone. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "insert_each_def"]
def insertEachSource {A : Type} : Nat → Nat → NumSet × A → NumSet × A
  | _, 0, state => state
  | loc, count + 1, (known, payload) =>
      insertEachSource (loc + 2) count (sptInsert loc () known, payload)

/-- The executed range fold performs the same insertions as the source recursion. -/
theorem insertEach_eq_source (loc count : Nat) (state : State) :
    insertEach loc count state = insertEachSource loc count state := by
  induction count generalizing loc state with
  | zero => simp [insertEach, insertEachSource]
  | succ count ih =>
    cases state with
    | mk known code =>
      simp only [insertEach, insertEachSource, List.range_succ_eq_map, List.foldl_cons,
        List.foldl_map, Nat.mul_zero, Nat.add_zero]
      rw [← ih (loc + 2) (sptInsert loc () known, code)]
      simp [insertEach, Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

end Flapjack.Compiler.Backend.ClosCall
