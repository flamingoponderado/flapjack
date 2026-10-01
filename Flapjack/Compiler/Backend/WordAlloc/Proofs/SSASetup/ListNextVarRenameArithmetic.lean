import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof infrastructure, with no independent HOL declaration:
the generated names and next counter are independent of the input map. -/
private theorem resultShape (names : List Nat) (ssa : Spt Nat) (next : Nat) :
    (listNextVarRename names ssa next).1 =
      (List.range names.length).map (fun index => 4 * index + next) ∧
    (listNextVarRename names ssa next).2.2 = next + 4 * names.length := by
  induction names generalizing ssa next with
  | nil => simp [listNextVarRename]
  | cons name names ih =>
    have tail := ih (sptInsert name next ssa) (next + 4)
    constructor
    · simp only [listNextVarRename, nextVarRename, List.length_cons,
        List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
        Nat.mul_zero, Nat.zero_add]
      rw [tail.1]
      congr 1
      apply List.map_congr_left
      intro index member
      omega
    · simp only [listNextVarRename, nextVarRename, List.length_cons]
      rw [tail.2]
      omega

/-- Full original arithmetic result for native SSA renaming. Repeated input
names and arbitrary initial trees/counters are allowed; the only premise is
the original renaming equation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "list_next_var_rename_lemma_1"]
theorem listNextVarRenameLemma1 (names : List Nat) (ssa : Spt Nat) (next : Nat)
    (renamed : List Nat) (ssaOut : Spt Nat) (nextOut : Nat)
    (rename : listNextVarRename names ssa next = (renamed, ssaOut, nextOut)) :
    renamed.Nodup ∧
      renamed = (List.range names.length).map (fun index => 4 * index + next) ∧
      nextOut = next + 4 * names.length := by
  have shape := resultShape names ssa next
  rw [rename] at shape
  change renamed = (List.range names.length).map (fun index => 4 * index + next) ∧
    nextOut = next + 4 * names.length at shape
  refine ⟨?_, shape.1, shape.2⟩
  rw [shape.1]
  apply List.Nodup.map _ List.nodup_range
  intro a b equal
  change 4 * a + next = 4 * b + next at equal
  omega

end Flapjack.Compiler.Backend.WordAlloc
