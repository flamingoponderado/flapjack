module

public import Flapjack.Compiler.Backend.ClosAnnotate.Shift
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Lookup properties for the compact closure environment. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate

/-- Looking up an element of a distinct live-variable list returns its
position plus the starting offset. This source-shaped helper remains untagged
pending comparison of the local HOL declaration's inferred types. -/
theorem lookup_shiftedEnv_el (variables : List Nat) (index offset : Nat)
    (bound : index < variables.length) (distinct : variables.Nodup) :
    sptLookup (Flapjack.holEl index variables) (shiftedEnv offset variables) = some (offset + index) := by
  induction variables generalizing index offset with
  | nil => simp at bound
  | cons first rest ih =>
    have parts := List.nodup_cons.mp distinct
    cases index with
    | zero => simp [shiftedEnv, Flapjack.holEl, Flapjack.holHd, sptLookup_sptInsert_same]
    | succ index =>
      have smaller : index < rest.length := by simpa using bound
      have member : Flapjack.holEl index rest ∈ rest := by
        rw [Flapjack.holEl_eq_getElem index rest smaller]
        exact List.getElem_mem smaller
      have different : Flapjack.holEl index rest ≠ first := by
        intro equal
        apply parts.1
        simpa [equal] using member
      simp only [shiftedEnv, Flapjack.holEl_cons_succ]
      rw [sptLookup_sptInsert_ne first (Flapjack.holEl index rest) offset
        (shiftedEnv (offset + 1) rest) different]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih index (offset + 1) smaller parts.2

end Flapjack.Compiler.Backend.ClosAnnotate
