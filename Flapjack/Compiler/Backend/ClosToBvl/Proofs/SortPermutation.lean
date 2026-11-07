import Flapjack.Compiler.Backend.ClosToBvl.Sort
import Mathlib.Data.List.Permutation

namespace Flapjack.Compiler.Backend.ClosToBvl

@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_split_IMP_PERM"]
theorem codeSplit_imp_perm {α : Type} (xs1 xs2 xs3 ts1 ts2 : List α)
    (split : codeSplit xs1 xs2 xs3 = (ts1, ts2)) :
    (ts1 ++ ts2).Perm (xs2 ++ xs3 ++ xs1) := by
  classical
  rw [List.perm_iff_count]
  intro value
  induction xs1 generalizing xs2 xs3 with
  | nil =>
    simp [codeSplit] at split
    rcases split with ⟨rfl, rfl⟩
    simp
  | cons head tail ih =>
    have h := ih (head :: xs3) xs2 (by simpa [codeSplit] using split)
    simp only [List.count_append, List.count_cons] at h ⊢
    omega

end Flapjack.Compiler.Backend.ClosToBvl
