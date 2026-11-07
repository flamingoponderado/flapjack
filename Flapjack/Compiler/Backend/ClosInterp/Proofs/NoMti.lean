import Flapjack.Compiler.Backend.ClosInterp.Optimise
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti

/-! Pre-multi-argument syntax under incremental interpreter insertion. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open ClosLang ClosProps

private theorem optInterp_noMti (e e' : Exp) (h : optInterp e = some e') : noMti e' := by
  unfold optInterp at h
  split at h
  · simp only [Option.some.injEq] at h
    subst e'
    simp [noMti, noMtiList]
  · simp at h

private theorem optInterp1_noMti (e : Exp) (h : noMti e) : noMti (optInterp1 e) := by
  cases result : optInterp e with
  | none => simpa [optInterp1, result] using h
  | some e' => simpa [optInterp1, result] using optInterp_noMti e e' result

private theorem mappedOpt_noMti (es : List Exp) (h : noMtiList es) :
    noMtiList (es.map optInterp1) := by
  rw [noMtiList_iff] at h ⊢
  intro e member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact optInterp1_noMti source (h source sourceMember)

private theorem insertInterp1_noMti (e : Exp) (h : noMti e) : noMti (insertInterp1 e) := by
  cases result : optInterp e with
  | some e' => simpa [insertInterp1, result] using optInterp_noMti e e' result
  | none =>
    cases e <;> simp [insertInterp1, result, noMti] at h ⊢ <;> try assumption
    case «let» t es body => exact ⟨mappedOpt_noMti es h.1, h.2⟩

/-- Incremental interpreter insertion preserves pre-MTI syntax. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "insert_interp_no_mti"]
theorem insertInterp_noMti (e : Exp) (xs : List Exp)
    (member : e ∈ insertInterp xs) (safe : ∀ x ∈ xs, noMti x) : noMti e := by
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp (by simpa [insertInterp] using member)
  exact insertInterp1_noMti source (safe source sourceMember)

end Flapjack.Compiler.Backend.ClosInterp
