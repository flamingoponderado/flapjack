import Flapjack.Compiler.Backend.ClosInterp.Proofs.Globals
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Preservation of function annotations by interpreter insertion. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open ClosLang ClosProps

/-- Local fallback case of the HOL insertion proof; no separate HOL declaration. -/
private theorem optInterp1_fnVarsNone (e : Exp) (h : fnVarsNoneExp e) :
    fnVarsNoneExp (optInterp1 e) := by
  cases result : optInterp e with
  | none => simpa [optInterp1, result] using h
  | some e' => simpa [optInterp1, result, everyFnVarsNone] using (optInterp_lemma e e' 0 result).2.2.2.1

/-- Local mapped-list case of the HOL insertion proof; no separate HOL declaration. -/
private theorem mappedOpt_fnVarsNone (es : List Exp) (h : everyFnVarsNone es) :
    everyFnVarsNone (es.map optInterp1) := by
  rw [everyFnVarsNone_every] at h ⊢
  intro e member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  simpa [everyFnVarsNone] using optInterp1_fnVarsNone source (by simpa [everyFnVarsNone] using h source sourceMember)

/-- Local singleton case of the HOL insertion proof; no separate HOL declaration. -/
private theorem insertInterp1_fnVarsNone (e : Exp) (h : fnVarsNoneExp e) :
    fnVarsNoneExp (insertInterp1 e) := by
  cases result : optInterp e with
  | some e' => simpa [insertInterp1, result, everyFnVarsNone] using (optInterp_lemma e e' 0 result).2.2.2.1
  | none =>
    cases e <;> simp [insertInterp1, result, fnVarsNoneExp] at h ⊢ <;> try assumption
    case «let» t es body => exact ⟨h.1, mappedOpt_fnVarsNone es h.2⟩

/-- Interpreter insertion preserves absent function-variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "every_Fn_vs_NONE_insert_interp"]
theorem everyFnVarsNone_insertInterp (xs : List Exp) (safe : everyFnVarsNone xs) :
    everyFnVarsNone (insertInterp xs) := by
  rw [everyFnVarsNone_every] at safe ⊢
  intro e member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp (by simpa [insertInterp] using member)
  simpa [everyFnVarsNone] using insertInterp1_fnVarsNone source (by simpa [everyFnVarsNone] using safe source sourceMember)

end Flapjack.Compiler.Backend.ClosInterp
