import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.LocalListHelpers

/-!
# crep_to_loop `crep_to_loop_compile_prog_lab_min`

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`crep_to_loop_compile_prog_lab_min` (4398-4400) (bead `flapjack-pxn.18.5.6.33.21`).

The six `make_funcs`/`compile_prog` list lemmas of
`crep_to_loopProofScript.sml` 3757-3945 (bead `flapjack-pxn.18.5.6.33.20`) are
held pending the finite-support carrier correction
(`flapjack-pxn.18.5.6.33.22.1`) and are intentionally not included here; only
the generic `List.zipWith`/`Prod.fst` helper they share is kept, untagged.

`compile_prog` is the tagged `compileProgHOLExact` (`compile_prog_def`) and
`first_name` the tagged `firstLoopName` (`first_name_def`, 64).
-/

namespace Flapjack

private theorem map_fst_zipWith_pair {α β γ : Type} (g : α → β → γ) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (List.zipWith (fun x y => (x, g x y)) xs ys).map Prod.fst = xs
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: xs, _ :: ys, h => by
      simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact map_fst_zipWith_pair g xs ys (by simpa using h)

/-- Exact HOL `crep_to_loop_compile_prog_lab_min` (`crep_to_loopProofScript.sml:4398-4400`):
    `crep_to_loop$compile_prog c cprog = lprog ⇒ EVERY (λprog. 60 ≤ FST prog) lprog`,
    with its free variables universally quantified and `EVERY` as `∀ x ∈ lprog`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_to_loop_compile_prog_lab_min"
  (words_as_type_indexed_bitvec)]
theorem crep_to_loop_compile_prog_lab_min {width : Nat} [NeZero width] :
    ∀ (c : Compiler.Encoders.Asm.AsmArchitecture)
      (cprog : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
      (lprog : List (Nat × List Nat × HolLoopProg width)),
      compileProgHOLExact c cprog = lprog → ∀ prog ∈ lprog, 60 ≤ prog.1 := by
  intro c cprog lprog h prog hp
  subst h
  have hfst : prog.1 ∈ (compileProgHOLExact c cprog).map Prod.fst := List.mem_map_of_mem hp
  have e : ((compileProgHOLExact c cprog).map Prod.fst) =
      (List.range cprog.length).map (fun n => n + firstLoopName) := by
    simp only [compileProgHOLExact]
    exact map_fst_zipWith_pair _ _ _ (by simp)
  rw [e, List.mem_map] at hfst
  obtain ⟨n, _, hn⟩ := hfst
  rw [← hn]
  simp [firstLoopName]

end Flapjack
