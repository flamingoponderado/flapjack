import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.LocalListHelpers

/-!
# crep_to_loop `crep_to_loop_compile_prog_lab_min`

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`crep_to_loop_compile_prog_lab_min` (4398-4400) (bead `flapjack-pxn.18.5.6.33.21`).

The `distinct_make_funcs` slice (bead
`flapjack-pxn.18.5.6.33.20.1`) uses the corrected exact finite-support
`make_funcs` result. The remaining five `make_funcs`/`compile_prog` list lemmas
remain on the parent bead `flapjack-pxn.18.5.6.33.20`.

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

/-- A successful lookup in the HOL equality fold over a reversed association
list must come from an entry in the original list. This is local infrastructure
for the exact `make_funcs` lemma below. -/
private theorem flookup_fupdateListHOL_reverse_mem {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (key : α) (value : β),
      FLOOKUP (FUPDATE_LIST_HOL (FEMPTY : FiniteMap α β) entries.reverse) key =
        some value → (key, value) ∈ entries
  | [], key, value, h => by
      simp [FUPDATE_LIST_HOL, FLOOKUP, FEMPTY] at h
  | entry :: entries, key, value, h => by
      simp only [List.reverse_cons, FUPDATE_LIST_HOL, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at h
      change (if key = entry.1 then some entry.2 else
        FLOOKUP (FUPDATE_LIST_HOL (FEMPTY : FiniteMap α β) entries.reverse) key) =
          some value at h
      by_cases heq : key = entry.1
      · simp [heq] at h
        cases h
        subst key
        exact List.mem_cons_self
      · simp [heq] at h
        exact List.mem_cons_of_mem _ (flookup_fupdateListHOL_reverse_mem
          entries key value h)

/-- Each association produced by the exact `make_funcs` list construction has
the key, label, and parameter count of one source program entry. -/
private theorem makeFuncsExact_entry_mem {α β γ : Type}
    (prog : List (α × List β × γ)) (key : α) (label arity : Nat)
    (h : (key, (label, arity)) ∈ (prog.zip (List.range prog.length)).map
      (fun entry => (entry.1.1, (firstLoopName + entry.2,
        entry.1.2.1.length)))) :
    ∃ (i : Nat) (hi : i < prog.length), key = (prog[i]'hi).1 ∧
      label = firstLoopName + i ∧ arity = (prog[i]'hi).2.1.length := by
  obtain ⟨⟨e, i⟩, he, hf⟩ := List.mem_map.mp h
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
  simp only [List.length_zip, List.length_range, Nat.min_self] at hk
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at hke
  obtain ⟨rfl, rfl⟩ := hke
  simp only [Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  exact ⟨k, hk, rfl, rfl, rfl⟩

/-- Exact HOL `distinct_make_funcs` (`crep_to_loopProofScript.sml:3757-3758`):
    `!crep_code. distinct_funcs (make_funcs crep_code)`. The exact tagged
    `make_funcs_def` dependency carries the reviewed finite-support result
    translation and lookup witness. Its map is consumed by the exact tagged
    `crepToLoopDistinctFuncsExact`, whose standalone finite-support parameter
    has its own canonical roundtrip witness. All three program tuple components
    remain polymorphic and no equality typeclass or other premise is added. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_make_funcs"]
theorem distinct_make_funcs {α β γ : Type} :
    ∀ (crep_code : List (α × List β × γ)),
      crepToLoopDistinctFuncsExact (crepToLoopMakeFuncsExactHOL crep_code) := by
  letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  intro crep_code x y n m rm rm' hx hy hnm
  change (crepToLoopMakeFuncsExactHOL crep_code).lookup x = some (n, rm) at hx
  change (crepToLoopMakeFuncsExactHOL crep_code).lookup y = some (m, rm') at hy
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL crep_code x] at hx
  rw [holFmapAsFiniteSupportResultWitness_crepToLoopMakeFuncsExactHOL crep_code y] at hy
  obtain ⟨i, hi, rfl, rfl, _⟩ := makeFuncsExact_entry_mem crep_code x n rm
    (flookup_fupdateListHOL_reverse_mem _ _ _ hx)
  obtain ⟨j, hj, rfl, hm, _⟩ := makeFuncsExact_entry_mem crep_code y m rm'
    (flookup_fupdateListHOL_reverse_mem _ _ _ hy)
  have : i = j := by omega
  subst this
  rfl

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
