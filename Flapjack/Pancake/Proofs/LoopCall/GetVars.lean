import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.HolRef

/-!
# `loop_callProof` `get_vars` helper lemmas

Counterpart module for `cakeml/pancake/proofs/loop_callProofScript.sml`.  The two
named HOL list lemmas used by the `Call` case of `compile_correct`
(`get_vars_front` at `loop_callProofScript.sml:273` and `get_vars_last` at
`:300`) are ported exactly over the tagged exact
`LoopSemStateFiniteExact.getVars` (the Lean port of HOL `loopSem$get_vars`,
`loopSemScript.sml` `get_vars_def`) and `sptLookup`.

HOL `FRONT` and `LAST` are core `listTheory` functions declared outside the
CakeML development, so their Lean renderings `List.dropLast` and
`List.getLast` are untagged infrastructure; the two theorems themselves carry
the exact `loop_callProofScript.sml` tags.  The nonemptiness of the result list
is derived internally (`getVars_ne_nil`), so neither theorem takes an extra
premise beyond the HOL hypotheses.

The remaining case pieces of `compile_correct` are assembled separately on
`flapjack-pxn.18.5.7`.
-/

namespace Flapjack

/- Fresh-namespace re-export of the canonical `fmap_as_finite_support` witness
   for the imported `LoopSemStateFiniteExact` carrier, used by the qualified
   tags below. -/
namespace LoopCallGetVarsFiniteSupport

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopCallGetVarsFiniteSupport

namespace LoopSemStateFiniteExact

/-- `get_vars` returns exactly one value per requested name: the result list has
    the same length as the argument list (used by the `FRONT`/`LAST` helpers). -/
theorem getVars_length {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (state : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (h : getVars names state = some values) :
    values.length = names.length := by
  induction names generalizing values with
  | nil =>
      have h' : some [] = some values := by simpa using h
      obtain rfl := Option.some.inj h'
      rfl
  | cons name names ih =>
      rw [getVars_cons] at h
      cases hv : sptLookup name state.locals with
      | none => simp [hv] at h
      | some v =>
          cases hg : getVars names state with
          | none => simp [hv, hg] at h
          | some vs =>
              have h' : some (v :: vs) = some values := by simpa [hv, hg] using h
              obtain rfl := Option.some.inj h'
              simp [ih vs hg]

/-- A nonempty request list yields a nonempty result list. -/
theorem getVars_ne_nil {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (state : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (h : getVars names state = some values)
    (hne : names ≠ []) : values ≠ [] := by
  intro hv
  have hlen := getVars_length names state values h
  subst hv
  simp only [List.length_nil] at hlen
  exact hne (List.length_eq_zero_iff.mp hlen.symm)

/-- Exact port of HOL `get_vars_front` (`loop_callProofScript.sml:273-297`):
    `FRONT` of the request list maps to `FRONT` of the result list. -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "get_vars_front"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem getVars_dropLast {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (state : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (h : getVars names state = some values)
    (hne : names ≠ []) :
    getVars names.dropLast state = some values.dropLast := by
  induction names generalizing values with
  | nil => exact absurd rfl hne
  | cons name names ih =>
      cases names with
      | nil =>
          rw [getVars_cons] at h
          cases hv : sptLookup name state.locals with
          | none => simp [hv] at h
          | some v =>
              have h' : some [v] = some values := by simpa [hv] using h
              obtain rfl := Option.some.inj h'
              simp [getVars_nil]
      | cons name2 rest =>
          rw [getVars_cons] at h
          cases hv : sptLookup name state.locals with
          | none => simp [hv] at h
          | some v =>
              cases hg : getVars (name2 :: rest) state with
              | none => simp [hv, hg] at h
              | some vs =>
                  have h' : some (v :: vs) = some values := by simpa [hv, hg] using h
                  obtain rfl := Option.some.inj h'
                  have ihv := ih vs hg (by simp)
                  have hvs : vs ≠ [] :=
                    getVars_ne_nil (name2 :: rest) state vs hg (by simp)
                  cases vs with
                  | nil => exact absurd rfl hvs
                  | cons w ws =>
                      rw [List.dropLast_cons_cons]
                      simp only [getVars_cons, hv, Option.bind_some, ihv,
                        Option.map_some]
                      rfl

/-- Internal form of `get_vars_last` with the (derivable) nonemptiness of the
    result list passed explicitly; `getVars_getLast` instantiates it. -/
theorem getVars_getLast_aux {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (state : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (h : getVars names state = some values)
    (hne : names ≠ []) (hvne : values ≠ []) :
    sptLookup (names.getLast hne) state.locals = some (values.getLast hvne) := by
  induction names generalizing values with
  | nil => exact absurd rfl hne
  | cons name names ih =>
      cases names with
      | nil =>
          rw [getVars_cons] at h
          cases hl : sptLookup name state.locals with
          | none => simp [hl] at h
          | some v =>
              have h' : some [v] = some values := by simpa [hl] using h
              obtain rfl := Option.some.inj h'
              rw [List.getLast_singleton hne, List.getLast_singleton hvne]
              exact hl
      | cons name2 rest =>
          rw [getVars_cons] at h
          cases hl : sptLookup name state.locals with
          | none => simp [hl] at h
          | some v =>
              cases hg : getVars (name2 :: rest) state with
              | none => simp [hl, hg] at h
              | some vs =>
                  have h' : some (v :: vs) = some values := by simpa [hl, hg] using h
                  obtain rfl := Option.some.inj h'
                  cases vs with
                  | nil =>
                      exact absurd rfl
                        (getVars_ne_nil (name2 :: rest) state [] hg (by simp))
                  | cons w ws =>
                      have hn' : (name2 :: rest) ≠ [] := by simp
                      have hv' : (w :: ws) ≠ [] := by simp
                      have ix := ih (w :: ws) hg hn' hv'
                      rw [List.getLast_cons hn', List.getLast_cons hv']
                      exact ix

/-- Exact port of HOL `get_vars_last` (`loop_callProofScript.sml:300-324`):
    the last requested name looks up the last result value. -/
@[hol "cakeml/pancake/proofs/loop_callProofScript.sml" "get_vars_last"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem getVars_getLast {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (state : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (h : getVars names state = some values)
    (hne : names ≠ []) :
    sptLookup (names.getLast hne) state.locals =
      some (values.getLast (getVars_ne_nil names state values h hne)) :=
  getVars_getLast_aux names state values h hne (getVars_ne_nil names state values h hne)

end LoopSemStateFiniteExact

end Flapjack