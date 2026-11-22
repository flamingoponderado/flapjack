module

public import Flapjack.Pancake.Semantics.LoopSemStateExact
public import Flapjack.Pancake.Semantics.LoopProps.EvalExact
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

@[expose] public section

/-!
# Exact ports of the `loopPropsScript.sml` `lookup` / `set_vars` lemmas

`loopProps$lookup_set_vars` (`loopPropsScript.sml:297`) and
`loopProps$lookup_set_vars_not_MEM` (`:310`) observe only how `set_vars`
rebuilds the `locals` `num_map` and how `lookup` reads it, so they are stated
over the exact `LoopSemStateFiniteExact` carrier rather than the association
list carrier of `LoopProps.lean`. The carrier's sole `|->` field `globals` is
recorded by the finite-support qualifier; `locals` is the exact `num_map`
`Spt`, which is a tree map and carries no finite-map qualifier.
-/

namespace Flapjack

open Flapjack.LoopSemStateFiniteExact

namespace LoopPropsSetVarsFiniteSupport

/-- Local same-module witness for the canonical finite-support
    `LoopSemStateFiniteExact` carrier used by the
    `fmap_as_finite_support := [globals]` qualified ports in this module
    (re-exports the checked witness of
    `Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopPropsSetVarsFiniteSupport

/-- HOL `ALOOKUP_MEM` (`alistScript.sml`): every association-list entry returned
    by `ALOOKUP` is a member of the list. Local proof support for
    `lookup_set_vars_not_MEM`; it has no tag of its own. -/
theorem memOfHolAlookup {α β : Type} [DecidableEq α] :
    ∀ (entries : List (α × β)) (key : α) (value : β),
      holAlookup entries key = some value → (key, value) ∈ entries
  | [], _, _, h => by simp [holAlookup] at h
  | (x, y) :: t, k, v, h => by
      simp only [holAlookup] at h
      split at h
      · rename_i hxy
        have hv : y = v := by injection h
        subst hv
        rw [← hxy]
        exact List.mem_cons_self
      · rename_i hxy
        exact List.mem_cons_of_mem _ (memOfHolAlookup t k v h)

/-- Membership in the name list from a successful `ALOOKUP` over `ZIP`: the
    lookup key must occur among the zipped names. Untagged support for
    `lookup_set_vars_not_MEM`. -/
theorem memOfHolAlookupZip {β : Type} :
    ∀ (names : List Nat) (values : List β) (n : Nat) (v : β),
      holAlookup (names.zip values) n = some v → n ∈ names
  | [], _, _, _, h => by simp [List.zip_nil_left, holAlookup] at h
  | name :: names, values, n, v, h => by
      cases values with
      | nil => simp [List.zip_nil_right, holAlookup] at h
      | cons value values =>
          simp only [List.zip_cons_cons, holAlookup] at h
          split at h
          · rename_i hxy
            rw [← hxy]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (memOfHolAlookupZip names values n v h)

/-- Exact port of HOL `loopProps$lookup_set_vars`
    (`cakeml/pancake/semantics/loopPropsScript.sml:297-307`):
    `lookup n (set_vars xs ys s).locals =
       case ALOOKUP (ZIP (xs,ys)) n of
       | NONE => lookup n s.locals
       | SOME v => SOME v`.
    The free variables are ordered `n`, `xs`, `ys`, `s` by their left-to-right
    occurrence in the source. `lookup` is `sptLookup` on the exact `num_map`
    `locals`, `ALOOKUP` is `holAlookup`, `ZIP` is `List.zip`, `set_vars` is the
    tagged `setVars`, and `s` is the exact `LoopSemStateFiniteExact` carrier
    whose `globals` `|->` field and positive word width are recorded by the two
    qualifiers. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "lookup_set_vars"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem lookupSetVarsHOL {width : Nat} [NeZero width] {F : Type}
    (n : Nat) (names : List Nat) (values : List (WordLocW width))
    (state : LoopSemStateFiniteExact width F) :
    sptLookup n (setVars names values state).locals =
      match holAlookup (names.zip values) n with
      | none => sptLookup n state.locals
      | some value => some value := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons _ _ => rfl
  | cons name names ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [setVars, sptAlistInsert, List.zip_cons_cons, holAlookup]
          rw [sptLookup_sptInsert]
          by_cases h : n = name
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun he : name = n => h he.symm)]
            exact ih values

/-- Exact port of HOL `loopProps$lookup_set_vars_not_MEM`
    (`cakeml/pancake/semantics/loopPropsScript.sml:310-317`):
    `~MEM n xs ⇒ lookup n (set_vars xs ys s).locals = lookup n s.locals`.
    Same free-variable order and carriers as `lookup_set_vars`; the conclusion
    follows from the tagged `lookupSetVarsHOL` and the untagged membership
    helper `memOfHolAlookupZip`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "lookup_set_vars_not_MEM"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem lookupSetVarsNotMemHOL {width : Nat} [NeZero width] {F : Type}
    (n : Nat) (names : List Nat) (values : List (WordLocW width))
    (state : LoopSemStateFiniteExact width F) :
    n ∉ names → sptLookup n (setVars names values state).locals = sptLookup n state.locals := by
  intro hn
  rw [lookupSetVarsHOL]
  cases h : holAlookup (names.zip values) n with
  | none => rfl
  | some value => exact absurd (memOfHolAlookupZip names values n value h) hn

end Flapjack
