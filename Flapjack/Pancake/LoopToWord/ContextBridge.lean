import Flapjack.Word
import Flapjack.Pancake.LoopToWord

/-!
# Production `WordContext` ↔ exact `Spt Nat` context for `loop_to_word`

Flapjack-internal infrastructure for bead `flapjack-pxn.18.5.9.7`.  The
executed compiler carries a loop variable map as `WordContext.vars : NatInfoMap
Nat`, an association list with first-match lookup (`Flapjack.lookupNatInfo`),
whereas the reviewed exact ports (`Flapjack.LoopToWord.findVarHOL`,
`compExpHOL`, `compHOL`) take the HOL `num |-> num` context as the exact `Spt
Nat` tree map.  This module provides the checked adapter between the two
carriers and the lookup agreement that lets bead `flapjack-pxn.18.5.9.5` route
the production `loopToWordExp`/`wordCompileExp` path through the reviewed exact
`compExpHOL`.

None of the declarations here is a HOL declaration, so none carries an `@[hol]`
attribute: HOL has no association-list-to-spt conversion of its own.

## The miss-default divergence

Production `Flapjack.wordFindVar` returns the *source* variable number `name`
when the key is absent, whereas exact `findVarHOL` returns register `0`:

```
wordFindVar context name = (lookupNatInfo name context.vars).getD name
findVarHOL context name  = (sptLookup name context).getD 0
```

The two agree on every key that is present in the context
(`wordFindVar_eq_findVarHOL_of_present` below).  On an absent key they agree
only when `name = 0`.  In HOL, `comp` runs with the context built by
`comp_func` (`cakeml/pancake/loop_to_wordScript.sml:164-169`):

```
make_ctxt 2 (params ++ vs) LN
  where vs = fromNumSet (difference (acc_vars body LN) (toNumSet params))
```

so every parameter and every variable assigned in `body` is present.  On a
well-formed source program every variable that occurs in `body` is either a
parameter or assigned before use, so the miss branch is unreachable at the
`comp_func` boundary.  That well-formedness fact is the remaining obligation
for bead `flapjack-pxn.18.5.9.5`: `WordContextCovers` records it as an explicit
predicate, and `wordFindVar_eq_findVarHOL_of_covers` reduces the whole
`WordContext` agreement to it, so the production path can be routed through
`findVarHOL` once the predicate is discharged for the `comp_func` context.
-/

namespace Flapjack.LoopToWord

/-- Adapter from the production association-list variable map to the exact HOL
`spt` context carrier, by right-recursive insertion that mirrors the accepted
`toNumSetHOL` style (`Flapjack/Pancake/LoopToWord.lean`).  Because the list is
folded from the right, the head element (the first match of
`Flapjack.lookupNatInfo`) is inserted last and therefore wins on duplicate keys,
matching the association list's first-match semantics.

Flapjack-internal infrastructure (bead `flapjack-pxn.18.5.9.7`); HOL has no
association-list-to-spt conversion, so this declaration is untagged.  The value
type is bound as `{α : Type}` rather than a universe-polymorphic `Type u`
because the reviewed `Flapjack.Spt` carrier accepts only `Type`; the production
context is `NatInfoMap Nat`, so this covers the use site. -/
def natInfoMapToSpt {α : Type} (m : NatInfoMap α) : Spt α :=
  m.foldr (fun entry acc => sptInsert entry.1 entry.2 acc) .ln

/-- One-step unfolding of the adapter: right-folding a nonempty list inserts the
head last, on top of the adapter of the tail. -/
theorem natInfoMapToSpt_cons {α : Type} (key : Nat) (value : α) (tail : NatInfoMap α) :
    natInfoMapToSpt ((key, value) :: tail) = sptInsert key value (natInfoMapToSpt tail) := by
  simp [natInfoMapToSpt]

/-- The adapter preserves lookup exactly, including duplicate keys: right-folding
inserts the association list's first match last, so `sptInsert` overwrites every
later duplicate with the first-match value.  This is unconditional; the `Nodup`
hypothesis sometimes suggested for this statement is not needed. -/
theorem sptLookup_natInfoMapToSpt {α : Type} (m : NatInfoMap α) (name : Nat) :
    sptLookup name (natInfoMapToSpt m) = lookupNatInfo name m := by
  induction m with
  | nil => simp [natInfoMapToSpt, lookupNatInfo]
  | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      rw [natInfoMapToSpt_cons]
      by_cases hkey : key = name
      · subst hkey
        simp [lookupNatInfo, sptLookup_sptInsert_same]
      · have hbeq : (key == name) = false := by
          simp [hkey]
        rw [sptLookup_sptInsert_ne key name value _ (Ne.symm hkey), ih]
        simp [lookupNatInfo, hbeq]

/-- On a present key, production `wordFindVar` and exact `findVarHOL` agree,
through the checked adapter.  This is the "key present" half of the
miss-default treatment documented at the top of the module. -/
theorem wordFindVar_eq_findVarHOL_of_present (context : WordContext) (name value : Nat)
    (h : lookupNatInfo name context.vars = some value) :
    wordFindVar context name = findVarHOL (natInfoMapToSpt context.vars) name := by
  unfold wordFindVar findVarHOL
  rw [sptLookup_natInfoMapToSpt, h]
  rfl

/-- Flapjack-internal coverage predicate: every name in `names` has a value in
the production association-list context.  This is the exact well-formedness
premise the miss-default divergence needs.  Discharging it for the `comp_func`
context (`names` = the variables occurring in the body) is the remaining
obligation for bead `flapjack-pxn.18.5.9.5`. -/
def WordContextCovers (context : WordContext) (names : List Nat) : Prop :=
  ∀ name ∈ names, ∃ value, lookupNatInfo name context.vars = some value

/-- If the context covers every name that can be looked up, production
`wordFindVar` agrees with exact `findVarHOL` on those names.  Combined with the
adapter agreement, this is the form in which the production `loop_to_word` path
can reuse the reviewed exact context functions. -/
theorem wordFindVar_eq_findVarHOL_of_covers (context : WordContext) (names : List Nat)
    (h : WordContextCovers context names) (name : Nat) (hmem : name ∈ names) :
    wordFindVar context name = findVarHOL (natInfoMapToSpt context.vars) name := by
  obtain ⟨value, hvalue⟩ := h name hmem
  exact wordFindVar_eq_findVarHOL_of_present context name value hvalue

end Flapjack.LoopToWord
