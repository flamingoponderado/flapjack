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
`comp_func` boundary.  `WordContextCovers` records it as an explicit predicate,
and `wordFindVar_eq_findVarHOL_of_covers` reduces the whole `WordContext`
agreement to it.

`loopToWordCompContext_covers` below discharges that obligation for the exact
context the executed `loop_to_word` stage threads
(`Flapjack.LoopToWord.loopToWordCompContext`), so the production lookup is known
to agree with exact `findVarHOL` on every referenced variable.

## Full `compExpHOL` routing status: blocked on carrier migration

Discharging coverage does not let the executed expression compiler *call*
`compExpHOL`, because the two operate on different carriers and at different
type parameters:

* `Flapjack.wordCompileExp : WordContext → LoopExp α → Option (WordExp α)` is
  polymorphic in `α` and uses the production `LoopExp` (which adds `crepOp`/`cmp`
  to HOL `loopLang$exp`) and production `WordExp` (whose `lookup` field is
  `WordStore α`, a datatype with a phantom word parameter).
* `compExpHOL : Spt Nat → HolLoopExp width → WordLangExpHOL (BitVec width)` is
  fixed at the positive width `BitVec width` and uses the exact `HolLoopExp` and
  `WordLangExpHOL` (whose `lookup` field is `WordStoreHOL = WordStore Unit`).

There is no total function `LoopExp α → HolLoopExp width` (not even
`LoopExp (BitVec width) → HolLoopExp width`); the repository only has the
HOL-to-executable projection `holLoopExpToExecutable` and the relation
`loopExpExecRel`.  Routing the executed `wordCompileExp` through `compExpHOL`
therefore requires either (1) migrating the production expression/program
carriers to the exact HOL carriers (changing `LoopExp`/`WordExp`/`WordProg`), or
(2) specializing the executed `loopToWordAtom`/`loopToWordProgWithLabels`/
`loopToWordCompFunc`/`pipelineWordFunctionsSource` chain to `BitVec width` with a
new codec and a whole-stage equality proof (a width-specialized duplicate of the
compiler stage).  Both change the executed compiler's carriers or structure
across `Flapjack/Word.lean`, `Flapjack/Pancake/LoopToWord.lean` and
`Flapjack/Pipeline.lean` and their callers, which is the broad state migration
the routing bead's blocker policy excludes.  `compExpHOL` therefore remains
proof-side; the production stage keeps its list-carrier implementation.
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

/-! ### Discharging the coverage obligation for the production `comp_func` context -/

/-- A key mentioned by an association-list map appears among the map's first
projections. -/
theorem fst_mem_of_mem_pair {α : Type} {m : NatInfoMap α} {name : Nat} {value : α}
    (h : (name, value) ∈ m) : name ∈ m.map Prod.fst := by
  induction m with
  | nil => simp at h
  | cons head tail ih =>
      rw [List.mem_cons] at h
      rw [List.map_cons, List.mem_cons]
      rcases h with hhead | htail
      · left
        exact congrArg Prod.fst hhead
      · right
        exact ih htail

/-- If a key appears among the map's first projections, `lookupNatInfo` returns
some value for it (the first match). -/
theorem lookupNatInfo_isSome_of_mem {α : Type} {m : NatInfoMap α} {name : Nat}
    (h : name ∈ m.map Prod.fst) : ∃ w, lookupNatInfo name m = some w := by
  induction m generalizing name with
  | nil => simp at h
  | cons head tail ih =>
      obtain ⟨key, val⟩ := head
      rw [List.map_cons, List.mem_cons] at h
      rcases h with hkey | htail
      · subst hkey
        exact ⟨val, by simp [lookupNatInfo]⟩
      · by_cases hk : key = name
        · subst hk
          exact ⟨val, by simp [lookupNatInfo]⟩
        · have hfalse : (key == name) = false := by
            cases hbeq : key == name <;> simp_all [beq_iff_eq]
          simp only [lookupNatInfo]
          rw [if_neg (by simp [hfalse])]
          exact ih htail

/-- Every name in `names` is a key of `sourceFallbackContext names`, with value
`0`. -/
theorem mem_sourceFallbackContext {names : List Nat} {name : Nat} (h : name ∈ names) :
    (name, 0) ∈ sourceFallbackContext names := by
  induction names with
  | nil => simp at h
  | cons head tail ih =>
      rw [List.mem_cons] at h
      rcases h with rfl | htail
      · simp [sourceFallbackContext]
      · simp [sourceFallbackContext, ih htail]

/-- `makeCtxt` only prepends entries to its seed context, so it preserves every
entry already present. -/
theorem mem_makeCtxt_of_mem {next : Nat} {names : List Nat}
    {context : List (Nat × Nat)} {entry : Nat × Nat} (h : entry ∈ context) :
    entry ∈ makeCtxt next names context := by
  induction names generalizing next context with
  | nil => simpa [makeCtxt] using h
  | cons name rest ih =>
      rw [makeCtxt, insertVar]
      exact ih (next := next + 2) (context := (name, next) :: context)
        (List.mem_cons_of_mem (name, next) h)

/-- `foldl max` is at least its seed. -/
theorem le_foldl_max_self (l : List Nat) (acc : Nat) : acc ≤ l.foldl max acc := by
  induction l generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (max acc head))

/-- `foldl max` is at least every member of the list. -/
theorem le_foldl_max_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) (acc : Nat) :
    x ≤ l.foldl max acc := by
  induction l generalizing acc with
  | nil => simp at h
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with hx | htail
      · rw [hx]
        exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max_self tail (max acc head))
      · exact ih htail (max acc head)

/-- The production `comp_func` context (`Flapjack.LoopToWord.loopToWordCompContext`)
covers every variable referenced by the compiled body.  The context is
`makeCtxt 2 (params ++ variables) fallback`, and `fallback` seeds every number up
to the `foldl max` bound with value `0`; `makeCtxt` only prepends, so the seed
covers all referenced names.  This discharges the well-formedness premise noted
at the top of this module, so `wordFindVar_eq_findVarHOL_of_covers` applies to
the executed `loop_to_word` context. -/
theorem loopToWordCompContext_covers (params : List Nat) (body : LoopProg α) :
    WordContextCovers { vars := loopToWordCompContext params body }
      (loopReferencedVars body) := by
  intro name hmem
  simp only [loopToWordCompContext]
  refine lookupNatInfo_isSome_of_mem ?_
  refine fst_mem_of_mem_pair (mem_makeCtxt_of_mem (mem_sourceFallbackContext ?_))
  rw [List.mem_range]
  exact Nat.lt_succ_of_le
    (le_foldl_max_of_mem (List.mem_append_right (params ++ loopAccVars body []) hmem) 0)

/-- On the production `comp_func` context, every referenced variable is present,
so production `wordFindVar` agrees with exact `findVarHOL` through the adapter. -/
theorem wordFindVar_eq_findVarHOL_loopToWordCompContext (params : List Nat)
    (body : LoopProg α) (name : Nat) (hmem : name ∈ loopReferencedVars body) :
    wordFindVar { vars := loopToWordCompContext params body } name =
      findVarHOL (natInfoMapToSpt (loopToWordCompContext params body)) name :=
  wordFindVar_eq_findVarHOL_of_covers _ _ (loopToWordCompContext_covers params body)
    name hmem

end Flapjack.LoopToWord
