import Flapjack.HolRef

/-!
# Exact `spt`/`num_set` carrier

Counterpart of the HOL `spt` data structure (`HOL/src/finite_maps/sptreeScript.sml`)
and of the CakeML abbreviation `num_set = unit spt`
(`cakeml/misc/miscScript.sml:787`).

HOL's `spt` is defined outside the CakeML submodule, so the datatype itself cannot
carry an `@[hol]` reference into `cakeml/`.  The carrier below mirrors the HOL
constructors exactly:

```
Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt
```

The taggable `cakeml` declaration is the abbreviation `num_set = unit spt`, which
`Misc.Sptree.NumSet` matches by construction.

`Misc.Sptree.sptLookup`, `Misc.Sptree.sptInsert`, `Misc.Sptree.sptIsEmpty` and
`Misc.Sptree.sptWf` mirror the HOL `lookup`, `insert`, `isEmpty` (i.e. `t = LN`)
and `wf` definitions, including the recursive key arithmetic
`(k - 1) DIV 2` and the `EVEN k` branch selection.  `EVEN` is rendered as
`k % 2 = 0` in Lean.  The recursion is written so that the recursive call sits in
each parity branch on a direct subterm, which makes the equations hold
definitionally (as Lean structural recursion rather than HOL's
well-founded recursion).
-/

namespace Flapjack

/-- Exact Lean rendering of the HOL `spt` datatype
`spt = LN | LS 'a | BN spt spt | BS spt 'a spt`. -/
inductive Spt (α : Type) : Type where
  /-- `LN`: the leaf holding no value. -/
  | ln : Spt α
  /-- `LS a`: the leaf holding `a`. -/
  | ls (value : α) : Spt α
  /-- `BN t1 t2`: an internal node with no value. -/
  | bn (left right : Spt α) : Spt α
  /-- `BS t1 a t2`: an internal node holding `a`. -/
  | bs (left : Spt α) (value : α) (right : Spt α) : Spt α
  deriving Repr, DecidableEq

/-- The CakeML abbreviation `num_set = unit spt` (`cakeml/misc/miscScript.sml:787`). -/
@[hol "cakeml/misc/miscScript.sml" "num_set"]
abbrev NumSet : Type := Spt Unit

/-- HOL `sptree$isEmpty t = (t = LN)`. -/
def sptIsEmpty {α : Type} : Spt α → Bool
  | .ln => true
  | _ => false

/-- HOL `sptree$wf`: well-formedness (no internal node whose both children are empty). -/
def sptWf {α : Type} : Spt α → Bool
  | .ln => true
  | .ls _ => true
  | .bn left right => sptWf left && sptWf right && !(sptIsEmpty left && sptIsEmpty right)
  | .bs left _ right => sptWf left && sptWf right && !(sptIsEmpty left && sptIsEmpty right)

/-- HOL `sptree$lookup` with the recursive key arithmetic `(k - 1) DIV 2`. -/
def sptLookup {α : Type} (key : Nat) : Spt α → Option α
  | .ln => none
  | .ls value => if key = 0 then some value else none
  | .bn left right =>
      if key = 0 then none
      else if key % 2 = 0 then sptLookup ((key - 1) / 2) left
      else sptLookup ((key - 1) / 2) right
  | .bs left value right =>
      if key = 0 then some value
      else if key % 2 = 0 then sptLookup ((key - 1) / 2) left
      else sptLookup ((key - 1) / 2) right

/-- HOL `sptree$insert` with the recursive key arithmetic `(k - 1) DIV 2`. -/
def sptInsert {α : Type} (key : Nat) (value : α) : Spt α → Spt α
  | .ln =>
      if key = 0 then .ls value
      else if key % 2 = 0 then .bn (sptInsert ((key - 1) / 2) value .ln) .ln
      else .bn .ln (sptInsert ((key - 1) / 2) value .ln)
  | .ls existing =>
      if key = 0 then .ls value
      else if key % 2 = 0 then .bs (sptInsert ((key - 1) / 2) value .ln) existing .ln
      else .bs .ln existing (sptInsert ((key - 1) / 2) value .ln)
  | .bn left right =>
      if key = 0 then .bs left value right
      else if key % 2 = 0 then .bn (sptInsert ((key - 1) / 2) value left) right
      else .bn left (sptInsert ((key - 1) / 2) value right)
  | .bs left existing right =>
      if key = 0 then .bs left value right
      else if key % 2 = 0 then .bs (sptInsert ((key - 1) / 2) value left) existing right
      else .bs left existing (sptInsert ((key - 1) / 2) value right)

/-- `sptLookup` on the empty set is `none`. -/
@[simp] theorem sptLookup_ln {α : Type} (key : Nat) :
    sptLookup key (.ln : Spt α) = none := by simp [sptLookup]

/-- `sptIsEmpty` on the empty tree is `true`. -/
@[simp] theorem sptIsEmpty_ln {α : Type} : sptIsEmpty (.ln : Spt α) = true := by simp [sptIsEmpty]

/-- `sptWf` on the empty tree is `true`. -/
@[simp] theorem sptWf_ln {α : Type} : sptWf (.ln : Spt α) = true := by simp [sptWf]

/-- Inserting key `0` into the empty tree gives `LS value`. -/
@[simp] theorem sptInsert_ln_zero {α : Type} (value : α) :
    sptInsert 0 value (.ln : Spt α) = .ls value := by simp [sptInsert]

/-- Looking up key `0` after inserting it gives the inserted value. -/
theorem sptLookup_sptInsert_zero {α : Type} (value : α) (tree : Spt α) :
    sptLookup 0 (sptInsert 0 value tree) = some value := by
  cases tree <;> simp [sptInsert, sptLookup]

/-- Inserting key `0` overwrites any existing value at key `0`. -/
theorem sptLookup_sptInsert_zero_overwrite {α : Type} (first second : α) (tree : Spt α) :
    sptLookup 0 (sptInsert 0 second (sptInsert 0 first tree)) = some second := by
  cases tree <;> simp [sptInsert, sptLookup]

/-- HOL `lrnext`: the increment used when placing subtrees in the spt index
space (`HOL/src/finite_maps/sptreeScript.sml:421-422`). -/
def lrNext : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * lrNext (n / 2)

/-- HOL sptree `foldi` (`HOL/src/finite_maps/sptreeScript.sml:737-749`) over
the exact tree, in the same mixed order. -/
def sptFoldi {α : Type} (f : Nat → α → List (Nat × α) → List (Nat × α))
    (index : Nat) (accumulator : List (Nat × α)) : Spt α → List (Nat × α)
  | .ln => accumulator
  | .ls value => f index value accumulator
  | .bn left right =>
      let increment := lrNext index
      sptFoldi f (index + increment)
        (sptFoldi f (index + 2 * increment) accumulator left) right
  | .bs left value right =>
      let increment := lrNext index
      sptFoldi f (index + increment)
        (f index value (sptFoldi f (index + 2 * increment) accumulator left)) right

/-- HOL `toAList` (`HOL/src/finite_maps/sptreeScript.sml:898-899`): the
association list of the tree in the mixed sptree enumeration order. -/
def sptToAList {α : Type} (tree : Spt α) : List (Nat × α) :=
  sptFoldi (fun key value accumulator => (key, value) :: accumulator) 0 [] tree

/-- `toAList` on the empty tree is empty. -/
@[simp] theorem sptToAList_ln {α : Type} :
    sptToAList (.ln : Spt α) = [] := by simp [sptToAList, sptFoldi]

/-- HOL sptree `list_insert` (`HOL/src/finite_maps/sptreeScript.sml:2031-2034`):
    insert each key (with unit value) into the tree, left to right. The HOL
    source lives in the HOL installation's `src/finite_maps`, outside `cakeml/`,
    so this rendering is Flapjack infrastructure and carries no `@[hol]` tag. -/
def sptListInsert : List Nat → NumSet → NumSet
  | [], tree => tree
  | key :: keys, tree => sptListInsert keys (sptInsert key () tree)

/-- HOL `sptree$mk_BN` (`HOL/src/finite_maps/sptreeScript.sml:88-92`): collapse
two empty children back to `LN`.  The HOL source lives in the HOL
installation's `src/finite_maps`, outside `cakeml/`, so this rendering is
Flapjack infrastructure and carries no `@[hol]` tag. -/
def sptMkBN {α : Type} (left right : Spt α) : Spt α :=
  match left, right with
  | .ln, .ln => .ln
  | _, _ => .bn left right

/-- HOL `sptree$mk_BS` (`HOL/src/finite_maps/sptreeScript.sml:94-98`): collapse
the two empty children around a value to `LS`.  Untagged Flapjack
infrastructure, as for `sptMkBN`. -/
def sptMkBS {α : Type} (left : Spt α) (value : α) (right : Spt α) : Spt α :=
  match left, right with
  | .ln, .ln => .ls value
  | _, _ => .bs left value right

/-- HOL `sptree$delete` (`HOL/src/finite_maps/sptreeScript.sml:99-113`) with the
recursive key arithmetic `(k - 1) DIV 2` and the `mk_BN`/`mk_BS` collapsing.
Untagged Flapjack infrastructure (source outside `cakeml/`). -/
def sptDelete {α : Type} (key : Nat) : Spt α → Spt α
  | .ln => .ln
  | .ls value => if key = 0 then .ln else .ls value
  | .bn left right =>
      if key = 0 then .bn left right
      else if key % 2 = 0 then sptMkBN (sptDelete ((key - 1) / 2) left) right
      else sptMkBN left (sptDelete ((key - 1) / 2) right)
  | .bs left value right =>
      if key = 0 then .bn left right
      else if key % 2 = 0 then
        sptMkBS (sptDelete ((key - 1) / 2) left) value right
      else sptMkBS left value (sptDelete ((key - 1) / 2) right)

/-- HOL `sptree$union` (`HOL/src/finite_maps/sptreeScript.sml:219-244`).  The
left operand's value wins on shared keys, matching HOL's clause order.
Untagged Flapjack infrastructure (source outside `cakeml/`). -/
def sptUnion {α : Type} : Spt α → Spt α → Spt α
  | .ln, right => right
  | .ls value, right =>
      match right with
      | .ln => .ls value
      | .ls _ => .ls value
      | .bn first second => .bs first value second
      | .bs first _ second => .bs first value second
  | .bn first second, right =>
      match right with
      | .ln => .bn first second
      | .ls value => .bs first value second
      | .bn first' second' => .bn (sptUnion first first') (sptUnion second second')
      | .bs first' value second' =>
          .bs (sptUnion first first') value (sptUnion second second')
  | .bs first value second, right =>
      match right with
      | .ln => .bs first value second
      | .ls _ => .bs first value second
      | .bn first' second' =>
          .bs (sptUnion first first') value (sptUnion second second')
      | .bs first' _ second' =>
          .bs (sptUnion first first') value (sptUnion second second')
termination_by left _ => sizeOf left

/-- HOL `sptree$inter` (`HOL/src/finite_maps/sptreeScript.sml:272-291`): keep
only keys present in both trees, with the left operand's value.  HOL's declared
type is heterogeneous (`'a num_map -> 'b num_map -> 'a num_map`; the second
tree's values are never read), so this rendering is generic in both value
types.  Untagged Flapjack infrastructure (source outside `cakeml/`). -/
def sptInter {α β : Type} : Spt α → Spt β → Spt α
  | .ln, _ => .ln
  | .ls value, right =>
      match right with
      | .ln => .ln
      | .ls _ => .ls value
      | .bn _ _ => .ln
      | .bs _ _ _ => .ls value
  | .bn first second, right =>
      match right with
      | .ln => .ln
      | .ls _ => .ln
      | .bn first' second' => sptMkBN (sptInter first first') (sptInter second second')
      | .bs first' _ second' =>
          sptMkBN (sptInter first first') (sptInter second second')
  | .bs first value second, right =>
      match right with
      | .ln => .ln
      | .ls _ => .ls value
      | .bn first' second' =>
          sptMkBN (sptInter first first') (sptInter second second')
      | .bs first' _ second' =>
          sptMkBS (sptInter first first') value (sptInter second second')
termination_by left _ => sizeOf left

/-- HOL `list_delete` (`cakeml/compiler/backend/backend_commonScript.sml:180-182`):
delete each key (with unit value) from the tree, left to right.  HOL's declared
type is generic in the map's value type (`num list -> 'a num_map -> 'a num_map`),
so this rendering is generic too. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "list_delete_def"]
def sptListDelete {α : Type} : List Nat → Spt α → Spt α
  | [], tree => tree
  | key :: keys, tree => sptListDelete keys (sptDelete key tree)

/-- HOL `oEL` (`HOL/src/list/src/listScript.sml:5482-5484`): the `n`-th list
element as an option.  Untagged Flapjack infrastructure (source outside
`cakeml/`). -/
def sptOel {α : Type} : Nat → List α → Option α
  | _, [] => none
  | 0, value :: _ => some value
  | n + 1, _ :: rest => sptOel n rest

/-- HOL `sptree$size` (`HOL/src/finite_maps/sptreeScript.sml:117-122`): the
number of stored values.  Untagged Flapjack infrastructure (source outside
`cakeml/`). -/
def sptSize {α : Type} : Spt α → Nat
  | .ln => 0
  | .ls _ => 1
  | .bn left right => sptSize left + sptSize right
  | .bs left _ right => sptSize left + sptSize right + 1

@[simp] theorem sptSize_ln {α : Type} : sptSize (.ln : Spt α) = 0 := rfl
@[simp] theorem sptSize_ls {α : Type} (value : α) : sptSize (.ls value) = 1 := rfl
@[simp] theorem sptSize_bn {α : Type} (left right : Spt α) :
    sptSize (.bn left right) = sptSize left + sptSize right := rfl
@[simp] theorem sptSize_bs {α : Type} (left : Spt α) (value : α) (right : Spt α) :
    sptSize (.bs left value right) = sptSize left + sptSize right + 1 := rfl

/-- HOL `loop_liveScript.sml:27-33 size_mk_BN`: collapsing via `mk_BN` preserves
the sptree size.  Untagged Flapjack infrastructure (HOL source outside
`cakeml/`). -/
@[simp] theorem sptSize_mkBN {α : Type} (left right : Spt α) :
    sptSize (sptMkBN left right) = sptSize left + sptSize right := by
  cases left <;> cases right <;> simp [sptMkBN, sptSize]

/-- HOL `loop_liveScript.sml:34-38 size_mk_BS`: collapsing via `mk_BS` preserves
the sptree size.  Untagged Flapjack infrastructure. -/
@[simp] theorem sptSize_mkBS {α : Type} (left : Spt α) (value : α) (right : Spt α) :
    sptSize (sptMkBS left value right) = sptSize left + sptSize right + 1 := by
  cases left <;> cases right <;> simp [sptMkBS, sptSize]

/-- HOL `loop_liveScript.sml:40-49 size_inter`: the intersection is no larger
than its left operand.  This is the measure lemma `fixedpoint` termination
needs.  Untagged Flapjack infrastructure. -/
theorem sptSize_inter_le {α β : Type} (left : Spt α) (right : Spt β) :
    sptSize (sptInter left right) <= sptSize left := by
  induction left generalizing right with
  | ln => simp [sptInter]
  | ls value => cases right <;> simp [sptInter]
  | bn first second ihFirst ihSecond =>
      cases right with
      | ln => simp [sptInter]
      | ls value => simp [sptInter]
      | bn f s =>
          simp only [sptInter, sptSize_bn, sptSize_mkBN]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
      | bs f value s =>
          simp only [sptInter, sptSize_bn, sptSize_mkBN]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
  | bs first value second ihFirst ihSecond =>
      cases right with
      | ln => simp [sptInter]
      | ls v => simp [sptInter]
      | bn f s =>
          simp only [sptInter, sptSize_bs, sptSize_mkBN]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
      | bs f v s =>
          simp only [sptInter, sptSize_bs, sptSize_mkBS]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega

/-- Rebuild an spt tree with the root value replaced by `v` (keying at index
`sptInsert 0`). This is the key-`0` insertion pattern of HOL sptree `insert`:
inserting key `0` writes at the root of whatever tree it is given. Flapjack
infrastructure used to reason about key-`0` insertions; there is no separate
HOL declaration for it. -/
def sptRootSet {α : Type} (v : α) : Spt α → Spt α
  | .ln => .ls v
  | .ls _ => .ls v
  | .bn left right => .bs left v right
  | .bs left _ right => .bs left v right

/-- Key-`0` insertion writes the root value: `sptInsert 0 v t = sptRootSet v t`.
This is the `key = 0` branch of the HOL sptree `insert` definition. -/
theorem sptInsert_zero {α : Type} (v : α) (t : Spt α) :
    sptInsert 0 v t = sptRootSet v t := by
  cases t <;> simp [sptInsert, sptRootSet]

/-- Inserting a nonzero key commutes with replacing the root value. This is the
tree-swap step of the HOL sptree `insert` recursion for the key-`0` layer;
Flapjack infrastructure with no separate HOL declaration. -/
theorem sptRootSet_insert {α : Type} (v d : α) (c : Nat) (t : Spt α) (hc : c ≠ 0) :
    sptRootSet v (sptInsert c d t) = sptInsert c d (sptRootSet v t) := by
  cases t with
  | ln =>
    by_cases hc2 : c % 2 = 0
    · conv => lhs; rw [sptInsert.eq_1, if_neg hc, if_pos hc2, sptRootSet.eq_3]
      rw [sptRootSet.eq_1, sptInsert.eq_2, if_neg hc, if_pos hc2]
    · conv => lhs; rw [sptInsert.eq_1, if_neg hc, if_neg hc2, sptRootSet.eq_3]
      rw [sptRootSet.eq_1, sptInsert.eq_2, if_neg hc, if_neg hc2]
  | ls existing =>
    by_cases hc2 : c % 2 = 0
    · conv => lhs; rw [sptInsert.eq_2, if_neg hc, if_pos hc2, sptRootSet.eq_4]
      rw [sptRootSet.eq_2, sptInsert.eq_2, if_neg hc, if_pos hc2]
    · conv => lhs; rw [sptInsert.eq_2, if_neg hc, if_neg hc2, sptRootSet.eq_4]
      rw [sptRootSet.eq_2, sptInsert.eq_2, if_neg hc, if_neg hc2]
  | bn left right =>
    by_cases hc2 : c % 2 = 0
    · conv => lhs; rw [sptInsert.eq_3, if_neg hc, if_pos hc2, sptRootSet.eq_3]
      rw [sptRootSet.eq_3, sptInsert.eq_4, if_neg hc, if_pos hc2]
    · conv => lhs; rw [sptInsert.eq_3, if_neg hc, if_neg hc2, sptRootSet.eq_3]
      rw [sptRootSet.eq_3, sptInsert.eq_4, if_neg hc, if_neg hc2]
  | bs left existing right =>
    by_cases hc2 : c % 2 = 0
    · conv => lhs; rw [sptInsert.eq_4, if_neg hc, if_pos hc2, sptRootSet.eq_4]
      rw [sptRootSet.eq_4, sptInsert.eq_4, if_neg hc, if_pos hc2]
    · conv => lhs; rw [sptInsert.eq_4, if_neg hc, if_neg hc2, sptRootSet.eq_4]
      rw [sptRootSet.eq_4, sptInsert.eq_4, if_neg hc, if_neg hc2]

/-- Exact port of HOL sptree `insert_shadow`
    (`HOL/src/finite_maps/sptreeScript.sml:1641`): re-inserting the same key
    keeps only the newest value. The HOL source lives in the HOL installation's
    `src/finite_maps`, outside `cakeml/`, so this rendering is Flapjack
    infrastructure and carries no `@[hol]` tag. -/
theorem sptInsert_insert_shadow {α : Type} (a : Nat) (b c : α) (tree : Spt α) :
    sptInsert a b (sptInsert a c tree) = sptInsert a b tree := by
  revert c tree
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro c tree
    by_cases h0 : a = 0
    · subst h0
      cases tree <;> simp [sptInsert]
    · have ha : 0 < a := Nat.pos_of_ne_zero h0
      have hk : (a - 1) / 2 < a := by
        have hle : (a - 1) / 2 ≤ a - 1 := Nat.div_le_self _ _
        have hlt : a - 1 < a := Nat.sub_lt ha (by decide)
        omega
      by_cases h2 : a % 2 = 0
      · cases tree with
        | ln =>
            conv => rhs; rw [sptInsert.eq_1, if_neg h0, if_pos h2]
            rw [sptInsert.eq_1, if_neg h0, if_pos h2, sptInsert.eq_3, if_neg h0, if_pos h2,
              ih ((a - 1) / 2) hk c .ln]
        | ls existing =>
            conv => rhs; rw [sptInsert.eq_2, if_neg h0, if_pos h2]
            rw [sptInsert.eq_2, if_neg h0, if_pos h2,
              sptInsert.eq_4, if_neg h0, if_pos h2, ih ((a - 1) / 2) hk c .ln]
        | bn left right =>
            conv => rhs; rw [sptInsert.eq_3, if_neg h0, if_pos h2]
            rw [sptInsert.eq_3, if_neg h0, if_pos h2,
              sptInsert.eq_3, if_neg h0, if_pos h2, ih ((a - 1) / 2) hk c left]
        | bs left existing right =>
            conv => rhs; rw [sptInsert.eq_4, if_neg h0, if_pos h2]
            rw [sptInsert.eq_4, if_neg h0, if_pos h2,
              sptInsert.eq_4, if_neg h0, if_pos h2, ih ((a - 1) / 2) hk c left]
      · cases tree with
        | ln =>
            conv => rhs; rw [sptInsert.eq_1, if_neg h0, if_neg h2]
            rw [sptInsert.eq_1, if_neg h0, if_neg h2, sptInsert.eq_3, if_neg h0, if_neg h2,
              ih ((a - 1) / 2) hk c .ln]
        | ls existing =>
            conv => rhs; rw [sptInsert.eq_2, if_neg h0, if_neg h2]
            rw [sptInsert.eq_2, if_neg h0, if_neg h2,
              sptInsert.eq_4, if_neg h0, if_neg h2, ih ((a - 1) / 2) hk c .ln]
        | bn left right =>
            conv => rhs; rw [sptInsert.eq_3, if_neg h0, if_neg h2]
            rw [sptInsert.eq_3, if_neg h0, if_neg h2,
              sptInsert.eq_3, if_neg h0, if_neg h2, ih ((a - 1) / 2) hk c right]
        | bs left existing right =>
            conv => rhs; rw [sptInsert.eq_4, if_neg h0, if_neg h2]
            rw [sptInsert.eq_4, if_neg h0, if_neg h2,
              sptInsert.eq_4, if_neg h0, if_neg h2, ih ((a - 1) / 2) hk c right]

/-- Exact port of HOL sptree `insert_swap`
    (`HOL/src/finite_maps/sptreeScript.sml:2214`): inserting distinct keys in
    either order gives the same tree. The HOL source lives in the HOL
    installation's `src/finite_maps`, outside `cakeml/`, so this rendering is
    Flapjack infrastructure and carries no `@[hol]` tag. -/
theorem sptInsert_swap {α : Type} :
    ∀ (a c : Nat) (b d : α) (t : Spt α), a ≠ c →
      sptInsert a b (sptInsert c d t) = sptInsert c d (sptInsert a b t) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a iha =>
    intro c b d t h
    by_cases ha0 : a = 0
    · subst ha0
      have hc0 : c ≠ 0 := fun hc => h hc.symm
      simp only [sptInsert_zero]
      exact sptRootSet_insert b d c t hc0
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hka : (a - 1) / 2 < a := by
        have h1 : (a - 1) / 2 ≤ a - 1 := Nat.div_le_self _ _
        have h2 : a - 1 < a := Nat.sub_lt hapos (by decide)
        omega
      by_cases hc0 : c = 0
      · subst hc0
        simp only [sptInsert_zero]
        exact (sptRootSet_insert d b a t ha0).symm
      · have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
        by_cases hpar : a % 2 = c % 2
        · have hne : (a - 1) / 2 ≠ (c - 1) / 2 := by
            intro hcontra
            exact h (by omega)
          by_cases ha2 : a % 2 = 0
          · have hc2 : c % 2 = 0 := by omega
            cases t with
            | ln =>
              conv => rhs; rw [sptInsert.eq_1, if_neg ha0, if_pos ha2, sptInsert.eq_3, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_1, if_neg hc0, if_pos hc2, sptInsert.eq_3, if_neg ha0, if_pos ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d .ln hne]
            | ls existing =>
              conv => rhs; rw [sptInsert.eq_2, if_neg ha0, if_pos ha2, sptInsert.eq_4, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_2, if_neg hc0, if_pos hc2, sptInsert.eq_4, if_neg ha0, if_pos ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d .ln hne]
            | bn left right =>
              conv => rhs; rw [sptInsert.eq_3, if_neg ha0, if_pos ha2, sptInsert.eq_3, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_3, if_neg hc0, if_pos hc2, sptInsert.eq_3, if_neg ha0, if_pos ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d left hne]
            | bs left existing right =>
              conv => rhs; rw [sptInsert.eq_4, if_neg ha0, if_pos ha2, sptInsert.eq_4, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_4, if_neg hc0, if_pos hc2, sptInsert.eq_4, if_neg ha0, if_pos ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d left hne]
          · have hc2 : ¬ c % 2 = 0 := by omega
            cases t with
            | ln =>
              conv => rhs; rw [sptInsert.eq_1, if_neg ha0, if_neg ha2, sptInsert.eq_3, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_1, if_neg hc0, if_neg hc2, sptInsert.eq_3, if_neg ha0, if_neg ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d .ln hne]
            | ls existing =>
              conv => rhs; rw [sptInsert.eq_2, if_neg ha0, if_neg ha2, sptInsert.eq_4, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_2, if_neg hc0, if_neg hc2, sptInsert.eq_4, if_neg ha0, if_neg ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d .ln hne]
            | bn left right =>
              conv => rhs; rw [sptInsert.eq_3, if_neg ha0, if_neg ha2, sptInsert.eq_3, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_3, if_neg hc0, if_neg hc2, sptInsert.eq_3, if_neg ha0, if_neg ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d right hne]
            | bs left existing right =>
              conv => rhs; rw [sptInsert.eq_4, if_neg ha0, if_neg ha2, sptInsert.eq_4, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_4, if_neg hc0, if_neg hc2, sptInsert.eq_4, if_neg ha0, if_neg ha2,
                iha ((a - 1) / 2) hka ((c - 1) / 2) b d right hne]
        · by_cases ha2 : a % 2 = 0
          · have hc2 : ¬ c % 2 = 0 := by omega
            cases t with
            | ln =>
              conv => rhs; rw [sptInsert.eq_1, if_neg ha0, if_pos ha2, sptInsert.eq_3, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_1, if_neg hc0, if_neg hc2, sptInsert.eq_3, if_neg ha0, if_pos ha2]
            | ls existing =>
              conv => rhs; rw [sptInsert.eq_2, if_neg ha0, if_pos ha2, sptInsert.eq_4, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_2, if_neg hc0, if_neg hc2, sptInsert.eq_4, if_neg ha0, if_pos ha2]
            | bn left right =>
              conv => rhs; rw [sptInsert.eq_3, if_neg ha0, if_pos ha2, sptInsert.eq_3, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_3, if_neg hc0, if_neg hc2, sptInsert.eq_3, if_neg ha0, if_pos ha2]
            | bs left existing right =>
              conv => rhs; rw [sptInsert.eq_4, if_neg ha0, if_pos ha2, sptInsert.eq_4, if_neg hc0, if_neg hc2]
              rw [sptInsert.eq_4, if_neg hc0, if_neg hc2, sptInsert.eq_4, if_neg ha0, if_pos ha2]
          · have hc2 : c % 2 = 0 := by omega
            cases t with
            | ln =>
              conv => rhs; rw [sptInsert.eq_1, if_neg ha0, if_neg ha2, sptInsert.eq_3, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_1, if_neg hc0, if_pos hc2, sptInsert.eq_3, if_neg ha0, if_neg ha2]
            | ls existing =>
              conv => rhs; rw [sptInsert.eq_2, if_neg ha0, if_neg ha2, sptInsert.eq_4, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_2, if_neg hc0, if_pos hc2, sptInsert.eq_4, if_neg ha0, if_neg ha2]
            | bn left right =>
              conv => rhs; rw [sptInsert.eq_3, if_neg ha0, if_neg ha2, sptInsert.eq_3, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_3, if_neg hc0, if_pos hc2, sptInsert.eq_3, if_neg ha0, if_neg ha2]
            | bs left existing right =>
              conv => rhs; rw [sptInsert.eq_4, if_neg ha0, if_neg ha2, sptInsert.eq_4, if_neg hc0, if_pos hc2]
              rw [sptInsert.eq_4, if_neg hc0, if_pos hc2, sptInsert.eq_4, if_neg ha0, if_neg ha2]

/-! ## HOL `fromAList` rendering

The `fromAList` definition is in HOL's external standard-library
`HOL/src/finite_maps/sptreeScript.sml`, not in the CakeML submodule. Its Lean
rendering below is therefore Flapjack infrastructure without an `@[hol]` tag.
The CakeML theorem `mem_lookup_fromalist_some` is ported in the
`Flapjack.Pancake.CrepToLoop.StateRel` proof counterpart. -/

/-- Flapjack rendering of HOL `sptree$fromAList`: each head association is
inserted over the tree built from the tail, matching the external HOL
standard-library definition. -/
def sptFromAList {α : Type} : List (Nat × α) → Spt α
  | [] => .ln
  | (key, value) :: entries => sptInsert key value (sptFromAList entries)

end Flapjack
