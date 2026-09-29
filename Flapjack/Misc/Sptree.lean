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

/-! ## HOL `domain` membership

HOL `sptree$domain` (`HOL/src/finite_maps/sptreeScript.sml:473`) and its
membership characterisation `domain_lookup` (`:620`,
`k IN domain t <=> ?v. lookup k t = SOME v`) live in the HOL standard library
outside the `cakeml/` submodule, so the rendering below is untagged Flapjack
infrastructure.  HOL sets are rendered as predicates, matching the
`memaddrs`/`sh_memaddrs` rendering: `sptDomain t` is the predicate
`fun key => (lookup key t).isSome`, so `k IN domain t` is `sptMem k t` and
`domain t1 SUBSET domain t2` is `forall k, sptMem k t1 -> sptMem k t2`. -/

/-- Predicate rendering of HOL `domain` on the exact spt carrier. -/
def sptDomain {α : Type} (tree : Spt α) : Nat → Prop :=
  fun key => (sptLookup key tree).isSome

/-- HOL `k IN domain t`, i.e. `sptDomain t k`. -/
def sptMem {α : Type} (key : Nat) (tree : Spt α) : Prop :=
  sptDomain tree key

/-- Exact port of HOL sptree `domain_lookup`
(`HOL/src/finite_maps/sptreeScript.sml:620`): `k IN domain t` holds iff
`lookup k t` returns some value.  The proof is constructor-independent
(`Option.isSome` decomposes as an existential for every tree), so it covers all
four spt constructors.  Untagged Flapjack infrastructure (source outside
`cakeml/`). -/
theorem sptMem_iff_lookup {α : Type} (key : Nat) (tree : Spt α) :
    sptMem key tree ↔ ∃ v, sptLookup key tree = some v := by
  unfold sptMem sptDomain
  exact Option.isSome_iff_exists

/-- No key is a member of the empty tree. -/
@[simp] theorem sptMem_ln {α : Type} (key : Nat) :
    ¬ sptMem key (.ln : Spt α) := by
  unfold sptMem sptDomain
  simp [sptLookup]

/-- The single-leaf tree has exactly key `0` in its domain. -/
@[simp] theorem sptMem_ls {α : Type} (key : Nat) (value : α) :
    sptMem key (.ls value : Spt α) ↔ key = 0 := by
  unfold sptMem sptDomain
  by_cases h : key = 0
  · simp [sptLookup, h]
  · simp [sptLookup, h]

/-- `domain_def` clause for `BN`
(`HOL/src/finite_maps/sptreeScript.sml:473`):
`domain (BN t1 t2) = IMAGE (fun n => 2 * n + 2) (domain t1) UNION
IMAGE (fun n => 2 * n + 1) (domain t2)`, rendered as membership.  Untagged
Flapjack infrastructure (source outside `cakeml/`). -/
theorem sptMem_bn {α : Type} (left right : Spt α) (key : Nat) :
    sptMem key (.bn left right) ↔
      (∃ m, sptMem m left ∧ key = 2 * m + 2) ∨
        (∃ m, sptMem m right ∧ key = 2 * m + 1) := by
  unfold sptMem sptDomain
  by_cases h0 : key = 0
  · subst h0
    simp only [sptLookup]
    simp
  · by_cases h2 : key % 2 = 0
    · simp only [sptLookup, if_neg h0, if_pos h2]
      constructor
      · intro h
        left
        exact ⟨(key - 1) / 2, by simpa using h, by omega⟩
      · rintro (⟨m, hm, hmk⟩ | ⟨m, hm, hmk⟩)
        · have : m = (key - 1) / 2 := by omega
          subst this; simpa using hm
        · omega
    · simp only [sptLookup, if_neg h0, if_neg h2]
      constructor
      · intro h
        right
        exact ⟨(key - 1) / 2, by simpa using h, by omega⟩
      · rintro (⟨m, hm, hmk⟩ | ⟨m, hm, hmk⟩)
        · omega
        · have : m = (key - 1) / 2 := by omega
          subst this; simpa using hm

/-- `domain_def` clause for `BS`
(`HOL/src/finite_maps/sptreeScript.sml:473`):
`domain (BS t1 _ t2) = {0} UNION IMAGE (fun n => 2 * n + 2) (domain t1) UNION
IMAGE (fun n => 2 * n + 1) (domain t2)`, rendered as membership.  Untagged
Flapjack infrastructure (source outside `cakeml/`). -/
theorem sptMem_bs {α : Type} (left : Spt α) (value : α) (right : Spt α) (key : Nat) :
    sptMem key (.bs left value right) ↔
      key = 0 ∨ (∃ m, sptMem m left ∧ key = 2 * m + 2) ∨
        (∃ m, sptMem m right ∧ key = 2 * m + 1) := by
  unfold sptMem sptDomain
  by_cases h0 : key = 0
  · subst h0
    simp only [sptLookup]
    simp
  · by_cases h2 : key % 2 = 0
    · simp only [sptLookup, if_neg h0, if_pos h2]
      constructor
      · intro h
        right; left
        exact ⟨(key - 1) / 2, by simpa using h, by omega⟩
      · rintro (h | ⟨m, hm, hmk⟩ | ⟨m, hm, hmk⟩)
        · omega
        · have : m = (key - 1) / 2 := by omega
          subst this; simpa using hm
        · omega
    · simp only [sptLookup, if_neg h0, if_neg h2]
      constructor
      · intro h
        right; right
        exact ⟨(key - 1) / 2, by simpa using h, by omega⟩
      · rintro (h | ⟨m, hm, hmk⟩ | ⟨m, hm, hmk⟩)
        · omega
        · omega
        · have : m = (key - 1) / 2 := by omega
          subst this; simpa using hm

/-- Predicate rendering of HOL sptree `subspt`
(`HOL/src/finite_maps/sptreeScript.sml:1737-1741`,
`subspt sp1 sp2 <=> !k. k IN domain sp1 ==> k IN domain sp2 /\
lookup k sp2 = lookup k sp1`). The HOL source lives in the HOL installation's
`src/finite_maps`, outside `cakeml/`, so this rendering is untagged Flapjack
infrastructure; it reuses the `sptMem` rendering of `domain`/`IN`. -/
def sptSubspt {α : Type} (sp1 sp2 : Spt α) : Prop :=
  ∀ k, sptMem k sp1 → sptMem k sp2 ∧ sptLookup k sp2 = sptLookup k sp1

/-- Same-key lookup after insertion, proved by strong induction on the HOL
binary-tree key recursion. -/
theorem sptLookup_sptInsert_same {α : Type} :
    ∀ (key : Nat) (value : α) (tree : Spt α),
      sptLookup key (sptInsert key value tree) = some value := by
  intro key
  induction key using Nat.strongRecOn with
  | ind key ih =>
      intro value tree
      by_cases hzero : key = 0
      · subst key
        exact sptLookup_sptInsert_zero value tree
      · have hpositive : 0 < key := Nat.pos_of_ne_zero hzero
        have hdecrease : (key - 1) / 2 < key := by
          have hdiv : (key - 1) / 2 ≤ key - 1 := Nat.div_le_self _ _
          have hlt : key - 1 < key := Nat.sub_lt hpositive (by decide)
          omega
        by_cases heven : key % 2 = 0
        · cases tree with
          | ln =>
              conv => lhs; rw [sptInsert.eq_1, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | ls existing =>
              conv => lhs; rw [sptInsert.eq_2, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | bn left right =>
              conv => lhs; rw [sptInsert.eq_3, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value left
          | bs left existing right =>
              conv => lhs; rw [sptInsert.eq_4, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value left
        · cases tree with
          | ln =>
              conv => lhs; rw [sptInsert.eq_1, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | ls existing =>
              conv => lhs; rw [sptInsert.eq_2, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | bn left right =>
              conv => lhs; rw [sptInsert.eq_3, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value right
          | bs left existing right =>
              conv => lhs; rw [sptInsert.eq_4, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value right

private theorem div2_pred_ne {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hm : a % 2 = b % 2) (hne : a ≠ b) : (a - 1) / 2 ≠ (b - 1) / 2 := by
  intro h
  exact hne (by omega)

theorem sptLookup_sptInsert_ne {α : Type} :
    ∀ (other : Nat) (key : Nat) (value : α) (tree : Spt α),
      key ≠ other → sptLookup key (sptInsert other value tree) = sptLookup key tree := by
  intro other
  induction other using Nat.strongRecOn with
  | ind other ih =>
    intro key value tree hne
    by_cases h0 : other = 0
    · subst h0
      cases tree <;> simp [sptInsert, sptLookup, hne]
    · have hpos : 0 < other := Nat.pos_of_ne_zero h0
      have hdec : (other - 1) / 2 < other := by
        have h1 : (other - 1) / 2 ≤ other - 1 := Nat.div_le_self _ _
        have h2 : other - 1 < other := Nat.sub_lt hpos (by decide)
        omega
      by_cases h2 : other % 2 = 0
      · cases tree with
        | ln =>
          conv => lhs; rw [sptInsert.eq_1, if_neg h0, if_pos h2]
          conv => rhs; rw [sptLookup.eq_1]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_3, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_3, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value (.ln : Spt α)
                (div2_pred_ne (by omega) hpos (by omega) hne)]
              simp only [sptLookup.eq_1]
            · conv => lhs; rw [if_neg hkk]
              simp only [sptLookup.eq_1]
        | ls e =>
          conv => lhs; rw [sptInsert.eq_2, if_neg h0, if_pos h2]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_4, if_pos hk]
            conv => rhs; rw [sptLookup.eq_2, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_4, if_neg hk]
            conv => rhs; rw [sptLookup.eq_2, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value (.ln : Spt α)
                (div2_pred_ne (by omega) hpos (by omega) hne)]
              simp only [sptLookup.eq_1]
            · conv => lhs; rw [if_neg hkk]
              simp only [sptLookup.eq_1]
        | bn l r =>
          conv => lhs; rw [sptInsert.eq_3, if_neg h0, if_pos h2]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_3, if_pos hk]
            conv => rhs; rw [sptLookup.eq_3, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_3, if_neg hk]
            conv => rhs; rw [sptLookup.eq_3, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              conv => rhs; rw [if_pos hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value l
                (div2_pred_ne (by omega) hpos (by omega) hne)]
            · conv => lhs; rw [if_neg hkk]
              conv => rhs; rw [if_neg hkk]
        | bs l e r =>
          conv => lhs; rw [sptInsert.eq_4, if_neg h0, if_pos h2]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_4, if_pos hk]
            conv => rhs; rw [sptLookup.eq_4, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_4, if_neg hk]
            conv => rhs; rw [sptLookup.eq_4, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              conv => rhs; rw [if_pos hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value l
                (div2_pred_ne (by omega) hpos (by omega) hne)]
            · conv => lhs; rw [if_neg hkk]
              conv => rhs; rw [if_neg hkk]
      · cases tree with
        | ln =>
          conv => lhs; rw [sptInsert.eq_1, if_neg h0, if_neg h2]
          conv => rhs; rw [sptLookup.eq_1]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_3, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_3, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              simp only [sptLookup.eq_1]
            · conv => lhs; rw [if_neg hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value (.ln : Spt α)
                (div2_pred_ne (by omega) hpos (by omega) hne)]
              simp only [sptLookup.eq_1]
        | ls e =>
          conv => lhs; rw [sptInsert.eq_2, if_neg h0, if_neg h2]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_4, if_pos hk]
            conv => rhs; rw [sptLookup.eq_2, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_4, if_neg hk]
            conv => rhs; rw [sptLookup.eq_2, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              simp only [sptLookup.eq_1]
            · conv => lhs; rw [if_neg hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value (.ln : Spt α)
                (div2_pred_ne (by omega) hpos (by omega) hne)]
              simp only [sptLookup.eq_1]
        | bn l r =>
          conv => lhs; rw [sptInsert.eq_3, if_neg h0, if_neg h2]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_3, if_pos hk]
            conv => rhs; rw [sptLookup.eq_3, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_3, if_neg hk]
            conv => rhs; rw [sptLookup.eq_3, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              conv => rhs; rw [if_pos hkk]
            · conv => lhs; rw [if_neg hkk]
              conv => rhs; rw [if_neg hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value r
                (div2_pred_ne (by omega) hpos (by omega) hne)]
        | bs l e r =>
          conv => lhs; rw [sptInsert.eq_4, if_neg h0, if_neg h2]
          by_cases hk : key = 0
          · conv => lhs; rw [sptLookup.eq_4, if_pos hk]
            conv => rhs; rw [sptLookup.eq_4, if_pos hk]
          · conv => lhs; rw [sptLookup.eq_4, if_neg hk]
            conv => rhs; rw [sptLookup.eq_4, if_neg hk]
            by_cases hkk : key % 2 = 0
            · conv => lhs; rw [if_pos hkk]
              conv => rhs; rw [if_pos hkk]
            · conv => lhs; rw [if_neg hkk]
              conv => rhs; rw [if_neg hkk]
              rw [ih ((other - 1) / 2) hdec ((key - 1) / 2) value r
                (div2_pred_ne (by omega) hpos (by omega) hne)]


/-- Membership after insertion: the inserted key joins the tree, all others are
unchanged.  Exact `sptree$lookup`/`sptree$` domain content behind the HOL
`lookup_insert` fact used by `locals_rel_insert_gt_vmax`. -/
theorem sptMem_sptInsert {α : Type} (key other : Nat) (value : α) (tree : Spt α) :
    sptMem key (sptInsert other value tree) ↔ key = other ∨ sptMem key tree := by
  constructor
  · intro h
    rw [sptMem_iff_lookup] at h
    obtain ⟨found, hfound⟩ := h
    by_cases hk : key = other
    · exact Or.inl hk
    · exact Or.inr (by
        rw [sptMem_iff_lookup]
        exact ⟨found, by rw [sptLookup_sptInsert_ne other key value tree hk] at hfound; exact hfound⟩)
  · intro h
    rw [sptMem_iff_lookup]
    rcases h with hk | hmem
    · subst hk
      exact ⟨value, sptLookup_sptInsert_same key value tree⟩
    · rw [sptMem_iff_lookup] at hmem
      obtain ⟨found, hfound⟩ := hmem
      by_cases hk : key = other
      · exact ⟨value, by rw [hk]; exact sptLookup_sptInsert_same other value tree⟩
      · exact ⟨found, by rw [sptLookup_sptInsert_ne other key value tree hk]; exact hfound⟩

/-- HOL `lrnext`: the increment used when placing subtrees in the spt index
space (`HOL/src/finite_maps/sptreeScript.sml:421-422`). -/
def lrNext : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * lrNext (n / 2)

/-! The `foldi` traversal in HOL's `toAList` relies on these two adjacent
`lrNext` identities (`lrlemma1` and `lrlemma2` in
`HOL/src/finite_maps/sptreeScript.sml`).  They are untagged infrastructure
because the source is the external HOL standard library, not CakeML. -/

theorem lrNext_offset_one (index : Nat) :
    lrNext (index + lrNext index) = 2 * lrNext index := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
      by_cases hzero : index = 0
      · subst index
        simp [lrNext]
      · rcases Nat.mod_two_eq_zero_or_one index with heven | hodd
        · let half := index / 2 - 1
          have hindex : index = 2 * half + 2 := by omega
          have hlt : half < index := by omega
          have hquot : (2 * half + 1) / 2 = half := by omega
          have hinc : lrNext (2 * half + 2) = 2 * lrNext half := by
            simp only [lrNext]
            rw [hquot]
          rw [hindex, hinc]
          have hsum : 2 * half + 2 + 2 * lrNext half =
              2 * (half + lrNext half) + 2 := by omega
          rw [hsum]
          have hstep : lrNext (2 * (half + lrNext half) + 2) =
              2 * lrNext (half + lrNext half) := by
            have hdiv : (2 * (half + lrNext half) + 1) / 2 =
                half + lrNext half := by omega
            simp only [lrNext]
            rw [hdiv]
          rw [hstep, ih half hlt]
        · let half := index / 2
          have hindex : index = 2 * half + 1 := by omega
          have hlt : half < index := by omega
          have hquot : (2 * half) / 2 = half := by omega
          have hinc : lrNext (2 * half + 1) = 2 * lrNext half := by
            simp only [lrNext]
            rw [hquot]
          rw [hindex, hinc]
          have hsum : 2 * half + 1 + 2 * lrNext half =
              2 * (half + lrNext half) + 1 := by omega
          rw [hsum]
          have hstep : lrNext (2 * (half + lrNext half) + 1) =
              2 * lrNext (half + lrNext half) := by
            have hdiv : (2 * (half + lrNext half)) / 2 =
                half + lrNext half := by omega
            simp only [lrNext]
            rw [hdiv]
          rw [hstep, ih half hlt]

theorem lrNext_offset_two (index : Nat) :
    lrNext (index + 2 * lrNext index) = 2 * lrNext index := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
      by_cases hzero : index = 0
      · subst index
        simp [lrNext]
      · rcases Nat.mod_two_eq_zero_or_one index with heven | hodd
        · let half := index / 2 - 1
          have hindex : index = 2 * half + 2 := by omega
          have hlt : half < index := by omega
          have hquot : (2 * half + 1) / 2 = half := by omega
          have hinc : lrNext (2 * half + 2) = 2 * lrNext half := by
            simp only [lrNext]
            rw [hquot]
          rw [hindex, hinc]
          have hdouble : 2 * (2 * lrNext half) = 4 * lrNext half := by omega
          rw [hdouble]
          have hsum : 2 * half + 2 + 4 * lrNext half =
              2 * (half + 2 * lrNext half) + 2 := by omega
          rw [hsum]
          have hstep : lrNext (2 * (half + 2 * lrNext half) + 2) =
              2 * lrNext (half + 2 * lrNext half) := by
            have hdiv : (2 * (half + 2 * lrNext half) + 1) / 2 =
                half + 2 * lrNext half := by omega
            simp only [lrNext]
            rw [hdiv]
          rw [hstep, ih half hlt]
          omega
        · let half := index / 2
          have hindex : index = 2 * half + 1 := by omega
          have hlt : half < index := by omega
          have hquot : (2 * half) / 2 = half := by omega
          have hinc : lrNext (2 * half + 1) = 2 * lrNext half := by
            simp only [lrNext]
            rw [hquot]
          rw [hindex, hinc]
          have hdouble : 2 * (2 * lrNext half) = 4 * lrNext half := by omega
          rw [hdouble]
          have hsum : 2 * half + 1 + 4 * lrNext half =
              2 * (half + 2 * lrNext half) + 1 := by omega
          rw [hsum]
          have hstep : lrNext (2 * (half + 2 * lrNext half) + 1) =
              2 * lrNext (half + 2 * lrNext half) := by
            have hdiv : (2 * (half + 2 * lrNext half)) / 2 =
                half + 2 * lrNext half := by omega
            simp only [lrNext]
            rw [hdiv]
          rw [hstep, ih half hlt]
          omega

/-- HOL `sptree$spt_acc` (`HOL/src/finite_maps/sptreeScript.sml:750-755`):
the key at local index `key` when a subtree is rooted at `index`. This is
external HOL-library support and is intentionally untagged. -/
def sptAcc (index : Nat) : Nat → Nat
  | 0 => index
  | key + 1 =>
      sptAcc (index + if (key + 1) % 2 = 0 then 2 * lrNext index else lrNext index)
        (key / 2)
termination_by key => key
decreasing_by omega

/-- HOL `spt_acc` computes the affine key `index + lrnext index * key`; this
is the arithmetic bridge between `foldi`'s threaded indices and `lookup`'s
binary key recursion. -/
theorem sptAcc_eq (index key : Nat) :
    sptAcc index key = index + lrNext index * key := by
  revert index
  induction key using Nat.strongRecOn with
  | ind key ih =>
      cases key with
      | zero => intro index; simp [sptAcc]
      | succ key =>
          intro index
          rw [sptAcc]
          by_cases heven : (key + 1) % 2 = 0
          · rw [if_pos heven]
            have hlt : key / 2 < key + 1 := by omega
            have hkey : key + 1 = 2 * (key / 2) + 2 := by omega
            have hchild := ih (key / 2) hlt (index + 2 * lrNext index)
            rw [lrNext_offset_two index] at hchild
            rw [hchild]
            rw [hkey]
            have hmul : (2 * lrNext index) * (key / 2) =
                lrNext index * (2 * (key / 2)) := by
              simp [Nat.mul_comm, Nat.mul_left_comm]
            rw [hmul, Nat.mul_add]
            omega
          · rw [if_neg heven]
            have hlt : key / 2 < key + 1 := by omega
            have hkey : key + 1 = 2 * (key / 2) + 1 := by omega
            have hchild := ih (key / 2) hlt (index + lrNext index)
            rw [lrNext_offset_one index] at hchild
            rw [hchild]
            rw [hkey]
            have hmul : (2 * lrNext index) * (key / 2) =
                lrNext index * (2 * (key / 2)) := by
              simp [Nat.mul_comm, Nat.mul_left_comm]
            rw [hmul, Nat.mul_add, Nat.mul_one]
            omega

/-- `lrNext` is always positive, so the affine address assigned to a local
index by `sptAcc` is injective. This is the key uniqueness fact needed when
foldi's mixed traversal order is related back to `lookup` keys. -/
theorem lrNext_pos (index : Nat) : 0 < lrNext index := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
      cases index with
      | zero => simp [lrNext]
      | succ index =>
          have hlt : index / 2 < index + 1 := by omega
          simp only [lrNext]
          exact Nat.mul_pos (by omega) (ih (index / 2) hlt)

/-- Distinct local keys have distinct absolute indices under `sptAcc`. -/
theorem sptAcc_injective (index : Nat) : Function.Injective (sptAcc index) := by
  intro left right h
  rw [sptAcc_eq, sptAcc_eq] at h
  have hmul : lrNext index * left = lrNext index * right := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left (lrNext_pos index) hmul

/-- Child offsets produced by `foldi` agree with `sptAcc`'s parent-key
encoding. -/
theorem sptAcc_childLeft (index key : Nat) :
    sptAcc (index + 2 * lrNext index) key = sptAcc index (2 * key + 2) := by
  rw [sptAcc_eq, sptAcc_eq, lrNext_offset_two]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (lrNext index) 2]
  omega

/-- Right-child counterpart of `sptAcc_childLeft`. -/
theorem sptAcc_childRight (index key : Nat) :
    sptAcc (index + lrNext index) key = sptAcc index (2 * key + 1) := by
  rw [sptAcc_eq, sptAcc_eq, lrNext_offset_one]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (lrNext index) 2]
  omega

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

/-- Every association emitted by `foldi` is either part of its initial
accumulator or is keyed by the affine address assigned to some local index.
This is the support half of the unrestricted `toAList`/`lookup` bridge; it
does not assume that the Spt tree is well formed. -/
theorem sptFoldi_mem_address {α : Type} (tree : Spt α) :
    ∀ (index : Nat) (accumulator : List (Nat × α)) (key : Nat) (value : α),
      (key, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries) index accumulator tree →
        (key, value) ∈ accumulator ∨
          ∃ localKey, key = sptAcc index localKey ∧
            sptLookup localKey tree = some value := by
  induction tree with
  | ln =>
      intro index accumulator key value hmem
      exact Or.inl hmem
  | ls stored =>
      intro index accumulator key value hmem
      simp only [sptFoldi, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · right
        injection hhead with hkey _
        subst key
        subst value
        exact ⟨0, by simp [sptAcc], by simp [sptLookup]⟩
      · exact Or.inl htail
  | bn left right ihLeft ihRight =>
      intro index accumulator key value hmem
      change (key, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries)
            (index + lrNext index)
            (sptFoldi (fun k v entries => (k, v) :: entries)
              (index + 2 * lrNext index) accumulator left) right at hmem
      rcases ihRight _ _ _ _ hmem with hacc | ⟨rightKey, hkey, hlookup⟩
      · rcases ihLeft _ _ _ _ hacc with hacc | ⟨leftKey, hkey, hlookup⟩
        · exact Or.inl hacc
        · right
          refine ⟨2 * leftKey + 2, ?_⟩
          constructor
          · rw [← sptAcc_childLeft]
            exact hkey
          · have hzero : 2 * leftKey + 2 ≠ 0 := by omega
            have hparity : (2 * leftKey + 2) % 2 = 0 := by omega
            have hdiv : (2 * leftKey + 1) / 2 = leftKey := by omega
            simpa [sptLookup, hzero, hparity, hdiv] using hlookup
      · right
        refine ⟨2 * rightKey + 1, ?_⟩
        constructor
        · rw [← sptAcc_childRight]
          exact hkey
        · have hzero : 2 * rightKey + 1 ≠ 0 := by omega
          have hparity : (2 * rightKey + 1) % 2 = 1 := by omega
          have hdiv : (2 * rightKey + 1 - 1) / 2 = rightKey := by omega
          simpa [sptLookup, hzero, hparity, hdiv] using hlookup
  | bs left stored right ihLeft ihRight =>
      intro index accumulator key value hmem
      change (key, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries)
            (index + lrNext index)
            ((index, stored) ::
              sptFoldi (fun k v entries => (k, v) :: entries)
                (index + 2 * lrNext index) accumulator left) right at hmem
      rcases ihRight _ _ _ _ hmem with hacc | ⟨rightKey, hkey, hlookup⟩
      · simp only [List.mem_cons] at hacc
        rcases hacc with hroot | hleft
        · right
          injection hroot with hkey _
          subst key
          subst value
          refine ⟨0, by simp [sptAcc], ?_⟩
          simp [sptLookup]
        · rcases ihLeft _ _ _ _ hleft with hacc | ⟨leftKey, hkey, hlookup⟩
          · exact Or.inl hacc
          · right
            refine ⟨2 * leftKey + 2, ?_⟩
            constructor
            · rw [← sptAcc_childLeft]
              exact hkey
            · have hzero : 2 * leftKey + 2 ≠ 0 := by omega
              have hparity : (2 * leftKey + 2) % 2 = 0 := by omega
              have hdiv : (2 * leftKey + 1) / 2 = leftKey := by omega
              simpa [sptLookup, hzero, hparity, hdiv] using hlookup
      · right
        refine ⟨2 * rightKey + 1, ?_⟩
        constructor
        · rw [← sptAcc_childRight]
          exact hkey
        · have hzero : 2 * rightKey + 1 ≠ 0 := by omega
          have hparity : (2 * rightKey + 1) % 2 = 1 := by omega
          have hdiv : (2 * rightKey + 1) / 2 = rightKey := by omega
          simpa [sptLookup, hzero, hparity, hdiv] using hlookup

/-- `foldi` preserves every entry supplied in its initial accumulator. -/
theorem sptFoldi_mem_acc {α : Type} (tree : Spt α) :
    ∀ (index : Nat) (accumulator : List (Nat × α)) (entry : Nat × α),
      entry ∈ accumulator →
        entry ∈ sptFoldi (fun k v entries => (k, v) :: entries) index accumulator tree := by
  induction tree with
  | ln =>
      intro index accumulator entry hmem
      simpa [sptFoldi] using hmem
  | ls stored =>
      intro index accumulator entry hmem
      simp only [sptFoldi, List.mem_cons]
      exact Or.inr hmem
  | bn left right ihLeft ihRight =>
      intro index accumulator entry hmem
      change entry ∈
        sptFoldi (fun k v entries => (k, v) :: entries)
          (index + lrNext index)
          (sptFoldi (fun k v entries => (k, v) :: entries)
            (index + 2 * lrNext index) accumulator left) right
      exact ihRight _ _ entry (ihLeft _ _ entry hmem)
  | bs left stored right ihLeft ihRight =>
      intro index accumulator entry hmem
      change entry ∈
        sptFoldi (fun k v entries => (k, v) :: entries)
          (index + lrNext index)
          ((index, stored) ::
            sptFoldi (fun k v entries => (k, v) :: entries)
              (index + 2 * lrNext index) accumulator left) right
      apply ihRight
      simp only [List.mem_cons]
      exact Or.inr (ihLeft _ _ entry hmem)

/-- Every successful lookup in a subtree is emitted by its corresponding
`foldi` traversal. Together with `sptFoldi_mem_address`, this characterizes
the traversal's entries without any well-formedness premise. -/
theorem sptFoldi_lookup_mem {α : Type} (tree : Spt α) :
    ∀ (index : Nat) (accumulator : List (Nat × α)) (localKey : Nat) (value : α),
      sptLookup localKey tree = some value →
        (sptAcc index localKey, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries) index accumulator tree := by
  induction tree with
  | ln =>
      intro index accumulator localKey value hlookup
      simp [sptLookup] at hlookup
  | ls stored =>
      intro index accumulator localKey value hlookup
      simp [sptLookup] at hlookup
      rcases hlookup with ⟨rfl, rfl⟩
      simp [sptFoldi, sptAcc]
  | bn left right ihLeft ihRight =>
      intro index accumulator localKey value hlookup
      have hzero : localKey ≠ 0 := by
        intro hz
        subst localKey
        simp [sptLookup] at hlookup
      by_cases heven : localKey % 2 = 0
      · let childKey := (localKey - 1) / 2
        have hparent : localKey = 2 * childKey + 2 := by
          dsimp [childKey]
          omega
        have hchild : sptLookup childKey left = some value := by
          simpa [sptLookup, hzero, heven, childKey] using hlookup
        have hchildMem :
            (sptAcc (index + 2 * lrNext index) childKey, value) ∈
              sptFoldi (fun k v entries => (k, v) :: entries)
                (index + 2 * lrNext index) accumulator left :=
          ihLeft _ _ _ _ hchild
        have haddr :
            sptAcc (index + 2 * lrNext index) childKey = sptAcc index localKey := by
          rw [sptAcc_childLeft, hparent]
        have hleft :
            (sptAcc index localKey, value) ∈
              sptFoldi (fun k v entries => (k, v) :: entries)
                (index + 2 * lrNext index) accumulator left := by
          simpa [haddr] using hchildMem
        change (sptAcc index localKey, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries)
            (index + lrNext index)
            (sptFoldi (fun k v entries => (k, v) :: entries)
              (index + 2 * lrNext index) accumulator left) right
        exact sptFoldi_mem_acc right _ _ _ hleft
      · have hodd : localKey % 2 = 1 := by omega
        let childKey := (localKey - 1) / 2
        have hparent : localKey = 2 * childKey + 1 := by
          dsimp [childKey]
          omega
        have hchild : sptLookup childKey right = some value := by
          simpa [sptLookup, hzero, heven, childKey] using hlookup
        have hchildMem :
            (sptAcc (index + lrNext index) childKey, value) ∈
              sptFoldi (fun k v entries => (k, v) :: entries)
                (index + lrNext index)
                (sptFoldi (fun k v entries => (k, v) :: entries)
                  (index + 2 * lrNext index) accumulator left) right :=
          ihRight _ _ _ _ hchild
        have haddr :
            sptAcc (index + lrNext index) childKey = sptAcc index localKey := by
          rw [sptAcc_childRight, hparent]
        change (sptAcc index localKey, value) ∈
          sptFoldi (fun k v entries => (k, v) :: entries)
            (index + lrNext index)
            (sptFoldi (fun k v entries => (k, v) :: entries)
              (index + 2 * lrNext index) accumulator left) right
        simpa [haddr] using hchildMem
  | bs left stored right ihLeft ihRight =>
      intro index accumulator localKey value hlookup
      by_cases hzero : localKey = 0
      · subst localKey
        simp [sptLookup] at hlookup
        subst value
        change (sptAcc index 0, stored) ∈
          sptFoldi (fun k v entries => (k, v) :: entries)
            (index + lrNext index)
            ((index, stored) ::
              sptFoldi (fun k v entries => (k, v) :: entries)
                (index + 2 * lrNext index) accumulator left) right
        exact sptFoldi_mem_acc right _ _ _ (by simp [sptAcc])
      · by_cases heven : localKey % 2 = 0
        · let childKey := (localKey - 1) / 2
          have hparent : localKey = 2 * childKey + 2 := by
            dsimp [childKey]
            omega
          have hchild : sptLookup childKey left = some value := by
            simpa [sptLookup, hzero, heven, childKey] using hlookup
          have hchildMem :
              (sptAcc (index + 2 * lrNext index) childKey, value) ∈
                sptFoldi (fun k v entries => (k, v) :: entries)
                  (index + 2 * lrNext index) accumulator left :=
            ihLeft _ _ _ _ hchild
          have haddr :
              sptAcc (index + 2 * lrNext index) childKey = sptAcc index localKey := by
            rw [sptAcc_childLeft, hparent]
          have hleft :
              (sptAcc index localKey, value) ∈
                sptFoldi (fun k v entries => (k, v) :: entries)
                  (index + 2 * lrNext index) accumulator left := by
            simpa [haddr] using hchildMem
          change (sptAcc index localKey, value) ∈
            sptFoldi (fun k v entries => (k, v) :: entries)
              (index + lrNext index)
              ((index, stored) ::
                sptFoldi (fun k v entries => (k, v) :: entries)
                  (index + 2 * lrNext index) accumulator left) right
          exact sptFoldi_mem_acc right _ _ _ (by simp [hleft])
        · have hodd : localKey % 2 = 1 := by omega
          let childKey := (localKey - 1) / 2
          have hparent : localKey = 2 * childKey + 1 := by
            dsimp [childKey]
            omega
          have hchild : sptLookup childKey right = some value := by
            simpa [sptLookup, hzero, heven, childKey] using hlookup
          have hchildMem :
              (sptAcc (index + lrNext index) childKey, value) ∈
                sptFoldi (fun k v entries => (k, v) :: entries)
                  (index + lrNext index)
                  ((index, stored) ::
                    sptFoldi (fun k v entries => (k, v) :: entries)
                      (index + 2 * lrNext index) accumulator left) right :=
            ihRight _ _ _ _ hchild
          have haddr :
              sptAcc (index + lrNext index) childKey = sptAcc index localKey := by
            rw [sptAcc_childRight, hparent]
          change (sptAcc index localKey, value) ∈
            sptFoldi (fun k v entries => (k, v) :: entries)
              (index + lrNext index)
              ((index, stored) ::
                sptFoldi (fun k v entries => (k, v) :: entries)
                  (index + 2 * lrNext index) accumulator left) right
          simpa [haddr] using hchildMem

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

/-- HOL library `lookup_union` over the exact Spt carrier: union is left
biased on values. Untagged proof support because its original is outside the
CakeML submodule (`HOL/src/finite_maps/sptreeScript.sml`). -/
theorem sptLookup_sptUnion {α : Type} (left right : Spt α) (key : Nat) :
    sptLookup key (sptUnion left right) =
      match sptLookup key left with
      | some v => some v
      | none => sptLookup key right := by
  induction left generalizing right key with
  | ln => simp [sptUnion]
  | ls v =>
      cases right <;> by_cases h0 : key = 0 <;> simp [sptUnion, sptLookup, h0]
  | bn l r ihl ihr =>
      cases right <;> by_cases h0 : key = 0 <;> by_cases he : key % 2 = 0 <;>
        simp [sptUnion, sptLookup, h0, he, ihl, ihr]
      all_goals split <;> simp_all
  | bs l v r ihl ihr =>
      cases right <;> by_cases h0 : key = 0 <;> by_cases he : key % 2 = 0 <;>
        simp [sptUnion, sptLookup, h0, he, ihl, ihr]
      all_goals split <;> simp_all

/-- HOL library `domain_union`: membership in exact Spt union is disjunction.
This is untagged library proof support (the HOL original is outside CakeML),
used by allocation live-set proofs. -/
theorem sptMem_sptUnion {α : Type} (left right : Spt α) (key : Nat) :
    sptMem key (sptUnion left right) ↔ sptMem key left ∨ sptMem key right := by
  unfold sptMem sptDomain
  rw [sptLookup_sptUnion]
  cases sptLookup key left <;> simp

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

/-- HOL `sptree$difference` (`HOL/src/finite_maps/sptreeScript.sml:319-339`):
remove every key present in the right tree while retaining the left payloads.
The right value type is independent because its payloads are never read. The
recursive clauses and `sptMkBN`/`sptMkBS` collapse behavior follow the HOL
definition exactly. The source is outside the CakeML submodule, so this is
Flapjack infrastructure without an `@[hol]` tag. -/
def sptDifference {α β : Type} : Spt α → Spt β → Spt α
  | .ln, _ => .ln
  | .ls value, right =>
      match right with
      | .ln => .ls value
      | .ls _ => .ln
      | .bn _ _ => .ls value
      | .bs _ _ _ => .ln
  | .bn first second, right =>
      match right with
      | .ln => .bn first second
      | .ls _ => .bn first second
      | .bn first' second' =>
          sptMkBN (sptDifference first first') (sptDifference second second')
      | .bs first' _ second' =>
          sptMkBN (sptDifference first first') (sptDifference second second')
  | .bs first value second, right =>
      match right with
      | .ln => .bs first value second
      | .ls _ => .bn first second
      | .bn first' second' =>
          sptMkBS (sptDifference first first') value (sptDifference second second')
      | .bs first' _ second' =>
          sptMkBN (sptDifference first first') (sptDifference second second')
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

/-- External HOL-library `ALOOKUP` rendering for numeric Spt association lists:
return the first value paired with `key`. This helper is untagged because
`ALOOKUP` and `fromAList` here come from the external Sptree library. -/
def sptAListLookup {α : Type} (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (other, value) :: entries =>
      if key = other then some value else sptAListLookup key entries

/-- Lookup in external HOL `fromAList` is first-match association-list lookup,
with no distinct-key or well-formedness premise. -/
theorem sptLookup_sptFromAList {α : Type} (key : Nat)
    (entries : List (Nat × α)) :
    sptLookup key (sptFromAList entries) = sptAListLookup key entries := by
  induction entries with
  | nil => simp [sptFromAList, sptAListLookup]
  | cons entry entries ih =>
      obtain ⟨other, value⟩ := entry
      by_cases hkey : key = other
      · subst key
        rw [sptFromAList, sptLookup_sptInsert_same]
        simp [sptAListLookup]
      · rw [sptFromAList,
          sptLookup_sptInsert_ne other key value (sptFromAList entries) hkey]
        simpa [sptAListLookup, hkey] using ih
/-- A first-match AList lookup is determined by a present entry when every
entry at that key carries the same value. -/
theorem sptAListLookup_eq_of_mem_unique {α : Type} (key : Nat) (value : α) :
    ∀ (entries : List (Nat × α)),
      (key, value) ∈ entries →
      (∀ other, (key, other) ∈ entries → other = value) →
      sptAListLookup key entries = some value := by
  intro entries
  induction entries with
  | nil =>
      intro hmem _
      simp at hmem
  | cons entry entries ih =>
      obtain ⟨other, found⟩ := entry
      intro hmem hunique
      simp only [List.mem_cons] at hmem
      by_cases hkey : key = other
      · have hfound : found = value := by
          apply hunique found
          simp [hkey]
        simp [sptAListLookup, hkey, hfound]
      · rcases hmem with hhead | htail
        · have hEq : key = other := by
            cases hhead
            rfl
          exact False.elim (hkey hEq)
        · have huniqueTail :
              ∀ candidate, (key, candidate) ∈ entries → candidate = value := by
            intro candidate hcandidate
            apply hunique candidate
            exact List.mem_cons_of_mem _ hcandidate
          simp [sptAListLookup, hkey, ih htail huniqueTail]

/-- A successful first-match lookup always witnesses a matching association. -/
theorem sptAListLookup_mem {α : Type} (key : Nat) (entries : List (Nat × α))
    (value : α) (hlookup : sptAListLookup key entries = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [sptAListLookup] at hlookup
  | cons entry entries ih =>
      obtain ⟨other, found⟩ := entry
      by_cases hkey : key = other
      · simp [sptAListLookup, hkey] at hlookup
        subst value
        simp only [List.mem_cons]
        exact Or.inl (by cases hkey; rfl)
      · have htail : sptAListLookup key entries = some value := by
          simpa [sptAListLookup, hkey] using hlookup
        exact List.mem_cons_of_mem _ (ih htail)

/-- External HOL-library lookup/fromAList/toAList observation on the exact
unrestricted Spt carrier. sptFoldi_mem_address and sptFoldi_lookup_mem establish
soundness and completeness of the mixed foldi enumeration;
sptLookup_sptFromAList supplies HOL's first-match ALOOKUP behavior. This
infrastructure is untagged because the source theorem is in the external HOL
finite-map library, not in CakeML (HOL/src/finite_maps/sptreeScript.sml:902-930,
1501-1504). -/
theorem sptLookup_sptFromAList_sptToAList {α : Type} (key : Nat)
    (tree : Spt α) :
    sptLookup key (sptFromAList (sptToAList tree)) = sptLookup key tree := by
  rw [sptLookup_sptFromAList]
  cases htree : sptLookup key tree with
  | none =>
      cases hlist : sptAListLookup key (sptToAList tree) with
      | none => rfl
      | some value =>
          have hmem := sptAListLookup_mem key (sptToAList tree) value hlist
          have hfold :
              (key, value) ∈
                sptFoldi (fun k v entries => (k, v) :: entries) 0 [] tree := by
            simpa [sptToAList] using hmem
          rcases sptFoldi_mem_address tree 0 [] key value hfold with hacc | ⟨localKey, haddr, hlookup⟩
          · simp at hacc
          · have hkey : key = localKey := by
              simpa [sptAcc_eq, lrNext] using haddr
            subst localKey
            rw [htree] at hlookup
            contradiction
  | some value =>
      have hfold := sptFoldi_lookup_mem tree 0 [] key value htree
      have hmem : (key, value) ∈ sptToAList tree := by
        simpa [sptToAList, sptAcc_eq, lrNext] using hfold
      have hunique :
          ∀ other, (key, other) ∈ sptToAList tree → other = value := by
        intro other hother
        have hotherFold :
            (key, other) ∈
              sptFoldi (fun k v entries => (k, v) :: entries) 0 [] tree := by
          simpa [sptToAList] using hother
        rcases sptFoldi_mem_address tree 0 [] key other hotherFold with hacc | ⟨localKey, haddr, hlookup⟩
        · simp at hacc
        · have hkey : key = localKey := by
            simpa [sptAcc_eq, lrNext] using haddr
          subst localKey
          rw [htree] at hlookup
          injection hlookup with hvalue
          exact hvalue.symm
      have hresult := sptAListLookup_eq_of_mem_unique key value
        (sptToAList tree) hmem hunique
      exact hresult

/-- Exact HOL `misc$fromList2_def` (`cakeml/misc/miscScript.sml:351-353`):
    `fromList2 l = SND (FOLDL (\(i,t) a. (i + 2, insert i a t)) (0,LN) l)`,
    which inserts the list elements at the even keys `0, 2, 4, …`. -/
@[hol "cakeml/misc/miscScript.sml" "fromList2_def"]
def sptFromList2 {α : Type} (values : List α) : Spt α :=
  (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 2, sptInsert acc.1 value acc.2))
    (0, .ln)).2

end Flapjack
