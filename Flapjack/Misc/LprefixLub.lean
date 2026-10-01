import Flapjack.HolRef
import Flapjack.Misc.Option
import Flapjack.Misc.LList

/-!
# HOL `lprefix_lub` (least upper bounds of lazy-list prefix chains)

Rendering of HOL4's `examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`
(a pinned external HOL4 snapshot at
`hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`, so the exact
generic chain/equality declarations carry unqualified `@[hol]` tags), plus
HOL's option-choice binder `some` from `Flapjack.Misc.Option`
(`hol4/src/coretypes/optionScript.sml:794`).
HOL sets `'a llist set` are rendered as predicates `HolLList α → Prop`.  These
are the ingredients of the Pancake observational `semantics_def`s
(`build_lprefix_lub (IMAGE ... UNIV)`).  Noncomputable exactly where HOL uses
Hilbert choice.
-/

namespace Flapjack

namespace HolLList

variable {α : Type}

/-- HOL `lprefix_chain ls ⇔ !ll1 ll2. ll1 ∈ ls ∧ ll2 ∈ ls ⇒ LPREFIX ll1 ll2 ∨ LPREFIX ll2 ll1`
    (`lprefix_lubScript.sml:171-174`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_def"]
def lprefixChain (ls : HolLList α → Prop) : Prop :=
  ∀ ll1 ll2, ls ll1 → ls ll2 → lprefix ll1 ll2 ∨ lprefix ll2 ll1

/-- HOL `lprefix_chain_nth n ls = some x. ?l. l ∈ ls ∧ LNTH n l = SOME x`
    (`lprefix_lubScript.sml:200-203`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_nth_def"]
noncomputable def lprefixChainNth (n : Nat) (ls : HolLList α → Prop) : Option α :=
  holOptionSome (fun x => ∃ l, ls l ∧ lnth n l = some x)

/-- HOL `lprefix_lub ls lub ⇔ (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
    (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)` (`lprefix_lubScript.sml:306-310`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_def"]
def lprefixLub (ls : HolLList α → Prop) (lub : HolLList α) : Prop :=
  (∀ ll, ls ll → lprefix ll lub) ∧ (∀ ub, (∀ ll, ls ll → lprefix ll ub) → lprefix lub ub)

/-- HOL `build_lprefix_lub_f ls n = OPTION_MAP (λx. (n+1, x)) (lprefix_chain_nth n ls)`
    (`lprefix_lubScript.sml:430-433`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_f_def"]
noncomputable def buildLprefixLubF (ls : HolLList α → Prop) (n : Nat) : Option (Nat × α) :=
  (lprefixChainNth n ls).map (fun x => (n + 1, x))

/-- HOL `build_lprefix_lub ls = LUNFOLD (build_lprefix_lub_f ls) 0`
    (`lprefix_lubScript.sml:435-438`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_def"]
noncomputable def buildLprefixLub (ls : HolLList α → Prop) : HolLList α :=
  lunfold (buildLprefixLubF ls) 0

/-! ### Prefix-chain support lemmas

`HolLrepOk` makes `rep` downward-closed (a `none` persists), so `lnth` is exactly
`rep`.  These connect the `ltl`/`lhd`-based `lnth` to the `rep` function. -/

/-- Flapjack-only strengthening of the chain-guarded HOL result: no chain
    hypothesis is needed if every member is undefined at this index. The exact
    HOL statement is retained separately in `not_exists_lprefix_chain_nth`. -/
theorem lprefixChainNth_eq_none {n : Nat} {ls : HolLList α → Prop}
    (h : ∀ l, ls l → lnth n l = none) : lprefixChainNth n ls = none := by
  unfold lprefixChainNth holOptionSome
  split
  · rename_i hx
    rcases hx with ⟨x, l, hl, hlth⟩
    rw [h l hl] at hlth
    cases hlth
  · rfl

/-- HOL's original chain-guarded absence statement (215-219), without
    weakening its hypotheses to those of the stronger internal helper. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml"
  "not_exists_lprefix_chain_nth"]
theorem not_exists_lprefix_chain_nth {ls : HolLList α → Prop} {n : Nat}
    (_hchain : lprefixChain ls) (h : ∀ l, ls l → lnth n l = none) :
    lprefixChainNth n ls = none :=
  lprefixChainNth_eq_none h

/-- When `x` is the unique witness of `P`, `holOptionSome P` returns exactly
    `some x` (HOL's `some` picks a fixed but unknown witness; uniqueness pins it). -/
theorem holOptionSome_eq_some {P : α → Prop} {x : α} (hP : P x)
    (huniq : ∀ y, P y → y = x) : holOptionSome P = some x := by
  unfold holOptionSome
  split
  · rename_i h
    rw [huniq _ (Classical.choose_spec h)]
  · rename_i h
    exact absurd ⟨x, hP⟩ h

/-- HOL `lprefix_chain_nth_none_mono`
    (`lprefix_lubScript.sml:225-228`): over a chain, if the family has no value at
    `m` then it has none at any `n ≥ m`.  The chain binder is kept for HOL's
    shape; the Lean proof does not need it. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_nth_none_mono"]
theorem lprefixChainNth_none_mono {m n : Nat} {ls : HolLList α → Prop}
    (_hchain : lprefixChain ls) (hle : m ≤ n) (hm : lprefixChainNth m ls = none) :
    lprefixChainNth n ls = none := by
  apply lprefixChainNth_eq_none
  intro l hl
  cases hnn : lnth n l with
  | none => rfl
  | some x =>
      have hmne : lnth m l ≠ none := by
        intro hmn
        rw [lnth_none_mono l hmn hle] at hnn
        cases hnn
      cases hmn : lnth m l with
      | none => exact absurd hmn hmne
      | some y => exact absurd ⟨l, hl, hmn⟩ ((holOptionSome_none hm) y)

/-- HOL `lprefix_chain_LNTHs_agree` (`lprefix_lubScript.sml:182-187`): on a chain,
    any two members defined at `n` carry the same value there. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_LNTHs_agree"]
theorem lprefixChain_LNTHs_agree {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {l1 l2 : HolLList α} (h1 : ls l1) (h2 : ls l2) {n : Nat} {x1 x2 : α}
    (hx1 : lnth n l1 = some x1) (hx2 : lnth n l2 = some x2) : x1 = x2 := by
  rcases hchain l1 l2 h1 h2 with h | h
  · rw [lprefix_lnth h hx1] at hx2
    exact Option.some.inj hx2
  · rw [lprefix_lnth h hx2] at hx1
    exact (Option.some.inj hx1).symm

/-- HOL `exists_lprefix_chain_nth` (`lprefix_lubScript.sml:205-208`): on a chain,
    if a member has value `x` at `n`, `lprefixChainNth` returns `x`. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "exists_lprefix_chain_nth"]
theorem exists_lprefixChainNth {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {n : Nat} {x : α} (hx : ∃ l, ls l ∧ lnth n l = some x) :
    lprefixChainNth n ls = some x := by
  obtain ⟨l0, hl0, hl0n⟩ := hx
  apply holOptionSome_eq_some
  · exact ⟨l0, hl0, hl0n⟩
  · intro y hy
    obtain ⟨l, hl, hln⟩ := hy
    exact lprefixChain_LNTHs_agree hchain hl hl0 hln hl0n

/-- On a chain the `lunfold` index underlying `build_lprefix_lub` advances by
    exactly one, so its step stays at `buildLprefixLubF`. -/
theorem lunfoldStep_buildLprefixLubF {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ k : Nat, lunfoldStep (buildLprefixLubF ls) 0 k = buildLprefixLubF ls k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [lunfoldStep]
      rw [ih]
      cases hk : lprefixChainNth k ls with
      | none =>
          have hk1 : lprefixChainNth (k + 1) ls = none :=
            lprefixChainNth_none_mono hchain (Nat.le_succ k) hk
          simp [buildLprefixLubF, hk, hk1]
      | some x =>
          simp [buildLprefixLubF, hk]

/-- Flapjack corollary specializing the full HOL lemma to initial index zero.
    This is not the full HOL statement; `lnth_buildLprefixLub_full` retains it. -/
theorem lnth_buildLprefixLub {ls : HolLList α → Prop} (hchain : lprefixChain ls) (k : Nat) :
    lnth k (buildLprefixLub ls) = lprefixChainNth k ls := by
  rw [lnth_eq_rep, buildLprefixLub]
  change (lunfoldStep (buildLprefixLubF ls) 0 k).map Prod.snd = lprefixChainNth k ls
  rw [lunfoldStep_buildLprefixLubF hchain k]
  cases hk : lprefixChainNth k ls with
  | none => simp [buildLprefixLubF, hk]
  | some x => simp [buildLprefixLubF, hk]

/-- HOL `unique_lprefix_lub` (`lprefix_lubScript.sml:419-422`): two least upper
    bounds of the same family are equal. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "unique_lprefix_lub"]
theorem unique_lprefix_lub {ls : HolLList α → Prop} {ll1 ll2 : HolLList α}
    (h1 : lprefixLub ls ll1) (h2 : lprefixLub ls ll2) : ll1 = ll2 :=
  lprefix_antisym (h1.2 ll2 h2.1) (h2.2 ll1 h1.1)

/-- Flapjack-only representation-level iteration lemma for `lunfoldStep`.
    HOL's result is about LNTH of LUNFOLD, not the internal step pair; the exact
    observable statement is `lnth_buildLprefixLub_full` below. -/
theorem buildLprefixLubF_step {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ m n : Nat, lunfoldStep (buildLprefixLubF ls) m n =
      (lprefixChainNth (m + n) ls).map (fun x => (m + n + 1, x)) := by
  intro m n
  induction n generalizing m with
  | zero => simp [lunfoldStep, buildLprefixLubF]
  | succ n ih =>
      rw [lunfoldStep, ih]
      cases hk : lprefixChainNth (m + n) ls with
      | none =>
          have hk1 : lprefixChainNth (m + n + 1) ls = none :=
            lprefixChainNth_none_mono hchain (Nat.le_succ (m + n)) hk
          have harith : m + (n + 1) = m + n + 1 := rfl
          rw [harith, hk1]
          rfl
      | some x =>
          have harith : m + (n + 1) = m + n + 1 := rfl
          rw [harith]
          rfl

/-- HOL `build_lprefix_lub_lem` (`lprefix_lubScript.sml:440-445`) in full:
    `∀ m n, lnth n (lunfold (buildLprefixLubF ls) m) = lprefixChainNth (m+n) ls`
    on a chain.

    The HOL original is an ML `val build_lprefix_lub_lem = Q.prove (...)`
    binding: an ML-let bound theorem value, not a `Theorem`/`Definition`
    header.  `scripts/check-hol-refs.py` resolves `val NAME =` bindings as
    well as header declarations, so citing it from `@[hol]` is legitimate.
    The scanner accepts any `val NAME =` line and does not verify that the
    value is a proof, so not tagging a non-theorem ML value is a source-review
    duty rather than an enforced check. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_lem"]
theorem lnth_buildLprefixLub_full {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    (m n : Nat) :
    lnth n (lunfold (buildLprefixLubF ls) m) = lprefixChainNth (m + n) ls := by
  rw [lnth_eq_rep]
  change (lunfoldStep (buildLprefixLubF ls) m n).map Prod.snd =
    lprefixChainNth (m + n) ls
  rw [buildLprefixLubF_step hchain m n]
  cases lprefixChainNth (m + n) ls with
  | none => rfl
  | some x => rfl

/-- Upper-bound half of `buildLprefixLub_thm`: every chain member is an
    `lprefix` of `buildLprefixLub ls`. -/
theorem buildLprefixLub_upper {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ ll, ls ll → lprefix ll (buildLprefixLub ls) := by
  intro ll hl
  apply lprefix_of_rep_agree
  intro n x hx
  rw [← lnth_eq_rep] at hx
  have hcn : lprefixChainNth n ls = some x :=
    exists_lprefixChainNth hchain ⟨ll, hl, hx⟩
  rw [← lnth_eq_rep]
  rw [lnth_buildLprefixLub hchain n]
  exact hcn

/-- Least-upper-bound half of `buildLprefixLub_thm`: `buildLprefixLub ls` is
    below every upper bound of the chain. -/
theorem buildLprefixLub_least {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ ub, (∀ ll, ls ll → lprefix ll ub) → lprefix (buildLprefixLub ls) ub := by
  intro ub hub
  apply lprefix_of_rep_agree
  intro n x hx
  rw [← lnth_eq_rep] at hx
  rw [lnth_buildLprefixLub hchain n] at hx
  obtain ⟨l, hl, hln⟩ := holOptionSome_some hx
  rw [← lnth_eq_rep]
  exact lprefix_lnth (hub l hl) hln

/-- HOL `build_lprefix_lub_thm` (`lprefix_lubScript.sml:451-454`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_thm"]
theorem buildLprefixLub_thm {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    lprefixLub ls (buildLprefixLub ls) :=
  ⟨buildLprefixLub_upper hchain, buildLprefixLub_least hchain⟩

/-- HOL `lprefix_lub_nth` (`lprefix_lubScript.sml:319-322`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_nth"]
theorem lprefix_lub_nth {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {lub : HolLList α} :
    (lprefixLub ls lub ↔ ∀ n, lnth n lub = lprefixChainNth n ls) := by
  constructor
  · intro hlub n
    rw [unique_lprefix_lub hlub (buildLprefixLub_thm hchain)]
    exact lnth_buildLprefixLub hchain n
  · intro hnth
    constructor
    · intro ll hl
      apply lprefix_of_rep_agree
      intro n x hx
      rw [← lnth_eq_rep] at hx
      have hcn : lprefixChainNth n ls = some x :=
        exists_lprefixChainNth hchain ⟨ll, hl, hx⟩
      rw [← lnth_eq_rep]
      rw [hnth n]
      exact hcn
    · intro ub hub
      apply lprefix_of_rep_agree
      intro n x hx
      rw [← lnth_eq_rep] at hx
      rw [hnth n] at hx
      obtain ⟨l, hl, hln⟩ := holOptionSome_some hx
      rw [← lnth_eq_rep]
      exact lprefix_lnth (hub l hl) hln

/-- HOL `build_prefix_lub_intro` (`lprefix_lubScript.sml:515-517`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_prefix_lub_intro"]
theorem build_prefix_lub_intro {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {lub : HolLList α} :
    (lprefixLub ls lub ↔ lub = buildLprefixLub ls) := by
  constructor
  · intro hlub
    exact unique_lprefix_lub hlub (buildLprefixLub_thm hchain)
  · intro h
    rw [h]
    exact buildLprefixLub_thm hchain

/-! ### Chain/equality lemmas

HOL `equiv_lprefix_chain`, `lprefix_rel` and the derived equality facts
(`lprefix_lubScript.sml:242-558`). -/

/-- HOL `equiv_lprefix_chain ls1 ls2 ⇔
    !n. lprefix_chain_nth n ls1 = lprefix_chain_nth n ls2`
    (`lprefix_lubScript.sml:242-245`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "equiv_lprefix_chain_def"]
def equivLprefixChain (ls1 ls2 : HolLList α → Prop) : Prop :=
  ∀ n, lprefixChainNth n ls1 = lprefixChainNth n ls2

/-- HOL `lprefix_rel s1 s2 ⇔ ∀l1. l1 IN s1 ⇒ ∃l2. l2 IN s2 ∧ LPREFIX l1 l2`
    (`lprefix_lubScript.sml:522-524`); HOL sets `'a llist set` are predicates
    `HolLList α → Prop`. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_rel_def"]
def lprefixRel (s1 s2 : HolLList α → Prop) : Prop :=
  ∀ l1, s1 l1 → ∃ l2, s2 l2 ∧ lprefix l1 l2

/-- HOL `lprefix_lub_is_chain` (`lprefix_lubScript.sml:312-317`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_is_chain"]
theorem lprefix_lub_is_chain {ls : HolLList α → Prop} {ll : HolLList α}
    (h : lprefixLub ls ll) : lprefixChain ls := by
  intro a b ha hb
  exact lprefix_total_of_common (h.1 a ha) (h.1 b hb)

/-- HOL `equiv_lprefix_chain_thm` (`lprefix_lubScript.sml:247-262`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "equiv_lprefix_chain_thm"]
theorem equivLprefixChain_thm {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2) :
    (equivLprefixChain ls1 ls2 ↔
      (∀ ll1 n x, ls1 ll1 → lnth n ll1 = some x →
        ∃ ll2, ls2 ll2 ∧ lnth n ll2 = some x) ∧
      (∀ ll2 n x, ls2 ll2 → lnth n ll2 = some x →
        ∃ ll1, ls1 ll1 ∧ lnth n ll1 = some x)) := by
  constructor
  · intro heq
    refine ⟨?_, ?_⟩
    · intro ll1 n x hl1 hln
      have hc1 : lprefixChainNth n ls1 = some x :=
        exists_lprefixChainNth h1 ⟨ll1, hl1, hln⟩
      have hc2 : lprefixChainNth n ls2 = some x := by
        rw [← heq n]; exact hc1
      exact holOptionSome_some (P := fun z => ∃ l, ls2 l ∧ lnth n l = some z) (x := x) hc2
    · intro ll2 n x hl2 hln
      have hc2 : lprefixChainNth n ls2 = some x :=
        exists_lprefixChainNth h2 ⟨ll2, hl2, hln⟩
      have hc1 : lprefixChainNth n ls1 = some x := by
        rw [heq n]; exact hc2
      exact holOptionSome_some (P := fun z => ∃ l, ls1 l ∧ lnth n l = some z) (x := x) hc1
  · intro hdir
    rw [equivLprefixChain]
    intro n
    cases hc1 : lprefixChainNth n ls1 with
    | none =>
        symm
        apply lprefixChainNth_eq_none
        intro l2 hl2
        cases hln : lnth n l2 with
        | none => rfl
        | some y =>
            obtain ⟨l1, hl1, hln1⟩ := hdir.2 l2 n y hl2 hln
            have hcontra := exists_lprefixChainNth h1 ⟨l1, hl1, hln1⟩
            rw [hc1] at hcontra
            exact absurd hcontra (by simp)
    | some x =>
        obtain ⟨l1, hl1, hln1⟩ :=
          holOptionSome_some (P := fun z => ∃ l, ls1 l ∧ lnth n l = some z) (x := x) hc1
        obtain ⟨l2, hl2, hln2⟩ := hdir.1 l1 n x hl1 hln1
        exact (exists_lprefixChainNth h2 ⟨l2, hl2, hln2⟩).symm

/-- HOL `llist_shorter` (`lprefix_lubScript.sml:122-129`): `ll1` is no longer
    than `ll2`; `none` is the infinite length. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "llist_shorter_def"]
def llistShorter (ll1 ll2 : HolLList α) : Prop :=
  match llength ll1, llength ll2 with
  | none, none => True
  | some _, none => True
  | none, some _ => False
  | some x, some y => x ≤ y

/-- HOL `llist_shorter_fromList` (`lprefix_lubScript.sml:163-169`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "llist_shorter_fromList"]
theorem llistShorter_fromList (l1 l2 : List α) :
    llistShorter (fromList l1) (fromList l2) ↔ l1.length ≤ l2.length := by
  simp [llistShorter, llength_fromList]

/-- HOL `llist_shorter_lnth` (`lprefix_lubScript.sml:131-161`): `ll1` is no
    longer than `ll2` exactly when `ll2` is defined wherever `ll1` is.

    The HOL original is an ML `val llist_shorter_lnth = Q.prove (...)` binding
    (theorem-valued, not a header declaration); the reference checker resolves
    `val NAME =` bindings, so the tag above is a faithful citation.  The
    scanner does not distinguish a theorem value from other ML values, so
    avoiding tags on non-theorem ML values is a source-review duty. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "llist_shorter_lnth"]
theorem llistShorter_lnth {ll1 ll2 : HolLList α} :
    llistShorter ll1 ll2 ↔
      ∀ n x, lnth n ll1 = some x → ∃ y, lnth n ll2 = some y := by
  cases h1 : llength ll1 with
  | none =>
      cases h2 : llength ll2 with
      | none =>
          simp only [llistShorter, h1, h2]
          exact ⟨fun _ n x _ => lnth_some_of_not_LFinite (not_LFinite_of_llength_eq_none h2) n,
                 fun _ => trivial⟩
      | some b =>
          simp only [llistShorter, h1, h2]
          constructor
          · intro h; exact h.elim
          · intro H
            obtain ⟨x, hx⟩ :=
              lnth_some_of_not_LFinite (not_LFinite_of_llength_eq_none h1) b
            obtain ⟨y, hy⟩ := H b x hx
            rw [lnth_none_of_LLengthRel (LLengthRel_of_llength_eq_some h2)
              (Nat.le_refl b)] at hy
            exact Option.some_ne_none y hy.symm
  | some a =>
      cases h2 : llength ll2 with
      | none =>
          simp only [llistShorter, h1, h2]
          exact ⟨fun _ n x _ => lnth_some_of_not_LFinite (not_LFinite_of_llength_eq_none h2) n,
                 fun _ => trivial⟩
      | some b =>
          simp only [llistShorter, h1, h2]
          constructor
          · intro hab n x hx
            have hnlt : n < a := by
              by_cases hlt : n < a
              · exact hlt
              · exfalso
                rw [lnth_none_of_LLengthRel (LLengthRel_of_llength_eq_some h1)
                  (Nat.le_of_not_lt hlt)] at hx
                exact Option.some_ne_none x hx.symm
            exact lnth_some_of_LLengthRel (LLengthRel_of_llength_eq_some h2) n
              (Nat.lt_of_lt_of_le hnlt hab)
          · intro H
            by_cases hle : a ≤ b
            · exact hle
            · exfalso
              obtain ⟨x, hx⟩ := lnth_some_of_LLengthRel
                (LLengthRel_of_llength_eq_some h1) b (Nat.lt_of_not_le hle)
              obtain ⟨y, hy⟩ := H b x hx
              rw [lnth_none_of_LLengthRel (LLengthRel_of_llength_eq_some h2)
                (Nat.le_refl b)] at hy
              exact Option.some_ne_none y hy.symm

/-- HOL `equiv_lprefix_chain_thm2` (`lprefix_lubScript.sml:264-304`): with both
    families chains and every member of `ls2` finite, `equiv_lprefix_chain`
    equivalently says that `ls2` supplies a value wherever `ls1` does and that
    every non-empty `ls2` member is `llist_shorter` than some `ls1` member. -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "equiv_lprefix_chain_thm2"]
theorem equiv_lprefix_chain_thm2 {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2)
    (hfin : ∀ ll2, ls2 ll2 → LFinite ll2) :
    (equivLprefixChain ls1 ls2 ↔
      (∀ (ll1 : HolLList α) (n : Nat) (x : α), ls1 ll1 → lnth n ll1 = some x →
        ∃ ll2, ls2 ll2 ∧ lnth n ll2 = some x) ∧
      (∀ (ll2 : HolLList α) (_n : Nat) (_x : α), ls2 ll2 → ll2 ≠ lnil →
        ∃ ll1, ls1 ll1 ∧ llistShorter ll2 ll1)) := by
  rw [equivLprefixChain_thm h1 h2]
  constructor
  · intro ⟨hA, hB⟩
    refine ⟨hA, ?_⟩
    intro ll2 n x hl2 hne
    obtain ⟨len, _, hrel⟩ := llength_spec (hfin ll2 hl2)
    have hlen0 : len ≠ 0 := by
      intro h0
      exact hne (eq_lnil_of_LLengthRel_zero (h0 ▸ hrel))
    obtain ⟨v, hv⟩ := lnth_some_of_LLengthRel hrel len.pred (Nat.pred_lt hlen0)
    obtain ⟨ll1, hl1, hln1⟩ := hB ll2 len.pred v hl2 hv
    refine ⟨ll1, hl1, ?_⟩
    apply llistShorter_lnth.mpr
    intro m y hmy
    have hmx : m < len := by
      by_cases hlt : m < len
      · exact hlt
      · exfalso
        rw [lnth_none_of_LLengthRel hrel (Nat.le_of_not_lt hlt)] at hmy
        exact Option.some_ne_none y hmy.symm
    exact lnth_some_down_closed hln1 (Nat.le_pred_of_lt hmx)
  · intro ⟨hA, hC⟩
    refine ⟨hA, ?_⟩
    intro ll2 n x hl2 hln
    have hne : ll2 ≠ lnil := by
      intro heq
      rw [heq] at hln
      have : lnth n (lnil : HolLList α) = none := by rw [lnth_eq_rep]; rfl
      rw [this] at hln
      exact Option.some_ne_none x hln.symm
    obtain ⟨ll1, hl1, hsh⟩ := hC ll2 n x hl2 hne
    obtain ⟨z, hz⟩ := (llistShorter_lnth.mp hsh) n x hln
    obtain ⟨ll2', hl2', hln2'⟩ := hA ll1 n z hl1 hz
    have hzx : z = x := lprefixChain_LNTHs_agree h2 hl2' hl2 hln2' hln
    exact ⟨ll1, hl1, by rw [hzx] at hz; exact hz⟩

/-- HOL `lprefix_rel_lnth` (`lprefix_lubScript.sml:526-538`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_rel_lnth"]
theorem lprefix_rel_lnth {ls1 ls2 : HolLList α → Prop} (h : lprefixRel ls1 ls2) :
    ∀ ll1 n x, ls1 ll1 → lnth n ll1 = some x →
      ∃ ll2, ls2 ll2 ∧ lnth n ll2 = some x := by
  intro ll1 n x hl1 hln
  obtain ⟨l2, hl2, hpre⟩ := h ll1 hl1
  exact ⟨l2, hl2, lprefix_lnth hpre hln⟩

/-- HOL `IMP_equiv_lprefix_chain` (`lprefix_lubScript.sml:540-548`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "IMP_equiv_lprefix_chain"]
theorem IMP_equiv_lprefix_chain {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2)
    (hr12 : lprefixRel ls1 ls2) (hr21 : lprefixRel ls2 ls1) :
    equivLprefixChain ls1 ls2 := by
  rw [equivLprefixChain_thm h1 h2]
  exact ⟨lprefix_rel_lnth hr12, lprefix_rel_lnth hr21⟩

/-- HOL `lprefix_lub_equiv_chain2` (`lprefix_lubScript.sml:471-484`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_equiv_chain2"]
theorem lprefix_lub_equiv_chain2 {ls1 ls2 : HolLList α → Prop} {ll1 ll2 : HolLList α}
    (h1 : lprefixLub ls1 ll1) (h2 : lprefixLub ls2 ll2) :
    (ll1 = ll2 ↔ equivLprefixChain ls1 ls2) := by
  have hc1 := lprefix_lub_is_chain h1
  have hc2 := lprefix_lub_is_chain h2
  constructor
  · intro heq
    subst heq
    rw [equivLprefixChain]
    intro n
    rw [← (lprefix_lub_nth hc1).mp h1 n, ← (lprefix_lub_nth hc2).mp h2 n]
  · intro heq
    apply ext_of_rep
    intro n
    rw [← lnth_eq_rep n ll1, ← lnth_eq_rep n ll2]
    rw [(lprefix_lub_nth hc1).mp h1 n, (lprefix_lub_nth hc2).mp h2 n]
    exact heq n

/-- HOL `IMP_build_lprefix_lub_EQ` (`lprefix_lubScript.sml:550-558`). -/
@[hol "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "IMP_build_lprefix_lub_EQ"]
theorem IMP_build_lprefix_lub_EQ {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2)
    (hr12 : lprefixRel ls1 ls2) (hr21 : lprefixRel ls2 ls1) :
    buildLprefixLub ls1 = buildLprefixLub ls2 :=
  (lprefix_lub_equiv_chain2 (buildLprefixLub_thm h1) (buildLprefixLub_thm h2)).mpr
    (IMP_equiv_lprefix_chain h1 h2 hr12 hr21)

end HolLList

end Flapjack
