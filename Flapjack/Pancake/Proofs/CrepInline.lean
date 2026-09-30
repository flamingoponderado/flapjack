import Flapjack.HolRef
import Flapjack.PanToCrepMaxList
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepInline.Canonical

/-! Exact theorem counterpart for CakeML's `crep_inlineProofScript.sml`.

    The declarations here are stated over Lean's `(List.range n).map f`, the
    image of HOL's `GENLIST f n`, and over `Nat`, matching the source's
    `:num` variables. Each carries the HOL declaration name and argument
    order verbatim. -/

namespace Flapjack

/-- CakeML's `genlist_less_than` (`crep_inlineProofScript.sml:629`): every value
    in `GENLIST (λx. a + SUC x) n` is strictly above `a`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_less_than"]
theorem genlist_less_than (n a v : Nat) :
    v ∈ (List.range n).map (fun x => a + (x + 1)) → a < v := by
  intro hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  omega

/-- CakeML's `genlist_not_in` (`crep_inlineProofScript.sml:636`): values at or
    below `a` do not occur in `GENLIST (λx. a + SUC x) n`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_not_in"]
theorem genlist_not_in (n a v : Nat) (h : v ≤ a) :
    v ∉ (List.range n).map (fun x => a + (x + 1)) := by
  intro hmem
  have := genlist_less_than n a v hmem
  omega

/-- CakeML's `genlist_all_distinct` (`crep_inlineProofScript.sml:643`):
    `GENLIST (λx. a + SUC x) n` has no duplicates. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_all_distinct"]
theorem genlist_all_distinct (n a : Nat) :
    ((List.range n).map (fun x => a + (x + 1))).Nodup :=
  List.Pairwise.map (fun x => a + (x + 1))
    (fun _left _right hne heq =>
      hne (Nat.add_right_cancel (Nat.add_left_cancel heq)))
    List.nodup_range

/-- CakeML's `MORE_THEN_NOT_MAX_LIST` (`crep_inlineProofScript.sml:1562`): a
    value strictly above `MAX_LIST l` does not occur in `l`.  Lean's `maxList`
    is the faithful port of HOL's `rich_list$MAX_LIST`
    (`Flapjack/PanToCrepMaxList.lean`), so this is the same fact as HOL's
    `MAX_LIST_NOT_MEM`, stated here under the `crep_inline` declaration name. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MORE_THEN_NOT_MAX_LIST"]
theorem moreThenNotMaxList (l : List Nat) (x : Nat) (h : maxList l < x) :
    x ∉ l :=
  maxList_not_mem x l (by omega)

/-- CakeML's `max_list_genlist_add_suc_val`
    (`crep_inlineProofScript.sml:2579`): the maximum of
    `GENLIST (λx. SUC x + k) n` is `n + k` for `n ≠ 0`.  `(List.range n).map f`
    is Lean's image of HOL's `GENLIST f n`, and `maxList` is the faithful
    `rich_list$MAX_LIST` port (`Flapjack/PanToCrepMaxList.lean`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "max_list_genlist_add_suc_val"]
theorem max_list_genlist_add_suc_val (k : Nat) :
    ∀ n, n ≠ 0 →
      maxList ((List.range n).map (fun x => (x + 1) + k)) = n + k :=
  maxList_genlist_add_suc_val k

/-- CakeML's `cont_res` (`crep_inlineProofScript.sml:2168`): a finite,
    "continuous" result predicate.  `NONE` and `SOME` results that stop the
    walk (`Break`, `Continue`, `Error`) are `T`; all other results
    (`TimeOut`, `Return`, `Exception`, `FinalFFI`) are `F`.  The carrier is
    `CrepResultHOL`, the exact constructor-by-constructor encoding of
    `crepSem$result` (`crepSemScript.sml:37-44`), so the fourth HOL equation
    `cont_res _ = F` is the four remaining constructors. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "cont_res_def"]
def contResHOL : Option (CrepResultHOL α ε) → Bool
  | none => true
  | some (.break _) => true
  | some (.continue _) => true
  | some .error => true
  | some _ => false

/-- CakeML's `MEM_MAP2_IMP` (`crep_inlineProofScript.sml:2233`): every element
    of a pointwise map comes from elements of both input lists.  We keep the
    Flapjack lemma name `panMap2_mem`; `panMap2` is the exact `MAP2` port. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MEM_MAP2_IMP"]
theorem panMap2_mem {α β γ : Type} {f : α → β → γ} {l1 : List α} {l2 : List β}
    {x : γ} (hmem : x ∈ panMap2 f l1 l2) :
    ∃ y1 y2, x = f y1 y2 ∧ y1 ∈ l1 ∧ y2 ∈ l2 := by
  induction l1 generalizing l2 with
  | nil => simp [panMap2] at hmem
  | cons a as ih =>
      cases l2 with
      | nil => simp [panMap2] at hmem
      | cons b bs =>
          simp only [panMap2, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact ⟨a, b, heq, by simp, by simp⟩
          · obtain ⟨y1, y2, heq, h1, h2⟩ := ih hmem
            exact ⟨y1, y2, heq, by simp [h1], by simp [h2]⟩

/-- CakeML's `not_some_is_none` (`crep_inlineProofScript.sml:778`): an option
    with no `SOME` inhabitant is `NONE`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_some_is_none"]
theorem not_some_is_none {α : Type u} (a : Option α) :
    (∀ v, a ≠ some v) ↔ a = none := by
  cases a <;> simp

/-- CakeML's `fdom_eq_flookup_thm` (`crep_inlineProofScript.sml:784`): two
    finite maps have the same domain iff each lookup in one is supported in the
    other and a missing lookup in the first is missing in the second.  `FDOM`
    is the repo finite-map domain predicate (`Flapjack/FiniteMap/Basic.lean`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_eq_flookup_thm"]
theorem fdom_eq_flookup_thm {α : Type} {β : Type} (f1 f2 : FiniteMap α β) :
    FDOM f1 = FDOM f2 ↔
      (∀ x, (∃ v, FLOOKUP f1 x = some v) → (∃ v, FLOOKUP f2 x = some v)) ∧
      (∀ x, FLOOKUP f1 x = none → FLOOKUP f2 x = none) := by
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨v, hv⟩ := hx
      have hv' : f1 x = some v := hv
      have h1 : f1 x ≠ none := by rw [hv']; exact Option.some_ne_none v
      have h2 : f2 x ≠ none := (congrFun h x).mp h1
      cases hf2 : f2 x with
      | none => exact absurd hf2 h2
      | some w => exact ⟨w, hf2⟩
    · intro x hx
      have hx' : f1 x = none := hx
      have h1 : ¬ (f1 x ≠ none) := fun hc => hc hx'
      have h2 : ¬ (f2 x ≠ none) := fun hc => h1 ((congrFun h x).mpr hc)
      cases hf2 : f2 x with
      | none => exact hf2
      | some w => exact (h2 (by rw [hf2]; exact Option.some_ne_none w)).elim
  · rintro ⟨h12, hnone⟩
    funext x
    apply propext
    constructor
    · intro h1
      have hx : ∃ v, f1 x = some v := by
        cases hf1 : f1 x with
        | none => exact absurd hf1 h1
        | some v => exact ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := h12 x hx
      change f2 x ≠ none
      rw [show f2 x = some w from hw]
      exact Option.some_ne_none w
    · intro h2 hf1
      exact h2 (hnone x hf1)

/-- CakeML's `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`):
    `FDOM f` is contained in `FDOM g` iff every defined lookup in `f` is
    defined in `g`.  Subset of the `FDOM` predicate is pointwise implication. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdom_subset_flookup_thm"]
theorem fdom_subset_flookup_thm {α : Type} {β : Type} (f g : FiniteMap α β) :
    (∀ x, FDOM f x → FDOM g x) ↔
      (∀ x p, FLOOKUP f x = some p → ∃ q, FLOOKUP g x = some q) := by
  constructor
  · intro h x p hp
    have hf : f x ≠ none := by rw [show f x = some p from hp]; exact Option.some_ne_none p
    have hg : g x ≠ none := h x hf
    cases hx : g x with
    | none => exact absurd hx hg
    | some q => exact ⟨q, hx⟩
  · intro h x hf
    cases hx : f x with
    | none => exact absurd hx hf
    | some p =>
        obtain ⟨q, hq⟩ := h x p hx
        change g x ≠ none
        rw [show g x = some q from hq]
        exact Option.some_ne_none q

/-- CakeML's `res_var_commutes_strong` (`crep_inlineProofScript.sml:699`):
    `res_var` updates at two keys commute, with no `n ≠ h` side condition (the
    equal case is definitional).  Stated over the reviewed `resVar`
    (`res_var_def`), whose Boolean key equality reflects HOL's `=` under
    `[LawfulBEq α]`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem res_var_commutes_strong [BEq α] [LawfulBEq α] (lc lc' : FiniteMap α β)
    (n h : α) :
    resVar (resVar lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
    resVar (resVar lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  by_cases hne : n = h
  · subst hne
    rfl
  · exact resVar_commutes lc lc' n h hne

/-- CakeML's `res_var_foldl_commutes_strong`
    (`crep_inlineProofScript.sml:706`): commuting a single `res_var` update past
    a `foldl` of `res_var` over the `ZIP`ped lookup list.  `ZIP (vs, MAP f vs)`
    is Lean's `vs.zip (vs.map f)`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem res_var_foldl_commutes_strong [BEq α] [LawfulBEq α]
    (h : α) (vs : List α) (lc1 lc2 : FiniteMap α β) :
    resVar ((vs.zip (vs.map (FLOOKUP lc2))).foldl resVar lc1)
        (h, FLOOKUP lc2 h) =
      (vs.zip (vs.map (FLOOKUP lc2))).foldl resVar
        (resVar lc1 (h, FLOOKUP lc2 h)) := by
  induction vs generalizing lc1 with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih (resVar lc1 (v, FLOOKUP lc2 v)),
        (res_var_commutes_strong lc1 lc2 v h).symm]

/-- CakeML's `flookup_res_var_is_mem_zip_eq` (`crep_inlineProofScript.sml:802`):
    folding `res_var` over the `ZIP`ped lookup list and then looking up a member
    `x` of the key list reproduces `lc2`'s binding for `x`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem flookup_res_var_is_mem_zip_eq [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (lc1 lc2 : FiniteMap α β) (hx : x ∈ xs) :
    FLOOKUP ((xs.zip (xs.map (FLOOKUP lc2))).foldl resVar lc1) x =
      FLOOKUP lc2 x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [← res_var_foldl_commutes_strong a as lc1 lc2, FLOOKUP_resVar]
      rcases List.mem_cons.mp hx with hxa | hxas
      · subst hxa
        simp
      · by_cases hxa : x = a
        · subst hxa
          simp
        · rw [if_neg (by rw [beq_eq_false_iff_ne.mpr hxa]; simp)]
          exact ih hxas

/-- CakeML's `OPT_MMAP_SOME_ALL` (`crep_inlineProofScript.sml:36`): the optional
    map over a list succeeds for some result exactly when every element maps to
    a `some`.  `List.mapM` is the repo's `OPT_MMAP` carrier (cf. the tagged
    `optMmapEqSome`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "OPT_MMAP_SOME_ALL"]
theorem OPT_MMAP_SOME_ALL {α : Type} {β : Type} (f : α → Option β) (l : List α) :
    (∃ x, l.mapM f = some x) ↔ (∀ e, e ∈ l → ∃ y, f e = some y) := by
  induction l with
  | nil => simp
  | cons a as ih =>
      constructor
      · rintro ⟨x, hx⟩ e he
        rcases List.mem_cons.mp he with hea | he
        · rw [hea]
          cases hfa : f a with
          | none => rw [List.mapM_cons] at hx; simp [hfa] at hx
          | some y => exact ⟨y, rfl⟩
        · cases hfa : f a with
          | none => rw [List.mapM_cons] at hx; simp [hfa] at hx
          | some y =>
              cases hta : as.mapM f with
              | none => rw [List.mapM_cons] at hx; simp [hfa, hta] at hx
              | some rest => exact ih.mp ⟨rest, hta⟩ e he
      · intro h
        obtain ⟨y, hy⟩ := h a List.mem_cons_self
        obtain ⟨ys, hys⟩ := ih.mpr (fun e he => h e (List.mem_cons_of_mem a he))
        exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- CakeML's `OPT_MMAP_ALL_EQ` (`crep_inlineProofScript.sml:47`): two optional
    maps over a list agree when their functions agree on every element. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "OPT_MMAP_ALL_EQ"]
theorem OPT_MMAP_ALL_EQ {α : Type} {β : Type} (f g : α → Option β) (l : List α)
    (h : ∀ e, e ∈ l → f e = g e) : l.mapM f = l.mapM g := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.mapM_cons, h a List.mem_cons_self,
        ih (fun e he => h e (List.mem_cons_of_mem a he))]

/-- CakeML's `fdoms_eq_opt_mmap_flookup_some`
    (`crep_inlineProofScript.sml:1833`): if two finite maps have the same
    domain, an `OPT_MMAP` of `FLOOKUP` over the first succeeding implies the
    same sequence over the second succeeds. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "fdoms_eq_opt_mmap_flookup_some"]
theorem fdoms_eq_opt_mmap_flookup_some {α : Type} {β : Type} (vs : List α)
    (fm fm' : FiniteMap α β) (vals : List β) (hdom : FDOM fm = FDOM fm')
    (h : vs.mapM (FLOOKUP fm) = some vals) :
    ∃ z, vs.mapM (FLOOKUP fm') = some z := by
  have hall : ∀ e, e ∈ vs → ∃ y, FLOOKUP fm e = some y :=
    (OPT_MMAP_SOME_ALL (FLOOKUP fm) vs).mp ⟨vals, h⟩
  refine (OPT_MMAP_SOME_ALL (FLOOKUP fm') vs).mpr ?_
  intro e he
  obtain ⟨y, hy⟩ := hall e he
  have hmem : FDOM fm' e := by
    rw [← hdom]
    change fm e ≠ none
    change fm e = some y at hy
    rw [hy]
    exact Option.some_ne_none y
  change fm' e ≠ none at hmem
  cases h' : fm' e with
  | none => rw [h'] at hmem; exact absurd rfl hmem
  | some z => exact ⟨z, by change fm' e = some z; rw [h']⟩

/-! ## State and locals relations of `inline_prog_correct` -/

/-- CakeML's `state_rel` (`crep_inlineProofScript.sml:12`): two Crep states agree
    on globals, code, memory, both address domains, clock, endianness, FFI
    state, and base/top addresses.  `CrepHolState` is the exact 11-field
    encoding of `crepSem$state`, so this is a field-by-field port; like HOL it
    leaves `locals` to `locals_rel`/`locals_strong_rel`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineStateRelW below.
def crepInlineStateRel (s t : CrepHolState α σ) : Prop :=
  s.globals = t.globals ∧
  s.code = t.code ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.bigEndian = t.bigEndian ∧
  s.ffi = t.ffi ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress

/-- Finite-map `SUBMAP` for Lean's extensional lookup-function representation:
    every binding of `s` is also a binding of `t` with the same value.  HOL's
    `SUBMAP` holds when `FLOOKUP s` and `FLOOKUP t` agree on `FDOM s`, which is
    exactly this statement.  Untagged infrastructure: HOL's `SUBMAP` is a
    finite-map operation, not a declaration of `crep_inlineProofScript.sml`. -/
def crepHolSubmap {κ : Type} (s t : κ → Option β) : Prop :=
  ∀ n v, s n = some v → t n = some v

/-- Finite-map `SUBMAP_IMP_FUPDATE_SUBMAP`
    (`crep_inlineProofScript.sml:117`): pointwise updates at the same key
    preserve `SUBMAP`.  Stated over `crepHolSubmap`; `|+` is `FUPDATE`, whose
    Boolean key equality reflects HOL's `=` under `[LawfulBEq κ]`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem SUBMAP_IMP_FUPDATE_SUBMAP {κ : Type} {β : Type} [BEq κ] [LawfulBEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FUPDATE f (x, y)) (FUPDATE g (x, y)) := by
  intro n v hn
  by_cases hxn : x = n
  · subst hxn
    simp only [FUPDATE, beq_self_eq_true] at hn ⊢
    exact hn
  · have hb : (x == n) = false := beq_eq_false_iff_ne.mpr hxn
    simp only [FUPDATE, hb] at hn ⊢
    exact h n v hn

/-- Finite-map `SUBMAP_IMP_DOMSUB_SUBMAP`
    (`crep_inlineProofScript.sml:127`): removing the same key from both sides
    preserves `SUBMAP`.  `\\` is `FDOMSUB`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem SUBMAP_IMP_DOMSUB_SUBMAP {κ : Type} {β : Type} [BEq κ] [LawfulBEq κ]
    (f g : κ → Option β) (x : κ) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB f x) (FDOMSUB g x) := by
  intro n v hn
  by_cases hxn : x = n
  · subst hxn
    simp [FDOMSUB] at hn
  · have hb : (x == n) = false := beq_eq_false_iff_ne.mpr hxn
    simp only [FDOMSUB, hb] at hn ⊢
    exact h n v hn

/-- Finite-map `SUBMAP_IMP_DOMSUB_FUPDATE`
    (`crep_inlineProofScript.sml:135`): removing a key from the left and
    inserting it on the right preserves `SUBMAP`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem SUBMAP_IMP_DOMSUB_FUPDATE {κ : Type} {β : Type} [BEq κ] [LawfulBEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB f x) (FUPDATE g (x, y)) := by
  intro n v hn
  by_cases hxn : x = n
  · subst hxn
    simp [FDOMSUB] at hn
  · have hb : (x == n) = false := beq_eq_false_iff_ne.mpr hxn
    simp only [FDOMSUB, FUPDATE, hb] at hn ⊢
    exact h n v hn

/-- CakeML's `FOLDL_res_var_ZIP_lookup_var` (`crep_inlineProofScript.sml:2661`):
    a fold of `res_var` over the zipped names and their `l'`-lookups is a
    `SUBMAP` (`crepHolSubmap`) of `l1`, so any lookup that `l` already defined at
    a key not in `ns` survives in `l1`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem FOLDL_res_var_ZIP_lookup_var [BEq α] [LawfulBEq α] (l l' l1 : FiniteMap α β)
    (ns : List α) (x : α) (v : β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVar l) l1)
    (hv : FLOOKUP l x = some v) (hx : x ∉ ns) :
    FLOOKUP l1 x = some v := by
  apply hsub x v
  change FLOOKUP ((ns.zip (ns.map (FLOOKUP l'))).foldl resVar l) x = some v
  rw [FLOOKUP_foldl_resVar_zip_not_mem ns (ns.map (FLOOKUP l')) l x
    (by simp [List.length_map]) hx]
  exact hv

/-- CakeML's `FOLDL_res_var_ZIP_lookup` (`crep_inlineProofScript.sml:2675`):
    the `OPT_MMAP` (`List.mapM`) form of `FOLDL_res_var_ZIP_lookup_var`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar`/`FUPDATE` use Boolean key equality.
-- Faithful HOL-equality port tracked by bead flapjack-pxn.18.5.5.19.
theorem FOLDL_res_var_ZIP_lookup [BEq α] [LawfulBEq α] (l l' l1 : FiniteMap α β)
    (ns xs : List α) (vs : List β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVar l) l1)
    (h : xs.mapM (FLOOKUP l) = some vs)
    (hx : ∀ x, x ∈ xs → x ∉ ns) :
    xs.mapM (FLOOKUP l1) = some vs := by
  have hpt : ∀ x, x ∈ xs → FLOOKUP l1 x = FLOOKUP l x := by
    intro x hxmem
    obtain ⟨y, hy⟩ := (OPT_MMAP_SOME_ALL (FLOOKUP l) xs).mp ⟨vs, h⟩ x hxmem
    have hfl : FLOOKUP l1 x = some y :=
      FOLDL_res_var_ZIP_lookup_var l l' l1 ns x y hsub hy (hx x hxmem)
    rw [hfl, hy]
  rw [OPT_MMAP_ALL_EQ (FLOOKUP l1) (FLOOKUP l) xs hpt]
  exact h

/-! ## HOL-equality (`=`) forms of the `res_var` cluster

FLAPJACK-SPECIFIC (not exact HOL ports).  The HOL declarations below quantify
the key type freely and use propositional equality; `DecidableEq` is Lean's
encoding of HOL `=`, so the `FUPDATE_HOL`/`FDOMSUB_HOL`/`resVarHOL` forms below
remove the `BEq`/`LawfulBEq` side conditions of the production forms.  They are
still NOT exact HOL ports, because they quantify Lean's raw function carrier
`FiniteMap α β := α → Option β` (`Flapjack/FiniteMap/Basic.lean:19`), which
admits infinite-support inhabitants, whereas HOL `α |-> β` is finite-support.
`DecidableEq` alone does not repair that: the statements still range over
functions HOL cannot represent.  A faithful port must quantify
`HolFiniteMapExact α β` (`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean`),
which now provides `update`/`updateList`/`erase`/`resVar` and their lookup
lemmas; that port is tracked by bead `flapjack-pxn.18.3.7.1.3.1.1.3.1`.  The
`_hol` declarations are kept as untagged infrastructure only. -/

theorem submap_imp_fupdate_submap_hol {κ : Type} {β : Type} [DecidableEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FUPDATE_HOL f (x, y)) (FUPDATE_HOL g (x, y)) := by
  intro n v hn
  simp only [FUPDATE_HOL] at hn ⊢
  by_cases hxn : n = x
  · simp [hxn] at hn ⊢
    exact hn
  · simp [hxn] at hn ⊢
    exact h n v hn

theorem submap_imp_domsub_submap_hol {κ : Type} {β : Type} [DecidableEq κ]
    (f g : κ → Option β) (x : κ) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB_HOL f x) (FDOMSUB_HOL g x) := by
  intro n v hn
  simp only [FDOMSUB_HOL] at hn ⊢
  by_cases hxn : n = x
  · simp [hxn] at hn
  · simp [hxn] at hn ⊢
    exact h n v hn

theorem submap_imp_domsub_fupdate_hol {κ : Type} {β : Type} [DecidableEq κ]
    (f g : κ → Option β) (x : κ) (y : β) (h : crepHolSubmap f g) :
    crepHolSubmap (FDOMSUB_HOL f x) (FUPDATE_HOL g (x, y)) := by
  intro n v hn
  simp only [FDOMSUB_HOL, FUPDATE_HOL] at hn ⊢
  by_cases hxn : n = x
  · simp [hxn] at hn
  · simp [hxn] at hn ⊢
    exact h n v hn

theorem res_var_commutes_strong_hol {α : Type} {β : Type} [DecidableEq α]
    (lc lc' : FiniteMap α β) (n h : α) :
    resVarHOL (resVarHOL lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
      resVarHOL (resVarHOL lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  by_cases hne : n = h
  · subst hne
    rfl
  · exact resVarHOL_commutes lc lc' n h hne

theorem res_var_foldl_commutes_strong_hol {α : Type} {β : Type} [DecidableEq α]
    (h : α) (vs : List α) (lc1 lc2 : FiniteMap α β) :
    resVarHOL ((vs.zip (vs.map (FLOOKUP lc2))).foldl resVarHOL lc1)
        (h, FLOOKUP lc2 h) =
      (vs.zip (vs.map (FLOOKUP lc2))).foldl resVarHOL
        (resVarHOL lc1 (h, FLOOKUP lc2 h)) := by
  induction vs generalizing lc1 with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih (resVarHOL lc1 (v, FLOOKUP lc2 v)),
        (res_var_commutes_strong_hol lc1 lc2 v h).symm]

theorem flookup_res_var_is_mem_zip_eq_hol {α : Type} {β : Type} [DecidableEq α]
    (xs : List α) (x : α) (lc1 lc2 : FiniteMap α β) (hx : x ∈ xs) :
    FLOOKUP ((xs.zip (xs.map (FLOOKUP lc2))).foldl resVarHOL lc1) x =
      FLOOKUP lc2 x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [← res_var_foldl_commutes_strong_hol a as lc1 lc2, FLOOKUP_resVarHOL]
      rcases List.mem_cons.mp hx with hxa | hxas
      · subst hxa
        simp
      · by_cases hxea : x = a
        · subst hxea
          simp
        · rw [if_neg hxea]
          exact ih hxas

theorem foldl_res_var_zip_lookup_var_hol {α : Type} {β : Type} [DecidableEq α]
    (l l' l1 : FiniteMap α β) (ns : List α) (x : α) (v : β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVarHOL l) l1)
    (hv : FLOOKUP l x = some v) (hx : x ∉ ns) :
    FLOOKUP l1 x = some v := by
  apply hsub x v
  change FLOOKUP ((ns.zip (ns.map (FLOOKUP l'))).foldl resVarHOL l) x = some v
  rw [FLOOKUP_foldl_resVarHOL_zip_not_mem ns (ns.map (FLOOKUP l')) l x
    (by simp [List.length_map]) hx]
  exact hv

theorem foldl_res_var_zip_lookup_hol {α : Type} {β : Type} [DecidableEq α]
    (l l' l1 : FiniteMap α β) (ns xs : List α) (vs : List β)
    (hsub : crepHolSubmap ((ns.zip (ns.map (FLOOKUP l'))).foldl resVarHOL l) l1)
    (h : xs.mapM (FLOOKUP l) = some vs)
    (hx : ∀ x, x ∈ xs → x ∉ ns) :
    xs.mapM (FLOOKUP l1) = some vs := by
  have hpt : ∀ x, x ∈ xs → FLOOKUP l1 x = FLOOKUP l x := by
    intro x hxmem
    obtain ⟨y, hy⟩ := (OPT_MMAP_SOME_ALL (FLOOKUP l) xs).mp ⟨vs, h⟩ x hxmem
    have hfl : FLOOKUP l1 x = some y :=
      foldl_res_var_zip_lookup_var_hol l l' l1 ns x y hsub hy (hx x hxmem)
    rw [hfl, hy]
  rw [OPT_MMAP_ALL_EQ (FLOOKUP l1) (FLOOKUP l) xs hpt]
  exact h

/-! ## Exact finite-support (`HolFiniteMapExact`) forms of the `SUBMAP` cluster

The `_hol` statements above still quantify Lean's raw function carrier
`FiniteMap α β := α → Option β`, which admits infinite-support inhabitants that
HOL `α |-> β` cannot represent.  The declarations below state the same HOL
clauses (`crep_inlineProofScript.sml:117/127/135`) over the canonical
finite-support carrier `HolFiniteMapExact`
(`Flapjack/Pancake/Semantics/CrepSem/HOLState.lean`) with its HOL-equality
(`DecidableEq`) `updateEq`/`eraseEq`, so they carry the exact HOL statements
with no `BEq`/`LawfulBEq` side conditions.  `submap` is untagged
infrastructure: HOL's `SUBMAP` is a finite-map operation defined in
`fmapScript`, not a declaration of `crep_inlineProofScript.sml`. -/

namespace HolFiniteMapExact

/-- HOL finite-map `SUBMAP` on the canonical finite-support carrier: every
    binding of `f` is also a binding of `g` with the same value, i.e. `FLOOKUP f`
    and `FLOOKUP g` agree on `FDOM f`. -/
def submap (f g : HolFiniteMapExact α β) : Prop :=
  ∀ key value, f.lookup key = some value → g.lookup key = some value

end HolFiniteMapExact

/-- Finite-map `SUBMAP_IMP_FUPDATE_SUBMAP`
    (`crep_inlineProofScript.sml:117`) over the exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_FUPDATE_SUBMAP"
  (fmap_as_finite_support_relation := [f, g])]
theorem submap_imp_fupdate_submap_exact {κ : Type} {β : Type} [DecidableEq κ]
    (f : HolFiniteMapExact κ β) (g : HolFiniteMapExact κ β) (x : κ) (y : β) (h : f.submap g) :
    (f.updateEq (x, y)).submap (g.updateEq (x, y)) := by
  intro n v hn
  rw [HolFiniteMapExact.lookup_updateEq] at hn ⊢
  simp only [FUPDATE_HOL] at hn ⊢
  by_cases hxn : n = x
  · rw [if_pos hxn] at hn ⊢
    exact hn
  · rw [if_neg hxn] at hn ⊢
    exact h n v hn

/-- Finite-map `SUBMAP_IMP_DOMSUB_SUBMAP`
    (`crep_inlineProofScript.sml:127`) over the exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_DOMSUB_SUBMAP"
  (fmap_as_finite_support_relation := [f, g])]
theorem submap_imp_domsub_submap_exact {κ : Type} {β : Type} [DecidableEq κ]
    (f : HolFiniteMapExact κ β) (g : HolFiniteMapExact κ β) (x : κ) (h : f.submap g) :
    (f.eraseEq x).submap (g.eraseEq x) := by
  intro n v hn
  rw [HolFiniteMapExact.lookup_eraseEq] at hn ⊢
  simp only [FDOMSUB_HOL] at hn ⊢
  by_cases hnx : n = x
  · rw [if_pos hnx] at hn ⊢
    exact hn
  · rw [if_neg hnx] at hn ⊢
    exact h n v hn

/-- Finite-map `SUBMAP_IMP_DOMSUB_FUPDATE`
    (`crep_inlineProofScript.sml:135`) over the exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "SUBMAP_IMP_DOMSUB_FUPDATE"
  (fmap_as_finite_support_relation := [f, g])]
theorem submap_imp_domsub_fupdate_exact {κ : Type} {β : Type} [DecidableEq κ]
    (f : HolFiniteMapExact κ β) (g : HolFiniteMapExact κ β) (x : κ) (y : β) (h : f.submap g) :
    (f.eraseEq x).submap (g.updateEq (x, y)) := by
  intro n v hn
  rw [HolFiniteMapExact.lookup_eraseEq] at hn
  rw [HolFiniteMapExact.lookup_updateEq]
  simp only [FDOMSUB_HOL, FUPDATE_HOL] at hn ⊢
  by_cases hnx : n = x
  · rw [if_pos hnx] at hn ⊢
    exact absurd hn (by simp)
  · rw [if_neg hnx] at hn ⊢
    exact h n v hn

/-! ## Exact finite-support (`HolFiniteMapExact`) forms of the `res_var` cluster

The `_hol` statements above still quantify Lean's raw function carrier
`FiniteMap α β := α → Option β`, which admits infinite-support inhabitants that
HOL `α |-> β` cannot represent.  The declarations below state the same HOL
clauses (`crep_inlineProofScript.sml:699/706/802/2661/2675`) over the canonical
finite-support carrier `HolFiniteMapExact` with its HOL-equality
(`DecidableEq`) `resVarEq`, so they carry the exact HOL statements with no
`BEq`/`LawfulBEq` side conditions.  The two bridges `resVarEq_lookup` and
`foldl_resVarEq_lookup` are untagged Flapjack infrastructure: they only relate
the exact carrier's lookup to HOL's raw `res_var` map operation. -/

open HolFiniteMapExact

/-- Flapjack-only bridge: the lookup of the exact `resVarEq` is HOL's raw-map
    `res_var` applied to the underlying lookup function. -/
theorem resVarEq_lookup [DecidableEq α] (map : HolFiniteMapExact α β)
    (entry : α × Option β) : (resVarEq map entry).lookup = resVarHOL map.lookup entry := by
  obtain ⟨key, value⟩ := entry
  cases value <;> rfl

/-- Flapjack-only bridge: folding the exact `resVarEq` over a list of entries is
    folding HOL's raw-map `res_var` over the underlying lookup function. -/
theorem foldl_resVarEq_lookup [DecidableEq α] (entries : List (α × Option β))
    (f : HolFiniteMapExact α β) :
    (entries.foldl resVarEq f).lookup = entries.foldl resVarHOL f.lookup := by
  induction entries generalizing f with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.foldl_cons]
      rw [ih, resVarEq_lookup]

/-- HOL `res_var_commutes_strong` (`crep_inlineProofScript.sml:699`) over the
    exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "res_var_commutes_strong"
  (fmap_as_finite_support_relation := [lc, lc'])]
theorem res_var_commutes_strong_exact {α : Type} {β : Type} [DecidableEq α]
    (lc : HolFiniteMapExact α β) (lc' : HolFiniteMapExact α β) (n h : α) :
    resVarEq (resVarEq lc (h, lc'.lookup h)) (n, lc'.lookup n) =
      resVarEq (resVarEq lc (n, lc'.lookup n)) (h, lc'.lookup h) := by
  by_cases hne : n = h
  · subst hne
    rfl
  · apply HolFiniteMapExact.ext
    simp only [resVarEq_lookup]
    exact resVarHOL_commutes lc.lookup lc'.lookup n h hne

/-- HOL `res_var_foldl_commutes_strong` (`crep_inlineProofScript.sml:706`) over
    the exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "res_var_foldl_commutes_strong"
  (fmap_as_finite_support_relation := [lc1, lc2])]
theorem res_var_foldl_commutes_strong_exact {α : Type} {β : Type} [DecidableEq α]
    (h : α) (vs : List α) (lc1 : HolFiniteMapExact α β) (lc2 : HolFiniteMapExact α β) :
    resVarEq ((vs.zip (vs.map (fun x => lc2.lookup x))).foldl resVarEq lc1)
        (h, lc2.lookup h) =
      (vs.zip (vs.map (fun x => lc2.lookup x))).foldl resVarEq
        (resVarEq lc1 (h, lc2.lookup h)) := by
  induction vs generalizing lc1 with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih (resVarEq lc1 (v, lc2.lookup v)),
        res_var_commutes_strong_exact lc1 lc2 v h]

/-- HOL `flookup_res_var_is_mem_zip_eq` (`crep_inlineProofScript.sml:802`) over
    the exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "flookup_res_var_is_mem_zip_eq"
  (fmap_as_finite_support_relation := [lc1, lc2])]
theorem flookup_res_var_is_mem_zip_eq_exact {α : Type} {β : Type} [DecidableEq α]
    (xs : List α) (x : α) (lc1 : HolFiniteMapExact α β) (lc2 : HolFiniteMapExact α β)
    (hx : x ∈ xs) :
    ((xs.zip (xs.map (fun y => lc2.lookup y))).foldl resVarEq lc1).lookup x = lc2.lookup x := by
  rw [foldl_resVarEq_lookup]
  exact flookup_res_var_is_mem_zip_eq_hol xs x lc1.lookup lc2.lookup hx

/-- HOL `FOLDL_res_var_ZIP_lookup_var` (`crep_inlineProofScript.sml:2661`) over
    the exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FOLDL_res_var_ZIP_lookup_var"
  (fmap_as_finite_support_relation := [l, l', l1])]
theorem foldl_res_var_zip_lookup_var_exact {α : Type} {β : Type} [DecidableEq α]
    (l : HolFiniteMapExact α β) (l' : HolFiniteMapExact α β) (l1 : HolFiniteMapExact α β)
    (ns : List α) (x : α) (v : β)
    (hsub : ((ns.zip (ns.map (fun y => l'.lookup y))).foldl resVarEq l).submap l1)
    (hv : l.lookup x = some v) (hx : x ∉ ns) :
    l1.lookup x = some v := by
  exact foldl_res_var_zip_lookup_var_hol l.lookup l'.lookup l1.lookup ns x v
    (fun n w hw => hsub n w (by rwa [foldl_resVarEq_lookup])) hv hx

/-- HOL `FOLDL_res_var_ZIP_lookup` (`crep_inlineProofScript.sml:2675`) over the
    exact finite-support carrier. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "FOLDL_res_var_ZIP_lookup"
  (fmap_as_finite_support_relation := [l, l', l1])]
theorem foldl_res_var_zip_lookup_exact {α : Type} {β : Type} [DecidableEq α]
    (l : HolFiniteMapExact α β) (l' : HolFiniteMapExact α β) (l1 : HolFiniteMapExact α β)
    (ns xs : List α) (vs : List β)
    (hsub : ((ns.zip (ns.map (fun y => l'.lookup y))).foldl resVarEq l).submap l1)
    (h : xs.mapM (fun x => l.lookup x) = some vs)
    (hx : ∀ x, x ∈ xs → x ∉ ns) :
    xs.mapM (fun x => l1.lookup x) = some vs := by
  have hpt : ∀ x, x ∈ xs → l1.lookup x = l.lookup x := by
    intro x hxmem
    obtain ⟨y, hy⟩ := (OPT_MMAP_SOME_ALL (fun x => l.lookup x) xs).mp ⟨vs, h⟩ x hxmem
    have hfl : l1.lookup x = some y :=
      foldl_res_var_zip_lookup_var_exact l l' l1 ns x y hsub hy (hx x hxmem)
    rw [hfl, hy]
  rw [OPT_MMAP_ALL_EQ (fun x => l1.lookup x) (fun x => l.lookup x) xs hpt]
  exact h

/-- CakeML's `locals_rel` (`crep_inlineProofScript.sml:26`):
    `s.locals SUBMAP t.locals`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsRelW below.
def crepInlineLocalsRel (s t : CrepHolState α σ) : Prop :=
  crepHolSubmap s.locals t.locals

/-- CakeML's `locals_strong_rel` (`crep_inlineProofScript.sml:31`):
    `s.locals = t.locals`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsStrongRelW below.
def crepInlineLocalsStrongRel (s t : CrepHolState α σ) : Prop :=
  s.locals = t.locals

/-- CakeML's `locals_rel_dec_clock` (`crep_inlineProofScript.sml:167`): both
    relations are preserved by `dec_clock`, since only `clock` changes. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsRel_decClockW below.
theorem crepInlineLocalsRel_decClock (s t : CrepHolState α σ)
    (hlocals : crepInlineLocalsRel s t) (hstate : crepInlineStateRel s t) :
    crepInlineLocalsRel (decCrepHolClock s) (decCrepHolClock t) ∧
    crepInlineStateRel (decCrepHolClock s) (decCrepHolClock t) := by
  obtain ⟨hg, hc, hm, hma, hsm, hcl, hbe, hf, hba, hta⟩ := hstate
  refine ⟨?_, ?_⟩
  · simpa only [crepInlineLocalsRel, decCrepHolClock] using hlocals
  · simp only [crepInlineStateRel, decCrepHolClock]
    exact ⟨hg, hc, hm, hma, hsm, by rw [hcl], hbe, hf, hba, hta⟩

/-- Finite-map `FDOM` for Lean's extensional lookup-function representation:
    the predicate holding exactly at the bound keys.  HOL's `FDOM` is a
    finite set; membership `n ∈ FDOM f` is `FLOOKUP f n ≠ NONE`, which is this
    Boolean test.  The key type is arbitrary so the same definition covers both
    `locals` (`Nat` keys) and `code` (`mlstring` keys).  Untagged
    infrastructure: HOL's `FDOM` is a finite-map operation, not a declaration of
    `crep_inlineProofScript.sml`. -/
def crepHolFdom {κ : Type} (f : κ → Option β) : κ → Bool :=
  fun n => (f n).isSome

/-- Finite-map `FDIFF` for Lean's extensional lookup-function representation:
    drop every key selected by `s`.  HOL's `FDIFF f s` restricts `f` to the
    complement of `s`; state membership as a Boolean predicate so the
    operation is executable.  Untagged infrastructure. -/
def crepHolFdiff (f : Nat → Option β) (s : Nat → Bool) : Nat → Option β :=
  fun n => if s n then none else f n

/-- CakeML's `locals_ext_rel` (`crep_inlineProofScript.sml:162`): the locals
    added when running from `a` to `a'` equal those added from `b` to `b'`,
    i.e. `FDIFF a'.locals (FDOM a.locals) = FDIFF b'.locals (FDOM b.locals)`.
    `crepHolFdiff`/`crepHolFdom` render HOL's `FDIFF`/`FDOM` extensionally. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineLocalsExtRelW below.
def crepInlineLocalsExtRel (a b a' b' : CrepHolState α σ) : Prop :=
  crepHolFdiff a'.locals (crepHolFdom a.locals) =
    crepHolFdiff b'.locals (crepHolFdom b.locals)

/-- CakeML's `state_rel_code` (`crep_inlineProofScript.sml:1442`): `state_rel`
    without the `code` conjunct, used by the inlining simulation because
    inlining changes `code` but preserves the rest of the state. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type, while HOL
-- crepSem$state is indexed by the word length. The exact width-indexed tag is on
-- crepInlineStateRelCodeW below.
def crepInlineStateRelCode (s t : CrepHolState α σ) : Prop :=
  s.globals = t.globals ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.bigEndian = t.bigEndian ∧
  s.ffi = t.ffi ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress

/-- Dropping the whole `FDOM` leaves the empty map. -/
theorem crepHolFdiff_fdom_self (f : Nat → Option β) :
    crepHolFdiff f (crepHolFdom f) = fun _ => none := by
  funext n
  cases h : f n <;> simp [crepHolFdiff, crepHolFdom, h]

/-- `locals_ext_rel` holds when both runs add nothing to their locals. -/
theorem crepInlineLocalsExtRel_self (a b : CrepHolState α σ) :
    crepInlineLocalsExtRel a b a b := by
  simp only [crepInlineLocalsExtRel]
  rw [crepHolFdiff_fdom_self a.locals, crepHolFdiff_fdom_self b.locals]

/-- Finite-map form of Cake `crep_inline$code_inl_rel`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1504-1511`):

    `code_inl_rel inl_fs s t ⇔
       ∀fname args prog. FLOOKUP s.code fname = SOME (args, prog) ⇒
         ∃inl_bag. inl_bag SUBMAP inl_fs ∧
                  FLOOKUP t.code fname = SOME (args, inline_prog inl_bag prog)`

    `CrepInlineFmap.lookup`/`remove`/`submap` mirror HOL
    `FLOOKUP`/`DOMSUB`/`SUBMAP` and `crepInlineProgFmap` is the exact
    `inline_prog` port (see `Flapjack/Pancake/CrepInline/Pass.lean`).  The map
    carrier is a duplicate-free finite map (an entry list carrying a
    duplicate-free key invariant, so `card` equals the domain cardinality)
    rather than HOL's sptree, so no `@[hol]` tag is attached; the statement
    otherwise follows the source clause for clause. -/
def crepInlineCodeInlRel [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inl_fs : CrepInlineFmap α) (s t : CrepHolState α σ) : Prop :=
  ∀ fname args prog, s.code fname = some (args, prog) →
    ∃ inl_bag : CrepInlineFmap α,
      CrepInlineFmap.submap inl_bag inl_fs ∧
      t.code fname = some (args, crepInlineProgFmap inl_bag prog)

/-- Introduction rule with the witness `inl_bag := inl_fs`. -/
theorem crepInlineCodeInlRel_of_code [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inl_fs : CrepInlineFmap α) (s t : CrepHolState α σ)
    (h : ∀ fname args prog, s.code fname = some (args, prog) →
      t.code fname = some (args, crepInlineProgFmap inl_fs prog)) :
    crepInlineCodeInlRel inl_fs s t := by
  intro fname args prog hcode
  exact ⟨inl_fs, CrepInlineFmap.submap_refl inl_fs, h fname args prog hcode⟩

/-- A source binding with no target binding refutes the relation. -/
theorem not_crepInlineCodeInlRel_of_target_none
    [BEq FunName] [LawfulBEq FunName] [OfNat α 0] [OfNat α 1]
    (inl_fs : CrepInlineFmap α) (s t : CrepHolState α σ)
    (fname : FunName) (args : List Nat) (prog : CrepProg α)
    (hcode : s.code fname = some (args, prog)) (hnone : t.code fname = none) :
    ¬ crepInlineCodeInlRel inl_fs s t := by
  intro h
  obtain ⟨_bag, _hsub, htarget⟩ := h fname args prog hcode
  rw [hnone] at htarget
  simp at htarget

/-! ## Expression-evaluation invariance under the inline state relations

    These are the Lean counterparts of Cake's
    `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`),
    `eval_state_locals_same_code_fdom_same` (:1467) and `eval_code_inl` (:1513).

    Exactness caveat: the source evaluator `crepSem$eval` is polymorphic in the
    word type, while the Lean evaluator `evalCrepHolExp`
    (`Flapjack/Pancake/Semantics/CrepSem/Eval.lean`) is only defined for the
    concrete `RiscV.Word width` carrier (`[NeZero width]`) and is itself
    untagged; `crepHolFdom` renders `FDOM` as an extensional Boolean predicate
    rather than a HOL finite set; and `crepInlineCodeInlRel`'s bearer is the
    unique-key entry-list finite map.  So no `@[hol]` tag is attached even
    though the statements otherwise follow the source clause for clause. -/

/-- CakeML's `fdom_subset_flookup_thm` (`crep_inlineProofScript.sml:1456`):
    `FDOM f ⊆ FDOM g` is exactly "every binding of `f` has a binding of `g` at
    the same key".  Stated for an arbitrary key type since both `locals` and
    `code` are finite maps. -/
theorem crepHolFdom_subset_flookup {κ : Type} (f g : κ → Option β) :
    (∀ n, crepHolFdom f n = true → crepHolFdom g n = true) ↔
      (∀ n p, f n = some p → ∃ q, g n = some q) := by
  constructor
  · intro h n p hp
    exact Option.isSome_iff_exists.mp (h n (by simp [crepHolFdom, hp]))
  · intro h n hn
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨q, hq⟩ := h n p hp
    simp [crepHolFdom, hq]

/-- CakeML's `eval_code_inl` FDOM extraction: `code_inl_rel inl_fs s t` puts
    every key bound in `s.code` into `t.code`, so `FDOM s.code ⊆ FDOM t.code`.
    This is the hypothesis consumed by the expression-evaluation invariance
    below. -/
theorem crepInlineCodeInlRel_fdom_subset
    [BEq FunName] [LawfulBEq FunName]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    (inlFs : CrepInlineFmap (RiscV.Word width))
    (s t : CrepHolState (RiscV.Word width) σ)
    (hcode : crepInlineCodeInlRel inlFs s t) :
    ∀ n, crepHolFdom s.code n = true → crepHolFdom t.code n = true := by
  intro n hn
  obtain ⟨⟨args, prog⟩, hlookup⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨_inlBag, _hsub, htcode⟩ := hcode n args prog hlookup
  simp [crepHolFdom, htcode]

/-- CakeML's `eval_state_locals_same_code_fdom_same`
    (`crep_inlineProofScript.sml:1467`): expression evaluation depends only on
    the locals and the `state_rel_code` fields, never on `code`, so any two
    states related by `state_rel_code` with equal locals evaluate every
    expression identically.  The `FDOM` subset hypothesis is carried to match
    the HOL statement but is not needed, since `eval` never reads `code`. -/
theorem evalCrepHolExp_state_rel_code [NeZero width]
    (s t : CrepHolState (RiscV.Word width) σ) (e : CrepExp (RiscV.Word width))
    (hstate : crepInlineStateRelCode s t)
    (hlocals : crepInlineLocalsStrongRel s t)
    (_hcode : ∀ n, crepHolFdom s.code n = true → crepHolFdom t.code n = true) :
    evalCrepHolExp s e = evalCrepHolExp t e := by
  obtain ⟨hg, hm, hma, _hsm, _hcl, hbe, _hf, hba, hta⟩ := hstate
  have hloc : s.locals = t.locals := hlocals
  induction e using evalCrepHolExp.induct with
  | case1 value => simp only [evalCrepHolExp]
  | case2 name => simp only [evalCrepHolExp, hloc]
  | case3 address ih => simp only [evalCrepHolExp, ih, hm, hma]
  | case4 address ih => simp only [evalCrepHolExp, ih, hm, hma, hbe, crepHolEvalMemLoad32]
  | case5 address ih => simp only [evalCrepHolExp, ih, hm, hma, hbe, crepHolEvalMemLoadByte]
  | case6 address => simp only [evalCrepHolExp, hg]
  | case7 operator expressions ih =>
      simp only [evalCrepHolExp]
      have hmap : List.mapM (evalCrepHolExp s) expressions
          = List.mapM (evalCrepHolExp t) expressions := by
        induction expressions with
        | nil => simp
        | cons x xs ihxs =>
            have htail : List.mapM (evalCrepHolExp s) xs
                = List.mapM (evalCrepHolExp t) xs :=
              ihxs (fun y hy => ih y (by simp [hy]))
            simp only [List.mapM_cons, ih x (by simp), htail]
      rw [hmap]
  | case8 left right ihl ihr => simp only [evalCrepHolExp, ihl, ihr]
  | case9 operator args h => simp only [evalCrepHolExp]
  | case10 operator left right ihl ihr => simp only [evalCrepHolExp, ihl, ihr]
  | case11 operator left right ihl ihr => simp only [evalCrepHolExp, ihl, ihr]
  | case12 => simp only [evalCrepHolExp, hba]
  | case13 => simp only [evalCrepHolExp, hta]

/-- CakeML's `eval_code_inl` (`crep_inlineProofScript.sml:1513`): if `s` and `t`
    are related by `state_rel_code` with equal locals and `t`'s code inlines
    `s`'s code along `inl_fs`, then every expression `s` evaluates to, `t`
    evaluates to as well. -/
theorem crepInlineEvalCodeInl [NeZero width] [BEq FunName] [LawfulBEq FunName]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    (s t : CrepHolState (RiscV.Word width) σ) (e : CrepExp (RiscV.Word width))
    (value : RiscV.Word width) (inlFs : CrepInlineFmap (RiscV.Word width))
    (heval : evalCrepHolExp s e = some value)
    (hstate : crepInlineStateRelCode s t)
    (hlocals : crepInlineLocalsStrongRel s t)
    (hcode : crepInlineCodeInlRel inlFs s t) :
    evalCrepHolExp t e = some value := by
  have hsubset := crepInlineCodeInlRel_fdom_subset inlFs s t hcode
  rw [← heval]
  exact (evalCrepHolExp_state_rel_code s t e hstate hlocals hsubset).symm

/-- List-level option-map congruence (the `l1 = l2` case of CakeML's
    `OPT_MMAP_CONG`, `cakeml/misc/miscScript.sml:2481`): pointwise equal
    evaluators give equal `OPT_MMAP`/`mapM` results.  Untagged because the Lean
    evaluator is the fixed-width `evalCrepHolExp` and `mapM` is the
    `List.mapM` carrier rather than HOL `OPT_MMAP`. -/
theorem crepOptMmapEvalCongr [NeZero width]
    (s t : CrepHolState (RiscV.Word width) σ) (es : List (CrepExp (RiscV.Word width)))
    (h : ∀ e ∈ es, evalCrepHolExp s e = evalCrepHolExp t e) :
    es.mapM (evalCrepHolExp s) = es.mapM (evalCrepHolExp t) := by
  induction es with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- CakeML's `opt_mmap_mem_func` (`pan_commonPropsScript.sml:49`): every element
    of a list that `OPT_MMAP` maps to `SOME` is itself mapped to `SOME`. -/
theorem crepOptMmapMemFunc [NeZero width] (s : CrepHolState (RiscV.Word width) σ) :
    ∀ (es : List (CrepExp (RiscV.Word width))) (values : List (RiscV.Word width)),
      es.mapM (evalCrepHolExp s) = some values →
      ∀ e ∈ es, ∃ m, evalCrepHolExp s e = some m := by
  intro es
  induction es with
  | nil => intro values h e he; simp at he
  | cons x xs ih =>
      intro values h e he
      simp only [List.mapM_cons] at h
      cases hx : evalCrepHolExp s x with
      | none => simp [hx] at h
      | some v =>
          cases hxs : xs.mapM (evalCrepHolExp s) with
          | none => simp [hx, hxs] at h
          | some vs =>
              rw [List.mem_cons] at he
              rcases he with rfl | he
              · exact ⟨v, hx⟩
              · exact ih vs hxs e he

/-- CakeML's `opt_mmap_eval_code_inl` (`crep_inlineProofScript.sml:1530`): the
    `eval_code_inl` expression transfer lifted across a whole expression list,
    `OPT_MMAP (eval s) es = SOME vals` implies `OPT_MMAP (eval s1) es = SOME vals`
    under `state_rel_code`, `locals_strong_rel` and `code_inl_rel`.  Untagged:
    fixed-width `evalCrepHolExp`/`List.mapM` versus HOL's polymorphic `eval` and
    `OPT_MMAP`. -/
theorem crepInlineOptMmapEvalCodeInl [NeZero width] [BEq FunName] [LawfulBEq FunName]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    (s t : CrepHolState (RiscV.Word width) σ) (es : List (CrepExp (RiscV.Word width)))
    (values : List (RiscV.Word width)) (inlFs : CrepInlineFmap (RiscV.Word width))
    (heval : es.mapM (evalCrepHolExp s) = some values)
    (hstate : crepInlineStateRelCode s t)
    (hlocals : crepInlineLocalsStrongRel s t)
    (hcode : crepInlineCodeInlRel inlFs s t) :
    es.mapM (evalCrepHolExp t) = some values := by
  have hsubset := crepInlineCodeInlRel_fdom_subset inlFs s t hcode
  have hpoint : ∀ e ∈ es, evalCrepHolExp s e = evalCrepHolExp t e := by
    intro e he
    obtain ⟨m, hm⟩ := crepOptMmapMemFunc s es values heval e he
    have hse := evalCrepHolExp_state_rel_code s t e hstate hlocals hsubset
    rw [hm] at hse
    rw [hm]
    exact hse
  rw [← crepOptMmapEvalCongr s t es hpoint]
  exact heval

/-! ## Runtime `inline_prog_correct` Skip case

CakeML's `inline_prog_correct` (`crep_inlineProofScript.sml:2301`) is stated over
the clock-based `crepSem$evaluate`.  Lean currently has no port of that
evaluator over the 11-field `CrepHolState`; the closest production evaluator is
the fuel-bounded `evalCrepRuntimeResult` over the 14-field `CrepRuntimeState`.
The relations below are runtime projections of the reviewed `CrepHolState`
relations, and `crepInlineRuntimeSkip` proves the Skip constructor case: from a
source run it derives an existential target run and the post-state relations,
never assuming the target run.  Untagged, because the fuel-bounded evaluator is
not HOL's clock-based `evaluate`. -/

abbrev crepInlineRuntimeStateRelCode (s t : CrepRuntimeState α σ) : Prop :=
  crepInlineStateRelCode s.toHolState t.toHolState

abbrev crepInlineRuntimeLocalsStrongRel (s t : CrepRuntimeState α σ) : Prop :=
  s.locals = t.locals

abbrev crepInlineRuntimeCodeInlRel [BEq FunName] [LawfulBEq FunName]
    [OfNat α 0] [OfNat α 1]
    (inlFs : CrepInlineFmap α) (s t : CrepRuntimeState α σ) : Prop :=
  crepInlineCodeInlRel inlFs s.toHolState t.toHolState

theorem crepInlineRuntimeSkip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq FunName] [LawfulBEq FunName]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (s s' : CrepRuntimeState α σ) (t : CrepRuntimeState α σ)
    (inlFs : CrepInlineFmap α)
    (hsource : evalCrepRuntimeResult handler primitive (fuel + 1) s .skip =
      some (CrepRuntimeResult.normal, s'))
    (hstate : crepInlineRuntimeStateRelCode s t)
    (hlocals : crepInlineRuntimeLocalsStrongRel s t)
    (hcode : crepInlineRuntimeCodeInlRel inlFs s t) :
    ∃ t',
      evalCrepRuntimeResult handler primitive (fuel + 1) t
          (crepInlineProgFmap inlFs .skip) = some (CrepRuntimeResult.normal, t') ∧
      crepInlineRuntimeStateRelCode s' t' ∧
      crepInlineRuntimeLocalsStrongRel s' t' ∧
      crepInlineRuntimeCodeInlRel inlFs s' t' := by
  have hskip := evalCrepRuntimeResult_skip handler primitive fuel s
  have hs' : s' = s := by
    have hq := hsource.symm.trans hskip
    exact congrArg Prod.snd (Option.some.inj hq)
  rw [hs', crepInlineProgFmap_skip inlFs]
  exact ⟨t, evalCrepRuntimeResult_skip handler primitive fuel t, hstate, hlocals, hcode⟩

/-! ## Width-indexed wrappers for the crep_inline state relations

HOL `crepSem$state` is indexed by the word length.  These `...W` helpers use
`CrepHolState (BitVec width) σ`, whose locals/globals/code are unrestricted
lookup functions rather than HOL finite maps, so the helpers stay untagged.
The exact finite-support relation ports required by the correctness path are
tracked under `flapjack-2de.13`. -/

/-- FLAPJACK-SPECIFIC: raw-function state relation; this declaration has no
    exact finite-support counterpart in this module yet. -/
def crepInlineStateRelW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineStateRel s t

/-- FLAPJACK-SPECIFIC: raw-function locals submap. -/
def crepInlineLocalsRelW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineLocalsRel s t

/-- FLAPJACK-SPECIFIC: raw-function locals equality; exact finite-support
    replacement is tracked under `flapjack-2de.13`. -/
def crepInlineLocalsStrongRelW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineLocalsStrongRel s t

/-- FLAPJACK-SPECIFIC: clock preservation over raw-function state carriers. -/
theorem crepInlineLocalsRel_decClockW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ)
    (hlocals : crepInlineLocalsRelW s t) (hstate : crepInlineStateRelW s t) :
    crepInlineLocalsRelW (decCrepHolClockW s) (decCrepHolClockW t) ∧
    crepInlineStateRelW (decCrepHolClockW s) (decCrepHolClockW t) := by
  have h := crepInlineLocalsRel_decClock s t hlocals hstate
  simpa only [crepInlineLocalsRelW, crepInlineStateRelW,
    decCrepHolClockW_eq_decCrepHolClock] using h

/-- FLAPJACK-SPECIFIC: locals extension relation over raw-function maps. -/
def crepInlineLocalsExtRelW {width : Nat} [NeZero width] {σ : Type}
    (a b a' b' : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineLocalsExtRel a b a' b'

/-- FLAPJACK-SPECIFIC: raw-function carrier relation; exact finite-support
    replacement is tracked under `flapjack-2de.13`. -/
def crepInlineStateRelCodeW {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepHolState (BitVec width) σ) : Prop :=
  crepInlineStateRelCode s t

/-! ## Exact finite-support inlining relations

The generic relations above are useful Flapjack infrastructure, but their
`CrepHolState` carrier has raw lookup functions for `locals`, `globals`, and
`code`, so it admits infinite-support states HOL cannot represent. These
relation ports instead use `CrepSemHOLState`; the finite-map qualifier is
backed by the local roundtrip witness below, and the word qualifier records
the reviewed positive-width `BitVec` carrier.
-/
namespace CrepInlineExact

/-- Same-module canonical witness for the finite-map qualifier on exact
CrepInline relations. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Carrier-specific alias for the multi-carrier qualifier on code_inl_rel.
This keeps the same-module witness named for the owning state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Canonical finite-support witness for `code_inl_rel_def`'s existential
`inl_bag`, including the lookup and support projections as well as the
`CrepInlineMapBroad` roundtrip. -/
theorem holFmapAsFiniteSupportExistentialWitness_crepInlineCodeInlRelExact_inl_bag
    {width : Nat} [NeZero width]
    (inl_bag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) :
    (CrepInlineCanonical.CrepInlineMapBroad.ofBroad
        (CrepInlineCanonical.CrepInlineMapBroad.toBroad inl_bag)).lookup =
        inl_bag.lookup ∧
      (CrepInlineCanonical.CrepInlineMapBroad.ofBroad
        (CrepInlineCanonical.CrepInlineMapBroad.toBroad inl_bag)).finiteSupport =
        inl_bag.finiteSupport ∧
      CrepInlineCanonical.CrepInlineMapBroad.ofBroad
        (CrepInlineCanonical.CrepInlineMapBroad.toBroad inl_bag) = inl_bag := by
  exact ⟨rfl, rfl,
    CrepInlineCanonical.CrepInlineMapBroad.ofBroad_toBroad inl_bag⟩

/-- Exact finite-support carrier port of CakeML's `state_rel` relation
(`crep_inlineProofScript.sml:12-24`). The ten compared fields are globals,
code, memory, both memory domains, clock, endianness, FFI state, and base/top
addresses; locals are intentionally excluded as in the HOL definition. The
quantified states use `CrepSemHOLState`, whose three finite maps are the
reviewed canonical translation of HOL's `|->` fields. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
def crepInlineStateRelExact {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) : Prop :=
  s.globals = t.globals ∧
  s.code = t.code ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  s.baseAddr = t.baseAddr ∧
  s.topAddr = t.topAddr

/-- Exact finite-support carrier port of CakeML's `locals_rel` relation
(`crep_inlineProofScript.sml:26-29`). This is HOL finite-map `SUBMAP`: every
binding in `s.locals` is present with the same value in `t.locals`. The
statement uses lookup on the finite-support map carrier and adds no key
decidability or `BEq` hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_def"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
def crepInlineLocalsRelExact {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) : Prop :=
  ∀ key value, s.locals.lookup key = some value → t.locals.lookup key = some value

/-- Exact finite-support carrier port of CakeML's `locals_ext_rel`
(`crep_inlineProofScript.sml:162-165`): the locals added when running from
`a` to `a'` equal those added from `b` to `b'`, i.e.
`FDIFF a'.locals (FDOM a.locals) = FDIFF b'.locals (FDOM b.locals)`.
`crepHolFdiff`/`crepHolFdom` render HOL's `FDIFF`/`FDOM` extensionally over
`CrepSemHOLState`'s finite-support `locals` field. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_ext_rel_def"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
def crepInlineLocalsExtRelExact {width : Nat} [NeZero width] {σ : Type}
    (a b a' b' : CrepSemHOLState width σ) : Prop :=
  crepHolFdiff a'.locals.lookup (crepHolFdom a.locals.lookup) =
    crepHolFdiff b'.locals.lookup (crepHolFdom b.locals.lookup)

/-- Exact finite-support carrier port of CakeML's `locals_rel_dec_clock`
(`crep_inlineProofScript.sml:167-173`): both relations are preserved by
`dec_clock`, since only `clock` changes. The conclusion is the source
conjunction of `locals_rel` and `state_rel` at the decremented clocks. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_dec_clock"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepInlineLocalsRel_decClockExact {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ)
    (h : crepInlineLocalsRelExact s t ∧ crepInlineStateRelExact s t) :
    crepInlineLocalsRelExact (decClockCrepSemHOL s) (decClockCrepSemHOL t) ∧
    crepInlineStateRelExact (decClockCrepSemHOL s) (decClockCrepSemHOL t) := by
  obtain ⟨hlocals, hstate⟩ := h
  obtain ⟨hg, hc, hm, hma, hsm, hcl, hbe, hf, hba, hta⟩ := hstate
  refine ⟨?_, ?_⟩
  · intro key value hlookup
    simpa only [decClockCrepSemHOL] using hlocals key value hlookup
  · simp only [crepInlineStateRelExact, decClockCrepSemHOL]
    exact ⟨hg, hc, hm, hma, hsm, by rw [hcl], hbe, hf, hba, hta⟩

/-- Exact finite-support carrier port of CakeML's `state_rel_code` relation:
globals, memory, memory domains, clock, endianness, FFI state, and base/top
addresses agree; locals and code are intentionally omitted as in HOL. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_code_def"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
def crepInlineStateRelCodeExact {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) : Prop :=
  s.globals = t.globals ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  s.baseAddr = t.baseAddr ∧
  s.topAddr = t.topAddr

/-- Exact finite-support carrier port of CakeML's `locals_strong_rel`: the
local finite maps are equal, without admitting arbitrary infinite-support
lookup functions. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_strong_rel_def"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
def crepInlineLocalsStrongRelExact {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) : Prop :=
  s.locals = t.locals

/-- HOL `code_inl_rel_def` (`crep_inlineProofScript.sml:1504-1511`) on the
canonical finite-map and state carriers. This keeps HOL's existential
`inl_bag` as a finite-support map and uses the reviewed `inlineProgHOLExact`
definition, with the source quantifiers and conclusion unchanged.

The relation qualifier records the three exact state maps and standalone
`inl_fs`; the existential-map qualifier records `inl_bag` and its canonical
lookup/support roundtrip; the word qualifier records the positive-width HOL
word model. The prior `crepInlineCodeInlRel` remains Flapjack-specific
list-backed infrastructure. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "code_inl_rel_def"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inl_fs])
  (fmap_as_finite_support_existentials := [inl_bag])
  (words_as_type_indexed_bitvec)]
def crepInlineCodeInlRelExact {width : Nat} [NeZero width] {σ : Type}
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (s t : CrepSemHOLState width σ) : Prop :=
  ∀ fname args prog, s.code.lookup fname = some (args, prog) →
    ∃ inl_bag : HolFiniteMapExact CrepInlineMapHOLName
        (List Nat × CrepProgHOL width),
      HolFiniteMapExact.submap inl_bag inl_fs ∧
      t.code.lookup fname = some
        (args, CrepInlineCanonical.inlineProgHOLExact inl_bag prog)

/-- Flapjack-only helper: expression evaluation on the exact state carrier is
insensitive to code. This is not a port of HOL's
`eval_state_locals_same_code_fdom_same`: this fixed-width Lean evaluator proves
equality of the complete `Option` results without assuming a successful source
evaluation, while HOL proves one-way preservation of a supplied successful
result for its polymorphic evaluator. The unused code-domain premise is kept
only to make the call site correspond to the premise needed by the HOL theorem;
the Lean evaluator itself does not read `code`. -/
theorem evalCrepSemHOLExp_state_rel_code_exact {width : Nat} [NeZero width]
    {σ : Type} (s t : CrepSemHOLState width σ) (e : CrepExpHOL width)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (_hcode : ∀ name, s.code.lookup name ≠ none → t.code.lookup name ≠ none) :
    evalCrepSemHOLExp s e = evalCrepSemHOLExp t e := by
  obtain ⟨hg, hm, hma, _hsm, _hclock, hbe, _hffi, hbase, htop⟩ := hstate
  have hloc : s.locals = t.locals := hlocals
  induction e using evalCrepSemHOLExp.induct with
  | case1 value => simp only [evalCrepSemHOLExp]
  | case2 name => simp only [evalCrepSemHOLExp, hloc]
  | case3 address ih =>
      simp [evalCrepSemHOLExp, ih, hm]
      rw [hma]
  | case4 address ih =>
      simp [evalCrepSemHOLExp, ih, hm, hbe, panMemLoad32HOL]
      rw [hma]
  | case5 address ih =>
      simp [evalCrepSemHOLExp, ih, hm, hbe, panMemLoadByteHOL]
      rw [hma]
  | case6 address => simp only [evalCrepSemHOLExp, hg]
  | case7 operator expressions ih =>
      simp only [evalCrepSemHOLExp]
      have hmap : expressions.mapM (evalCrepSemHOLExp s) =
          expressions.mapM (evalCrepSemHOLExp t) := by
        induction expressions with
        | nil => simp
        | cons x xs ihxs =>
            have htail : xs.mapM (evalCrepSemHOLExp s) =
                xs.mapM (evalCrepSemHOLExp t) :=
              ihxs (fun y hy => ih y (by simp [hy]))
            simp only [List.mapM_cons, ih x (by simp), htail]
      rw [hmap]
  | case8 operator expressions ih =>
      simp only [evalCrepSemHOLExp]
      have hmap : expressions.mapM (evalCrepSemHOLExp s) =
          expressions.mapM (evalCrepSemHOLExp t) := by
        induction expressions with
        | nil => simp
        | cons x xs ihxs =>
            have htail : xs.mapM (evalCrepSemHOLExp s) =
                xs.mapM (evalCrepSemHOLExp t) :=
              ihxs (fun y hy => ih y (by simp [hy]))
            simp only [List.mapM_cons, ih x (by simp), htail]
      rw [hmap]
  | case9 operator left right ihl ihr =>
      simp only [evalCrepSemHOLExp, ihl, ihr]
  | case10 operator left right ihl ihr =>
      simp only [evalCrepSemHOLExp, ihl, ihr]
  | case11 => simp only [evalCrepSemHOLExp, hbase]
  | case12 => simp only [evalCrepSemHOLExp, htop]

/-- Exact port of CakeML's `eval_code_inl` (`crep_inlineProofScript.sml:1513-1521`).
The four premises and successful target evaluation conclusion match HOL; the
intermediate finite-map domain inclusion is derived from `code_inl_rel`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "eval_code_inl"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inl_fs])
  (words_as_type_indexed_bitvec)]
theorem evalCodeInlExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
    (value : HolWordLab width) (t : CrepSemHOLState width σ)
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) :
    (evalCrepSemHOLExp s e = some value ∧
      crepInlineStateRelCodeExact s t ∧
      crepInlineLocalsStrongRelExact s t ∧
      crepInlineCodeInlRelExact inl_fs s t) →
    evalCrepSemHOLExp t e = some value := by
  intro h
  obtain ⟨heval, hstate, hlocals, hcode⟩ := h
  have hsubset : ∀ name, s.code.lookup name ≠ none → t.code.lookup name ≠ none := by
    intro name hsource
    cases hlookup : s.code.lookup name with
    | none => exact False.elim (hsource hlookup)
    | some entry =>
        rcases entry with ⟨args, prog⟩
        obtain ⟨_bag, _hsub, htarget⟩ := hcode name args prog hlookup
        rw [htarget]
        simp
  rw [← heval]
  exact (evalCrepSemHOLExp_state_rel_code_exact s t e hstate hlocals hsubset).symm

/-- Exact port of CakeML's `opt_mmap_eval_code_inl`
    (`crep_inlineProofScript.sml:1530-1540`). HOL's `OPT_MMAP` is Lean's
    `List.mapM` on the constructor-for-constructor `List` carriers, and the
    four premises and successful target-list conclusion are unchanged. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "opt_mmap_eval_code_inl"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inl_fs])
  (words_as_type_indexed_bitvec)]
theorem optMmapEvalCodeInlExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (expressions : List (CrepExpHOL width))
    (values : List (HolWordLab width)) (t : CrepSemHOLState width σ)
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width)) :
    (expressions.mapM (evalCrepSemHOLExp s) = some values ∧
      crepInlineStateRelCodeExact s t ∧
      crepInlineLocalsStrongRelExact s t ∧
      crepInlineCodeInlRelExact inl_fs s t) →
    expressions.mapM (evalCrepSemHOLExp t) = some values := by
  rintro ⟨heval, hstate, hlocals, hcode⟩
  induction expressions generalizing values with
  | nil =>
      simp only [List.mapM_nil] at heval ⊢
      cases heval
      rfl
  | cons expression expressions ih =>
      simp only [List.mapM_cons] at heval ⊢
      cases hhead : evalCrepSemHOLExp s expression with
      | none => simp [hhead] at heval
      | some value =>
          cases htail : expressions.mapM (evalCrepSemHOLExp s) with
          | none => simp [hhead, htail] at heval
          | some tailValues =>
              have hvalues : values = value :: tailValues := by
                simpa [hhead, htail] using heval.symm
              subst values
              have hheadTarget : evalCrepSemHOLExp t expression = some value :=
                evalCodeInlExact s expression value t inl_fs
                  ⟨hhead, hstate, hlocals, hcode⟩
              have htailTarget :
                  expressions.mapM (evalCrepSemHOLExp t) = some tailValues :=
                ih tailValues htail
              simp [hheadTarget, htailTarget]

/-! ## `inline_prog_correct` Dec constructor case

HOL crep_inlineProofScript.sml:2301 states the source run, non-Error result,
two SUBMAP premises, state_rel_code, locals_strong_rel, and code_inl_rel. Its
Dec induction case at lines 2360-2373 adds exactly the recursive body induction
hypothesis from `evaluate_ind`: after a successful expression evaluation, the
source is fixed to `setVar name value s`; only the theorem predicate's other
arguments (including the target state) remain quantified. This declaration
uses those same hypotheses and result-dependent postconditions. The relation
qualifier records the three finite-map state fields plus `inlFs`; the standalone
`inlBag` map has a canonical roundtrip witness. `words_as_type_indexed_bitvec`
records the positive HOL word width. -/

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectDecCaseExact {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.dec name value body) = (r, s'))
    (hnotError : r ≠ some .error)
    (hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t)
    (ih : ∀ (valueResult : HolWordLab width),
        crepExactEvalExpClassical s value = some valueResult →
        ∀ (result : Option (CrepResultHOLExact width))
          (source' : CrepSemHOLState width σ)
          (inlFs' : HolFiniteMapExact CrepInlineMapHOLName
          (List Nat × CrepProgHOL width))
        (target : CrepSemHOLState width σ)
        (inlBag' : HolFiniteMapExact CrepInlineMapHOLName
          (List Nat × CrepProgHOL width)),
        evalCrepSemHOLProgExact (CrepSemHOLState.setVar name valueResult s)
            body = (result, source') →
        result ≠ some .error →
        HolFiniteMapExact.submap inlFs' (CrepSemHOLState.setVar name valueResult s).code →
        HolFiniteMapExact.submap inlBag' inlFs' →
        crepInlineStateRelCodeExact (CrepSemHOLState.setVar name valueResult s) target →
        crepInlineLocalsStrongRelExact (CrepSemHOLState.setVar name valueResult s) target →
        crepInlineCodeInlRelExact inlFs' (CrepSemHOLState.setVar name valueResult s) target →
        ∃ target' : CrepSemHOLState width σ,
          evalCrepSemHOLProgExact target (CrepInlineCanonical.inlineProgHOLExact inlBag' body) =
            (result, target') ∧
          crepInlineStateRelCodeExact source' target' ∧
          crepInlineCodeInlRelExact inlFs' source' target' ∧
          match result with
          | none => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact source' target'
          | some .error => False
          | _ => True) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.dec name value body)) =
        (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_dec_holShape] at hsource
  cases hexp : evalCrepSemHOLExp s value with
  | none =>
      simp [hexp] at hsource
      exact False.elim (hnotError hsource.1.symm)
  | some v =>
      let sourceBound : CrepSemHOLState width σ :=
        { s with locals := s.locals.updateEq (name, v) }
      let targetBound : CrepSemHOLState width σ :=
        { t with locals := t.locals.updateEq (name, v) }
      have htargetExp : evalCrepSemHOLExp t value = some v := by
        apply evalCodeInlExact s value v t inlFs
        exact ⟨hexp, hstate, hlocals, hcode⟩
      simp only [hexp] at hsource
      cases hbody : evalCrepSemHOLProgExact sourceBound body with
      | mk result sourceBody' =>
          simp only [sourceBound, hbody, Prod.mk.injEq] at hsource
          rcases hsource with ⟨hr, hs'⟩
          subst r
          subst s'
          have hstateBound : crepInlineStateRelCodeExact sourceBound targetBound := by
            simpa [sourceBound, targetBound, CrepSemHOLState.setVar,
              crepInlineStateRelCodeExact] using hstate
          have hlocalsBound : crepInlineLocalsStrongRelExact sourceBound targetBound := by
            change sourceBound.locals = targetBound.locals
            simpa [sourceBound, targetBound, CrepSemHOLState.setVar] using
              congrArg (fun locals => locals.updateEq (name, v)) hlocals
          have hcodeBound : crepInlineCodeInlRelExact inlFs sourceBound targetBound := by
            simpa [sourceBound, targetBound, CrepSemHOLState.setVar,
              crepInlineCodeInlRelExact] using hcode
          have hvalueForIH : crepExactEvalExpClassical s value = some v := by
            rw [crepExactEvalExpClassical_eq]
            exact hexp
          have hsubmapBound : HolFiniteMapExact.submap inlFs sourceBound.code := by
            simpa [sourceBound, CrepSemHOLState.setVar] using hsubmap
          obtain ⟨targetBody', htargetBody, hstateBody, hcodeBody, hlocalsBody⟩ :=
            ih v hvalueForIH result sourceBody' inlFs targetBound inlBag hbody
              (by simpa [hbody] using hnotError) hsubmapBound hbag hstateBound
              hlocalsBound hcodeBound
          have hinlineDec :
              CrepInlineCanonical.inlineProgHOLExact inlBag (.dec name value body) =
                .dec name value (CrepInlineCanonical.inlineProgHOLExact inlBag body) := by
            unfold CrepInlineCanonical.inlineProgHOLExact
            simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
          have htargetRun :
              evalCrepSemHOLProgExact t
                (CrepInlineCanonical.inlineProgHOLExact inlBag (.dec name value body)) =
                (result, { targetBody' with
                  locals := targetBody'.locals.resVarEq (name, t.locals.lookup name) }) := by
            have htargetBody' :
                evalCrepSemHOLProgExact
                  { t with locals := t.locals.updateEq (name, v) }
                  (CrepInlineCanonical.inlineProgHOLExact inlBag body) =
                  (result, targetBody') := by
              simpa [targetBound] using htargetBody
            rw [hinlineDec, evalCrepSemHOLProgExact_dec_holShape]
            simp only [htargetExp]
            rw [htargetBody']
          have hstatePost :
              crepInlineStateRelCodeExact
                { sourceBody' with
                  locals := sourceBody'.locals.resVarEq (name, s.locals.lookup name) }
                { targetBody' with
                  locals := targetBody'.locals.resVarEq (name, t.locals.lookup name) } := by
            simpa [hbody, crepInlineStateRelCodeExact] using hstateBody
          have hcodePost :
              crepInlineCodeInlRelExact inlFs
                { sourceBody' with
                  locals := sourceBody'.locals.resVarEq (name, s.locals.lookup name) }
                { targetBody' with
                  locals := targetBody'.locals.resVarEq (name, t.locals.lookup name) } := by
            simpa [hbody, crepInlineCodeInlRelExact] using hcodeBody
          refine ⟨{ targetBody' with
              locals := targetBody'.locals.resVarEq (name, t.locals.lookup name) }, ?_,
            ?_, ?_, ?_⟩
          · simpa [hbody] using htargetRun
          · exact hstatePost
          · exact hcodePost
          · split <;> simp_all [crepInlineLocalsStrongRelExact]

/-! ## `inline_prog_correct` If constructor case

HOL `crep_inlineProofScript.sml:2301-2309` states the theorem; its If case at
2374-2381 is the `If` conjunct of the source-reviewed `crepSem$evaluate_ind`
at `crepSemScript.sml:440`. That conjunct contributes exactly one IH: after
the condition evaluates to a word, the theorem predicate for the selected
branch in the original fixed state `s`. The exact `CrepExpHOL`, `CrepProgHOL`, width-indexed
`CrepSemHOLState`, and `HolWordLab` carriers are the counterparts already
recorded by those datatype and evaluator tags. The relation qualifier records
the state maps and both inline maps; no premise or conclusion is weakened. -/

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectIfCaseExact {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width)
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (ih : ∀ (value : HolWordLab width) (word : BitVec width),
        crepExactEvalExpClassical s condition = some value →
        value = .word word →
        ∀ (result : Option (CrepResultHOLExact width))
          (source' : CrepSemHOLState width σ)
          (inlFs' : HolFiniteMapExact CrepInlineMapHOLName
              (List Nat × CrepProgHOL width))
          (target : CrepSemHOLState width σ)
          (inlBag' : HolFiniteMapExact CrepInlineMapHOLName
              (List Nat × CrepProgHOL width)),
          evalCrepSemHOLProgExact s
              (if word ≠ 0 then thenBranch else elseBranch) = (result, source') →
          result ≠ some .error →
          HolFiniteMapExact.submap inlFs' s.code →
          HolFiniteMapExact.submap inlBag' inlFs' →
          crepInlineStateRelCodeExact s target →
          crepInlineLocalsStrongRelExact s target →
          crepInlineCodeInlRelExact inlFs' s target →
          ∃ target' : CrepSemHOLState width σ,
            evalCrepSemHOLProgExact target
                (CrepInlineCanonical.inlineProgHOLExact inlBag'
                  (if word ≠ 0 then thenBranch else elseBranch)) =
              (result, target') ∧
            crepInlineStateRelCodeExact source' target' ∧
            crepInlineCodeInlRelExact inlFs' source' target' ∧
            match result with
            | none => crepInlineLocalsStrongRelExact source' target'
            | some (CrepResultHOLExact.break _) =>
                crepInlineLocalsStrongRelExact source' target'
            | some (CrepResultHOLExact.continue _) =>
                crepInlineLocalsStrongRelExact source' target'
            | some .error => False
            | _ => True)
    (r : Option (CrepResultHOLExact width))
    (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.ite condition thenBranch elseBranch) = (r, s'))
    (hnotError : r ≠ some .error)
    (hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.ite condition thenBranch elseBranch)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_ite_holShape] at hsource
  cases hcondition : evalCrepSemHOLExp s condition with
  | none =>
      simp [hcondition] at hsource
      have hresult : r = some .error := hsource.1.symm
      subst r
      exact False.elim (hnotError rfl)
  | some value =>
      cases value with
      | word word =>
          have hconditionIH :
              crepExactEvalExpClassical s condition = some (.word word) := by
            rw [crepExactEvalExpClassical_eq]
            exact hcondition
          have hsourceBranch :
              evalCrepSemHOLProgExact s
                  (if word ≠ 0 then thenBranch else elseBranch) = (r, s') := by
            simpa [hcondition] using hsource
          have htargetCondition :
              evalCrepSemHOLExp t condition = some (.word word) := by
            apply evalCodeInlExact s condition (.word word) t inlFs
            exact ⟨hcondition, hstate, hlocals, hcode⟩
          obtain ⟨t', htargetBranch, hstatePost, hcodePost, hlocalsPost⟩ :=
            ih (.word word) word hconditionIH rfl
              r s' inlFs t inlBag hsourceBranch hnotError
              hsubmap hbag hstate hlocals hcode
          have hinlineIf :
              CrepInlineCanonical.inlineProgHOLExact inlBag
                  (.ite condition thenBranch elseBranch) =
                .ite condition
                  (CrepInlineCanonical.inlineProgHOLExact inlBag thenBranch)
                  (CrepInlineCanonical.inlineProgHOLExact inlBag elseBranch) := by
            unfold CrepInlineCanonical.inlineProgHOLExact
            simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
          have hinlineSelected :
              CrepInlineCanonical.inlineProgHOLExact inlBag
                  (if word ≠ 0 then thenBranch else elseBranch) =
                if word ≠ 0 then
                  CrepInlineCanonical.inlineProgHOLExact inlBag thenBranch
                else CrepInlineCanonical.inlineProgHOLExact inlBag elseBranch := by
            by_cases hnz : word ≠ 0
            · simp only [if_pos hnz]
            · simp only [if_neg hnz]
          refine ⟨t', ?_, hstatePost, hcodePost, ?_⟩
          · calc
              evalCrepSemHOLProgExact t
                  (CrepInlineCanonical.inlineProgHOLExact inlBag
                    (.ite condition thenBranch elseBranch)) =
                  evalCrepSemHOLProgExact t
                    (.ite condition
                      (CrepInlineCanonical.inlineProgHOLExact inlBag thenBranch)
                      (CrepInlineCanonical.inlineProgHOLExact inlBag elseBranch)) := by
                    rw [hinlineIf]
              _ = evalCrepSemHOLProgExact t
                    (if word ≠ 0 then
                      CrepInlineCanonical.inlineProgHOLExact inlBag thenBranch
                     else CrepInlineCanonical.inlineProgHOLExact inlBag elseBranch) := by
                    rw [evalCrepSemHOLProgExact_ite_holShape, htargetCondition]
              _ = evalCrepSemHOLProgExact t
                    (CrepInlineCanonical.inlineProgHOLExact inlBag
                      (if word ≠ 0 then thenBranch else elseBranch)) := by
                    rw [← hinlineSelected]
              _ = (r, t') := htargetBranch
          · cases r with
            | none => simpa using hlocalsPost
            | some result => cases result <;> simp_all

/-! ## `inline_prog_correct` Seq constructor case

HOL `crep_inlineProofScript.sml:2383-2400` applies the `evaluate_ind` Seq
case: first the predicate for `first`, then the conditional predicate for
`second` when the first result is `NONE`. The case below keeps the theorem's
source evaluation, non-Error premise, finite-map submap premises, and all
three relations. Its only additional premises are those two induction
hypotheses. The exact `CrepSemHOLState` evaluator and `inlineProgHOLExact`
are used throughout. The state-code invariant used to carry `inlFs SUBMAP`
through a successful first command is the already tagged exact
`evaluate_code_invariant` port; HOL uses that same fact in this case.
-/

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectSeqCaseExact {width : Nat} [NeZero width] {σ : Type}
    (first second : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.seq first second) = (r, s'))
    (hnotError : r ≠ some .error)
    (hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t)
    (ihFirst : ∀ (result : Option (CrepResultHOLExact width))
        (source' : CrepSemHOLState width σ)
        (inlFs' : HolFiniteMapExact CrepInlineMapHOLName
          (List Nat × CrepProgHOL width))
        (target : CrepSemHOLState width σ)
        (inlBag' : HolFiniteMapExact CrepInlineMapHOLName
          (List Nat × CrepProgHOL width)),
        evalCrepSemHOLProgExact s first = (result, source') →
        result ≠ some .error →
        HolFiniteMapExact.submap inlFs' s.code →
        HolFiniteMapExact.submap inlBag' inlFs' →
        crepInlineStateRelCodeExact s target →
        crepInlineLocalsStrongRelExact s target →
        crepInlineCodeInlRelExact inlFs' s target →
        ∃ target' : CrepSemHOLState width σ,
          evalCrepSemHOLProgExact target
              (CrepInlineCanonical.inlineProgHOLExact inlBag' first) =
            (result, target') ∧
          crepInlineStateRelCodeExact source' target' ∧
          crepInlineCodeInlRelExact inlFs' source' target' ∧
          match result with
          | none => crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.break _) =>
              crepInlineLocalsStrongRelExact source' target'
          | some (CrepResultHOLExact.continue _) =>
              crepInlineLocalsStrongRelExact source' target'
          | some .error => False
          | _ => True)
    (ihSecond : ∀ (resultFirst : Option (CrepResultHOLExact width))
        (sourceFirst : CrepSemHOLState width σ),
        (resultFirst, sourceFirst) = evalCrepSemHOLProgExact s first →
        resultFirst = none →
        ∀ (result : Option (CrepResultHOLExact width))
          (source' : CrepSemHOLState width σ)
          (inlFs' : HolFiniteMapExact CrepInlineMapHOLName
            (List Nat × CrepProgHOL width))
          (target : CrepSemHOLState width σ)
          (inlBag' : HolFiniteMapExact CrepInlineMapHOLName
            (List Nat × CrepProgHOL width)),
          evalCrepSemHOLProgExact sourceFirst second = (result, source') →
          result ≠ some .error →
          HolFiniteMapExact.submap inlFs' sourceFirst.code →
          HolFiniteMapExact.submap inlBag' inlFs' →
          crepInlineStateRelCodeExact sourceFirst target →
          crepInlineLocalsStrongRelExact sourceFirst target →
          crepInlineCodeInlRelExact inlFs' sourceFirst target →
          ∃ target' : CrepSemHOLState width σ,
            evalCrepSemHOLProgExact target
                (CrepInlineCanonical.inlineProgHOLExact inlBag' second) =
              (result, target') ∧
            crepInlineStateRelCodeExact source' target' ∧
            crepInlineCodeInlRelExact inlFs' source' target' ∧
            match result with
            | none => crepInlineLocalsStrongRelExact source' target'
            | some (CrepResultHOLExact.break _) =>
                crepInlineLocalsStrongRelExact source' target'
            | some (CrepResultHOLExact.continue _) =>
                crepInlineLocalsStrongRelExact source' target'
            | some .error => False
            | _ => True) :
    ∃ target' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.seq first second)) = (r, target') ∧
      crepInlineStateRelCodeExact s' target' ∧
      crepInlineCodeInlRelExact inlFs s' target' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' target'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' target'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' target'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_seq_holShape] at hsource
  cases hfirst : evalCrepSemHOLProgExact s first with
  | mk resultFirst sourceFirst =>
      have hfirstRun :
          evalCrepSemHOLProgExact s first = (resultFirst, sourceFirst) := hfirst
      have hsourceCase :
          (if resultFirst = none then
            evalCrepSemHOLProgExact sourceFirst second
           else (resultFirst, sourceFirst)) = (r, s') := by
        simpa only [hfirst] using hsource
      by_cases hfirstNone : resultFirst = none
      · have hsourceSecond :
            evalCrepSemHOLProgExact sourceFirst second = (r, s') := by
          simpa [hfirstNone] using hsourceCase
        have hcodeInvariant :=
          evaluateCodeInvariantHOL first s resultFirst sourceFirst hfirstRun
        have hsubmapFirst : HolFiniteMapExact.submap inlFs sourceFirst.code := by
          intro key value hlookup
          have hlookup' := hsubmap key value hlookup
          simpa [hcodeInvariant] using hlookup'
        obtain ⟨targetFirst, htargetFirst, hstateFirst, hcodeFirst,
            hlocalsFirst⟩ :=
          ihFirst resultFirst sourceFirst inlFs t inlBag hfirstRun
            (by simp [hfirstNone]) hsubmap hbag hstate hlocals hcode
        simp [hfirstNone] at hlocalsFirst
        obtain ⟨targetFinal, htargetSecond, hstateFinal, hcodeFinal,
            hlocalsFinal⟩ :=
          ihSecond resultFirst sourceFirst hfirstRun.symm hfirstNone
            r s' inlFs targetFirst inlBag hsourceSecond hnotError hsubmapFirst hbag
            hstateFirst hlocalsFirst hcodeFirst
        have hinlineSeq :
            CrepInlineCanonical.inlineProgHOLExact inlBag
                (.seq first second) =
              .seq (CrepInlineCanonical.inlineProgHOLExact inlBag first)
                (CrepInlineCanonical.inlineProgHOLExact inlBag second) := by
          unfold CrepInlineCanonical.inlineProgHOLExact
          simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
        refine ⟨targetFinal, ?_, hstateFinal, hcodeFinal, ?_⟩
        rw [hinlineSeq, evalCrepSemHOLProgExact_seq_holShape, htargetFirst]
        · simpa [hfirstNone] using htargetSecond
        · cases r with
          | none => exact hlocalsFinal
          | some result => cases result <;> simp_all
      · have hsourcePair :
            (resultFirst, sourceFirst) = (r, s') := by
          simpa [hfirstNone] using hsourceCase
        clear hsource
        rcases Prod.mk.inj hsourcePair with ⟨hr, hs'⟩
        subst r
        subst s'
        clear hsourceCase hsourcePair
        obtain ⟨targetFirst, htargetFirst, hstateFirst, hcodeFirst,
            hlocalsFirst⟩ :=
          ihFirst resultFirst sourceFirst inlFs t inlBag hfirstRun hnotError
            hsubmap hbag hstate hlocals hcode
        have hinlineSeq :
            CrepInlineCanonical.inlineProgHOLExact inlBag
                (.seq first second) =
              .seq (CrepInlineCanonical.inlineProgHOLExact inlBag first)
                (CrepInlineCanonical.inlineProgHOLExact inlBag second) := by
          unfold CrepInlineCanonical.inlineProgHOLExact
          simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
        refine ⟨targetFirst, ?_, hstateFirst, hcodeFirst, ?_⟩
        rw [hinlineSeq, evalCrepSemHOLProgExact_seq_holShape, htargetFirst]
        · simp [hfirstNone]
        · cases resultFirst with
          | none => exact False.elim (hfirstNone rfl)
          | some result => cases result <;> simp_all

/-! ## `inline_prog_correct` Return constructor case

HOL `crep_inlineProofScript.sml:2301-2309` states the theorem; the Return case
starts at line 2396. It has no recursive `evaluate_ind` hypothesis. HOL's
`evaluate (Return es, s)` evaluates the list once and clears only locals;
`inline_prog_def` leaves Return unchanged. The exact clocked Return clause,
`eval_code_inl`, and `opt_mmap_eval_code_inl` ports use `CrepExpHOL`,
`CrepProgHOL`, `HolWordLab`, and `CrepSemHOLState` with the reviewed fixed-width
and canonical finite-map carriers. -/

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectReturnCaseExact {width : Nat} [NeZero width] {σ : Type}
    (values : List (CrepExpHOL width)) (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.return values) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.return values)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_return_holShape] at hsource
  cases heval : values.mapM (evalCrepSemHOLExp s) with
  | none =>
      simp [heval] at hsource
      have hresult : r = some .error := hsource.1.symm
      exact False.elim (hnotError hresult)
  | some wordValues =>
      have htargetValues : values.mapM (evalCrepSemHOLExp t) = some wordValues :=
        optMmapEvalCodeInlExact s values wordValues t inlFs
          ⟨heval, hstate, hlocals, hcode⟩
      simp [heval] at hsource
      rcases hsource with ⟨hr, hs'⟩
      subst r
      subst s'
      have hinline :
          CrepInlineCanonical.inlineProgHOLExact inlBag (.return values) = .return values := by
        unfold CrepInlineCanonical.inlineProgHOLExact
        simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
      refine ⟨CrepSemHOLState.emptyLocals t, ?_, ?_, ?_, ?_⟩
      · rw [hinline, evalCrepSemHOLProgExact_return_holShape, htargetValues]
      · simpa [crepInlineStateRelCodeExact, CrepSemHOLState.emptyLocals] using hstate
      · simpa [crepInlineCodeInlRelExact, CrepSemHOLState.emptyLocals] using hcode
      · simp

/-! ## `inline_prog_correct` Skip constructor case

HOL `crep_inlineProofScript.sml:2301-2309` states the theorem; the terminal
remaining case in its `evaluate_ind` proof (`:2402-2405`) reduces Skip using
`inline_prog_def` and `evaluate_def`. The HOL inline transformation's generic
unchanged-program clause at `crep_inlineScript.sml:249` covers Skip, and
`crepSemScript.sml:241` gives `evaluate (Skip, s) = (NONE, s)`. Lean's exact
`CrepProgHOL` Skip constructor and `evalCrepSemHOLProgExact_skip` have the same
state-preserving behavior. The tagged theorem keeps the same exact finite-map
and positive-width word carriers reviewed for the other inline cases. -/

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectSkipCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.skip : CrepProgHOL width) = (r, s'))
    (_hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.skip : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_skip] at hsource
  cases hsource
  have hinline :
      CrepInlineCanonical.inlineProgHOLExact inlBag (.skip : CrepProgHOL width) =
        .skip := by
    unfold CrepInlineCanonical.inlineProgHOLExact
    simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
  refine ⟨t, ?_, hstate, hcode, ?_⟩
  · rw [hinline, evalCrepSemHOLProgExact_skip]
  · simpa [crepInlineLocalsStrongRelExact]

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectAssignCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (name : Nat) (src : CrepExpHOL width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.assign name src : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.assign name src : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_assign_holShape] at hsource
  cases hexp : evalCrepSemHOLExp s src with
  | none =>
      simp only [hexp] at hsource
      exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some w =>
      simp only [hexp] at hsource
      cases hl : s.locals.lookup name with
      | none =>
          simp only [hl] at hsource
          exact absurd (congrArg Prod.fst hsource).symm hnotError
      | some old =>
          simp only [hl] at hsource
          obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
          have hr' : r = none := hr.symm
          have hs'' : s' = { s with locals := s.locals.updateEq (name, w) } := hs'.symm
          subst hr'
          subst hs''
          have htargetExp : evalCrepSemHOLExp t src = some w :=
            evalCodeInlExact s src w t inlFs ⟨hexp, hstate, hlocals, hcode⟩
          have hlocalt : t.locals.lookup name = some old := by
            rw [← hlocals]
            exact hl
          have hinline :
              CrepInlineCanonical.inlineProgHOLExact inlBag
                  (.assign name src : CrepProgHOL width) = .assign name src := by
            unfold CrepInlineCanonical.inlineProgHOLExact
            simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
          refine ⟨{ t with locals := t.locals.updateEq (name, w) }, ?_, ?_, ?_, ?_⟩
          · rw [hinline, evalCrepSemHOLProgExact_assign_holShape, htargetExp, hlocalt]
          · exact hstate
          · exact hcode
          · simp only [crepInlineLocalsStrongRelExact]
            rw [hlocals]

/-- HOL `inline_prog_correct` Break case (`crep_inlineProofScript.sml:2301`,
    atomic fall-through; `inline_prog` leaves `.break` unchanged). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectBreakCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (label : Nat)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.break label : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.break label : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_break] at hsource
  obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
  have hr' : r = some (.break label) := hr.symm
  have hs'' : s' = s := hs'.symm
  subst hr'
  subst hs''
  have hinline :
      CrepInlineCanonical.inlineProgHOLExact inlBag (.break label : CrepProgHOL width) =
        .break label := by
    unfold CrepInlineCanonical.inlineProgHOLExact
    simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
  refine ⟨t, ?_, hstate, hcode, ?_⟩
  · rw [hinline, evalCrepSemHOLProgExact_break]
  · simp only [crepInlineLocalsStrongRelExact]
    exact hlocals

/-- HOL `inline_prog_correct` Continue case (`crep_inlineProofScript.sml:2301`,
    atomic fall-through; `inline_prog` leaves `.continue` unchanged). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectContinueCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (label : Nat)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.continue label : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.continue label : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_continue] at hsource
  obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
  have hr' : r = some (.continue label) := hr.symm
  have hs'' : s' = s := hs'.symm
  subst hr'
  subst hs''
  have hinline :
      CrepInlineCanonical.inlineProgHOLExact inlBag (.continue label : CrepProgHOL width) =
        .continue label := by
    unfold CrepInlineCanonical.inlineProgHOLExact
    simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
  refine ⟨t, ?_, hstate, hcode, ?_⟩
  · rw [hinline, evalCrepSemHOLProgExact_continue]
  · simp only [crepInlineLocalsStrongRelExact]
    exact hlocals

/-- HOL `inline_prog_correct` Raise case (`crep_inlineProofScript.sml:2301`,
    atomic fall-through; `inline_prog` leaves `.raise` unchanged). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectRaiseCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName
      (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (exception : BitVec width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.raise exception : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (_hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.raise exception : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) =>
          crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_raise] at hsource
  obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
  have hr' : r = some (.exception exception) := hr.symm
  have hs'' : s' = CrepSemHOLState.emptyLocals s := hs'.symm
  subst hr'
  subst hs''
  have hinline :
      CrepInlineCanonical.inlineProgHOLExact inlBag (.raise exception : CrepProgHOL width) =
        .raise exception := by
    unfold CrepInlineCanonical.inlineProgHOLExact
    simp only [CrepInlineCanonical.inlineProgHOLCoreExact]
  refine ⟨CrepSemHOLState.emptyLocals t, ?_, ?_, hcode, ?_⟩
  · rw [hinline, evalCrepSemHOLProgExact_raise]
  · simpa only [crepInlineStateRelCodeExact, CrepSemHOLState.emptyLocals] using hstate
  · trivial

private theorem srel_mem {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) (m : BitVec width → HolWordLab width)
    (h : crepInlineStateRelCodeExact s t) :
    crepInlineStateRelCodeExact { s with memory := m } { t with memory := m } := by
  obtain ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩ := h
  exact ⟨hg, rfl, hma, hshm, hcl, hbe, hffi, hba, hta⟩

private theorem srel_glob {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ) (key : BitVec 5) (value : HolWordLab width)
    (h : crepInlineStateRelCodeExact s t) :
    crepInlineStateRelCodeExact (CrepSemHOLState.setGlobals key value s)
      (CrepSemHOLState.setGlobals key value t) := by
  obtain ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩ := h
  exact ⟨by
    show s.globals.updateEq (key, value) = t.globals.updateEq (key, value)
    rw [hg], hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩

private theorem srel_empty {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ)
    (h : crepInlineStateRelCodeExact s t) :
    crepInlineStateRelCodeExact (CrepSemHOLState.emptyLocals s)
      (CrepSemHOLState.emptyLocals t) := by
  obtain ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩ := h
  exact ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩

private theorem srel_decclock {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ)
    (h : crepInlineStateRelCodeExact s t) :
    crepInlineStateRelCodeExact (decClockCrepSemHOL s) (decClockCrepSemHOL t) := by
  obtain ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩ := h
  exact ⟨hg, hmem, hma, hshm, by
    show s.clock - 1 = t.clock - 1
    rw [hcl], hbe, hffi, hba, hta⟩

theorem inline_store {width : Nat} [NeZero width] (inlBag) (dst src) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.store dst src : CrepProgHOL width) = .store dst src := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

theorem inline_store32 {width : Nat} [NeZero width] (inlBag) (dst src) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.store32 dst src : CrepProgHOL width) = .store32 dst src := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

theorem inline_storeByte {width : Nat} [NeZero width] (inlBag) (dst src) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.storeByte dst src : CrepProgHOL width) = .storeByte dst src := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

theorem inline_storeGlob {width : Nat} [NeZero width] (inlBag) (dst src) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.storeGlob dst src : CrepProgHOL width) = .storeGlob dst src := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

theorem inline_tick {width : Nat} [NeZero width] (inlBag) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.tick : CrepProgHOL width) = .tick := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

theorem inline_primitive {width : Nat} [NeZero width]
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (names : List Nat) (operator : PrimOp) (args : List Nat) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.primitive names operator args : CrepProgHOL width) =
      .primitive names operator args := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

theorem inline_extCall {width : Nat} [NeZero width]
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat) :
    CrepInlineCanonical.inlineProgHOLExact inlBag
        (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) =
      .extCall function configuration configurationLength array arrayLength := by
  unfold CrepInlineCanonical.inlineProgHOLExact
  simp only [CrepInlineCanonical.inlineProgHOLCoreExact]

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectStoreCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (dst src : CrepExpHOL width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.store dst src : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.store dst src : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_store_holShape] at hsource
  cases hdv : evalCrepSemHOLExp s dst with
  | none =>
      simp only [hdv] at hsource
      exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some dv =>
      cases dv with
      | word adr =>
          simp only [hdv] at hsource
          cases hsv : evalCrepSemHOLExp s src with
          | none =>
              simp only [hsv] at hsource
              exact absurd (congrArg Prod.fst hsource).symm hnotError
          | some w =>
              simp only [hsv] at hsource
              cases hm : panMemStoreHOL adr w s.memaddrs s.memory with
              | none =>
                  simp only [hm] at hsource
                  exact absurd (congrArg Prod.fst hsource).symm hnotError
              | some m =>
                  simp only [hm] at hsource
                  obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
                  have hr' : r = none := hr.symm
                  have hs'' : s' = { s with memory := m } := hs'.symm
                  subst hr'
                  subst hs''
                  have hdstt : evalCrepSemHOLExp t dst = some (.word adr) :=
                    evalCodeInlExact s dst (.word adr) t inlFs ⟨hdv, hstate, hlocals, hcode⟩
                  have hsrt : evalCrepSemHOLExp t src = some w :=
                    evalCodeInlExact s src w t inlFs ⟨hsv, hstate, hlocals, hcode⟩
                  have hmemt : panMemStoreHOL adr w t.memaddrs t.memory = some m := by
                    obtain ⟨_, hmem, hma, _, _, _, _, _, _⟩ := hstate
                    rw [← hma, ← hmem]
                    exact hm
                  refine ⟨{ t with memory := m }, ?_, ?_, hcode, ?_⟩
                  · have hgoal : evalCrepSemHOLProgExact t (.store dst src : CrepProgHOL width) =
                        (none, { t with memory := m }) := by
                      rw [evalCrepSemHOLProgExact_store_holShape]
                      simp only [hdstt, hsrt, hmemt]
                    rw [inline_store]
                    exact hgoal
                  · obtain ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩ := hstate
                    exact ⟨hg, rfl, hma, hshm, hcl, hbe, hffi, hba, hta⟩
                  · simp only [crepInlineLocalsStrongRelExact]
                    exact hlocals


@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
private theorem inlineProgCorrectStoreGlobCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (dst : BitVec 5) (src : CrepExpHOL width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.storeGlob dst src : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.storeGlob dst src : CrepProgHOL width)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_storeGlob_holShape] at hsource
  cases hsv : evalCrepSemHOLExp s src with
  | none =>
      simp only [hsv] at hsource
      exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some w =>
      simp only [hsv] at hsource
      obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
      have hr' : r = none := hr.symm
      have hs'' : s' = CrepSemHOLState.setGlobals dst w s := hs'.symm
      subst hr'
      subst hs''
      have hsrt : evalCrepSemHOLExp t src = some w :=
        evalCodeInlExact s src w t inlFs ⟨hsv, hstate, hlocals, hcode⟩
      have hgoal : evalCrepSemHOLProgExact t (.storeGlob dst src : CrepProgHOL width) =
          (none, CrepSemHOLState.setGlobals dst w t) := by
        rw [evalCrepSemHOLProgExact_storeGlob_holShape]
        simp only [hsrt]
      refine ⟨CrepSemHOLState.setGlobals dst w t, ?_, ?_, hcode, ?_⟩
      · rw [inline_storeGlob]
        exact hgoal
      · exact srel_glob s t dst w hstate
      · simp only [crepInlineLocalsStrongRelExact, CrepSemHOLState.setGlobals]
        exact hlocals


@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
private theorem inlineProgCorrectStore32CaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (dst src : CrepExpHOL width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.store32 dst src : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.store32 dst src : CrepProgHOL width)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_store32_holShape] at hsource
  cases hdv : evalCrepSemHOLExp s dst with
  | none =>
      simp only [hdv] at hsource
      exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some dv =>
      cases dv with
      | word adr =>
          simp only [hdv] at hsource
          cases hsv : evalCrepSemHOLExp s src with
          | none =>
              simp only [hsv] at hsource
              exact absurd (congrArg Prod.fst hsource).symm hnotError
          | some wv =>
              cases wv with
              | word w =>
                  simp only [hsv] at hsource
                  cases hm : panMemStore32HOL s.memory s.memaddrs s.be adr (BitVec.ofNat 32 w.toNat) with
                  | none =>
                      simp only [hm] at hsource
                      exact absurd (congrArg Prod.fst hsource).symm hnotError
                  | some m =>
                      simp only [hm] at hsource
                      obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
                      have hr' : r = none := hr.symm
                      have hs'' : s' = { s with memory := m } := hs'.symm
                      subst hr'
                      subst hs''
                      have hdstt : evalCrepSemHOLExp t dst = some (.word adr) :=
                        evalCodeInlExact s dst (.word adr) t inlFs ⟨hdv, hstate, hlocals, hcode⟩
                      have hsrt : evalCrepSemHOLExp t src = some (.word w) :=
                        evalCodeInlExact s src (.word w) t inlFs ⟨hsv, hstate, hlocals, hcode⟩
                      have hmemt : panMemStore32HOL t.memory t.memaddrs t.be adr
                          (BitVec.ofNat 32 w.toNat) = some m := by
                        obtain ⟨_, hmem, hma, _, _, hbe, _, _, _⟩ := hstate
                        rw [← hma, ← hmem, ← hbe]
                        exact hm
                      have hgoal : evalCrepSemHOLProgExact t (.store32 dst src : CrepProgHOL width) =
                          (none, { t with memory := m }) := by
                        rw [evalCrepSemHOLProgExact_store32_holShape]
                        simp only [hdstt, hsrt, hmemt]
                      refine ⟨{ t with memory := m }, ?_, ?_, hcode, ?_⟩
                      · rw [inline_store32]
                        exact hgoal
                      · exact srel_mem s t m hstate
                      · simp only [crepInlineLocalsStrongRelExact]
                        exact hlocals

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
private theorem inlineProgCorrectStoreByteCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ) (dst src : CrepExpHOL width)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.storeByte dst src : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.storeByte dst src : CrepProgHOL width)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_storeByte_holShape] at hsource
  cases hdv : evalCrepSemHOLExp s dst with
  | none =>
      simp only [hdv] at hsource
      exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some dv =>
      cases dv with
      | word adr =>
          simp only [hdv] at hsource
          cases hsv : evalCrepSemHOLExp s src with
          | none =>
              simp only [hsv] at hsource
              exact absurd (congrArg Prod.fst hsource).symm hnotError
          | some wv =>
              cases wv with
              | word w =>
                  simp only [hsv] at hsource
                  cases hm : panMemStoreByteWord8HOL s.memory s.memaddrs s.be adr (BitVec.ofNat 8 w.toNat) with
                  | none =>
                      simp only [hm] at hsource
                      exact absurd (congrArg Prod.fst hsource).symm hnotError
                  | some m =>
                      simp only [hm] at hsource
                      obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
                      have hr' : r = none := hr.symm
                      have hs'' : s' = { s with memory := m } := hs'.symm
                      subst hr'
                      subst hs''
                      have hdstt : evalCrepSemHOLExp t dst = some (.word adr) :=
                        evalCodeInlExact s dst (.word adr) t inlFs ⟨hdv, hstate, hlocals, hcode⟩
                      have hsrt : evalCrepSemHOLExp t src = some (.word w) :=
                        evalCodeInlExact s src (.word w) t inlFs ⟨hsv, hstate, hlocals, hcode⟩
                      have hmemt : panMemStoreByteWord8HOL t.memory t.memaddrs t.be adr
                          (BitVec.ofNat 8 w.toNat) = some m := by
                        obtain ⟨_, hmem, hma, _, _, hbe, _, _, _⟩ := hstate
                        rw [← hma, ← hmem, ← hbe]
                        exact hm
                      have hgoal : evalCrepSemHOLProgExact t (.storeByte dst src : CrepProgHOL width) =
                          (none, { t with memory := m }) := by
                        rw [evalCrepSemHOLProgExact_storeByte_holShape]
                        simp only [hdstt, hsrt, hmemt]
                      refine ⟨{ t with memory := m }, ?_, ?_, hcode, ?_⟩
                      · rw [inline_storeByte]
                        exact hgoal
                      · exact srel_mem s t m hstate
                      · simp only [crepInlineLocalsStrongRelExact]
                        exact hlocals

@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
private theorem inlineProgCorrectTickCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.tick : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag (.tick : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  rw [evalCrepSemHOLProgExact_tick] at hsource
  by_cases hc : s.clock = 0
  · simp only [hc, if_true] at hsource
    obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
    have hr' : r = some .timeOut := hr.symm
    have hs'' : s' = CrepSemHOLState.emptyLocals s := hs'.symm
    subst hr'
    subst hs''
    have hct : t.clock = 0 := by
      obtain ⟨_, _, _, _, hcl, _, _, _, _⟩ := hstate
      rw [← hcl]
      exact hc
    have hgoal : evalCrepSemHOLProgExact t (.tick : CrepProgHOL width) =
        (some .timeOut, CrepSemHOLState.emptyLocals t) := by
      rw [evalCrepSemHOLProgExact_tick, if_pos hct]
    refine ⟨CrepSemHOLState.emptyLocals t, ?_, ?_, hcode, ?_⟩
    · rw [inline_tick]
      exact hgoal
    · exact srel_empty s t hstate
    · trivial
  · simp only [hc, if_false] at hsource
    obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
    have hr' : r = none := hr.symm
    have hs'' : s' = decClockCrepSemHOL s := hs'.symm
    subst hr'
    subst hs''
    have hct : t.clock ≠ 0 := by
      obtain ⟨_, _, _, _, hcl, _, _, _, _⟩ := hstate
      rw [← hcl]
      exact hc
    have hgoal : evalCrepSemHOLProgExact t (.tick : CrepProgHOL width) =
        (none, decClockCrepSemHOL t) := by
      rw [evalCrepSemHOLProgExact_tick, if_neg hct]
    refine ⟨decClockCrepSemHOL t, ?_, ?_, hcode, ?_⟩
    · rw [inline_tick]
      exact hgoal
    · exact srel_decclock s t hstate
    · simp only [crepInlineLocalsStrongRelExact]
      exact hlocals

/-- HOL `inline_prog_correct` Primitive case
    (`crep_inlineProofScript.sml:2301-2309`, atomic catch-all `:2401`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectPrimitiveCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (names : List Nat) (operator : PrimOp) (args : List Nat)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s (.primitive names operator args : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.primitive names operator args : CrepProgHOL width)) = (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  simp only [crepInlineLocalsStrongRelExact] at hlocals
  rw [evalCrepSemHOLProgExact_primitive_holShape] at hsource
  cases hargs : args.mapM s.locals.lookup with
  | none =>
      simp only [hargs] at hsource
      exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some ws =>
      simp only [hargs] at hsource
      cases hop : crepPrimopHOLExact operator ws with
      | none =>
          simp only [hop] at hsource
          exact absurd (congrArg Prod.fst hsource).symm hnotError
      | some results =>
          simp only [hop] at hsource
          by_cases hg : names.length = results.length ∧
              (∀ v ∈ names, (s.locals.lookup v).isSome) ∧ names.Nodup
          · rw [if_pos hg] at hsource
            obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
            have hr' : r = none := hr.symm
            have hs'' : s' = { s with locals := s.locals.updateListEq (names.zip results) } :=
              hs'.symm
            subst hr'
            subst hs''
            have hargs_t : args.mapM t.locals.lookup = some ws := by
              rw [← hlocals]
              exact hargs
            have hg_t : names.length = results.length ∧
                (∀ v ∈ names, (t.locals.lookup v).isSome) ∧ names.Nodup := by
              refine ⟨hg.1, ?_, hg.2.2⟩
              intro v hv
              have hv' := hg.2.1 v hv
              rwa [← hlocals]
            have hgoal : evalCrepSemHOLProgExact t
                (.primitive names operator args : CrepProgHOL width) =
                (none, { t with locals := t.locals.updateListEq (names.zip results) }) := by
              rw [evalCrepSemHOLProgExact_primitive_holShape]
              simp only [hargs_t, hop, if_pos hg_t]
            refine ⟨{ t with locals := t.locals.updateListEq (names.zip results) },
              ?_, hstate, hcode, ?_⟩
            · rw [inline_primitive]
              exact hgoal
            · simp only [crepInlineLocalsStrongRelExact]
              rw [hlocals]
          · rw [if_neg hg] at hsource
            exact absurd (congrArg Prod.fst hsource).symm hnotError

/-- HOL `inline_prog_correct` ExtCall case
    (`crep_inlineProofScript.sml:2301-2309`, atomic catch-all `:2401`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "inline_prog_correct"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals,
      CrepSemHOLState.code, inlFs, inlBag])
  (words_as_type_indexed_bitvec)]
theorem inlineProgCorrectExtCallCaseExact {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (inlFs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (inlBag : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (t : CrepSemHOLState width σ)
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength : Nat)
    (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (hsource : evalCrepSemHOLProgExact s
        (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) = (r, s'))
    (hnotError : r ≠ some .error)
    (_hsubmap : HolFiniteMapExact.submap inlFs s.code)
    (_hbag : HolFiniteMapExact.submap inlBag inlFs)
    (hstate : crepInlineStateRelCodeExact s t)
    (hlocals : crepInlineLocalsStrongRelExact s t)
    (hcode : crepInlineCodeInlRelExact inlFs s t) :
    ∃ t' : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact t
          (CrepInlineCanonical.inlineProgHOLExact inlBag
            (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width)) =
            (r, t') ∧
      crepInlineStateRelCodeExact s' t' ∧
      crepInlineCodeInlRelExact inlFs s' t' ∧
      match r with
      | none => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.break _) => crepInlineLocalsStrongRelExact s' t'
      | some (CrepResultHOLExact.continue _) => crepInlineLocalsStrongRelExact s' t'
      | some .error => False
      | _ => True := by
  classical
  simp only [crepInlineLocalsStrongRelExact] at hlocals
  obtain ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩ := hstate
  rw [evalCrepSemHOLProgExact_extCall_holShape] at hsource
  cases h1 : s.locals.lookup configurationLength with
  | none => simp only [h1] at hsource; exact absurd (congrArg Prod.fst hsource).symm hnotError
  | some v1 =>
    cases v1 with
    | word configLength =>
      cases h2 : s.locals.lookup configuration with
      | none => simp only [h1, h2] at hsource; exact absurd (congrArg Prod.fst hsource).symm hnotError
      | some v2 =>
        cases v2 with
        | word configAddress =>
          cases h3 : s.locals.lookup arrayLength with
          | none => simp only [h1, h2, h3] at hsource; exact absurd (congrArg Prod.fst hsource).symm hnotError
          | some v3 =>
            cases v3 with
            | word arrayLengthValue =>
              cases h4 : s.locals.lookup array with
              | none => simp only [h1, h2, h3, h4] at hsource; exact absurd (congrArg Prod.fst hsource).symm hnotError
              | some v4 =>
                cases v4 with
                | word arrayAddress =>
                  simp only [h1, h2, h3, h4] at hsource
                  cases hr1 : readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                      (panMemLoadByteWord8HOL s.memory s.memaddrs s.be) with
                  | none => simp only [hr1] at hsource; exact absurd (congrArg Prod.fst hsource).symm hnotError
                  | some configBytes =>
                    simp only [hr1] at hsource
                    cases hr2 : readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                        (panMemLoadByteWord8HOL s.memory s.memaddrs s.be) with
                    | none => simp only [hr2] at hsource; exact absurd (congrArg Prod.fst hsource).symm hnotError
                    | some arrayBytes =>
                      simp only [hr2] at hsource
                      cases hcall : callFFIHOL s.ffi (.extCall function) configBytes arrayBytes with
                      | final event =>
                          simp only [hcall] at hsource
                          obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
                          have hr' : r = some (.finalFfi event) := hr.symm
                          have hs'' : s' = s := hs'.symm
                          subst hr'
                          subst s'
                          have ht1 : t.locals.lookup configurationLength = some (.word configLength) := by
                            rw [← hlocals]; exact h1
                          have ht2 : t.locals.lookup configuration = some (.word configAddress) := by
                            rw [← hlocals]; exact h2
                          have ht3 : t.locals.lookup arrayLength = some (.word arrayLengthValue) := by
                            rw [← hlocals]; exact h3
                          have ht4 : t.locals.lookup array = some (.word arrayAddress) := by
                            rw [← hlocals]; exact h4
                          have hload_t : panMemLoadByteWord8HOL t.memory t.memaddrs t.be =
                              panMemLoadByteWord8HOL s.memory s.memaddrs s.be := by
                            rw [← hmem, ← hma, ← hbe]
                          have hr1t : readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                              (panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some configBytes := by
                            rw [hload_t]; exact hr1
                          have hr2t : readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                              (panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some arrayBytes := by
                            rw [hload_t]; exact hr2
                          have hcallt : callFFIHOL t.ffi (.extCall function) configBytes arrayBytes = .final event := by
                            rw [← hffi]; exact hcall
                          have hgoal : evalCrepSemHOLProgExact t
                              (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) =
                              (some (.finalFfi event), t) := by
                            rw [evalCrepSemHOLProgExact_extCall_holShape]
                            simp only [ht1, ht2, ht3, ht4, hr1t, hr2t, hcallt]
                          refine ⟨t, ?_, ⟨hg, hmem, hma, hshm, hcl, hbe, hffi, hba, hta⟩, hcode, ?_⟩
                          · rw [inline_extCall]
                            exact hgoal
                          · trivial
                      | «ret» newFfi newBytes =>
                          simp only [hcall] at hsource
                          obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp hsource
                          have hr' : r = none := hr.symm
                          have hs'' : s' = { s with
                              memory := panWriteBytearrayWord8HOL arrayAddress newBytes s.memory s.memaddrs s.be,
                              ffi := newFfi } := hs'.symm
                          subst hr'
                          subst hs''
                          have ht1 : t.locals.lookup configurationLength = some (.word configLength) := by
                            rw [← hlocals]; exact h1
                          have ht2 : t.locals.lookup configuration = some (.word configAddress) := by
                            rw [← hlocals]; exact h2
                          have ht3 : t.locals.lookup arrayLength = some (.word arrayLengthValue) := by
                            rw [← hlocals]; exact h3
                          have ht4 : t.locals.lookup array = some (.word arrayAddress) := by
                            rw [← hlocals]; exact h4
                          have hload_t : panMemLoadByteWord8HOL t.memory t.memaddrs t.be =
                              panMemLoadByteWord8HOL s.memory s.memaddrs s.be := by
                            rw [← hmem, ← hma, ← hbe]
                          have hr1t : readBytearrayWordHOL (byteWidth := 8) configAddress configLength.toNat
                              (panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some configBytes := by
                            rw [hload_t]; exact hr1
                          have hr2t : readBytearrayWordHOL (byteWidth := 8) arrayAddress arrayLengthValue.toNat
                              (panMemLoadByteWord8HOL t.memory t.memaddrs t.be) = some arrayBytes := by
                            rw [hload_t]; exact hr2
                          have hcallt : callFFIHOL t.ffi (.extCall function) configBytes arrayBytes =
                              .ret newFfi newBytes := by
                            rw [← hffi]; exact hcall
                          have hwrite_t : panWriteBytearrayWord8HOL arrayAddress newBytes t.memory t.memaddrs t.be =
                              panWriteBytearrayWord8HOL arrayAddress newBytes s.memory s.memaddrs s.be := by
                            rw [← hmem, ← hma, ← hbe]
                          have hgoal : evalCrepSemHOLProgExact t
                              (.extCall function configuration configurationLength array arrayLength : CrepProgHOL width) =
                              (none, { t with
                                memory := panWriteBytearrayWord8HOL arrayAddress newBytes t.memory t.memaddrs t.be,
                                ffi := newFfi }) := by
                            rw [evalCrepSemHOLProgExact_extCall_holShape]
                            simp only [ht1, ht2, ht3, ht4, hr1t, hr2t, hcallt]
                          refine ⟨{ t with
                              memory := panWriteBytearrayWord8HOL arrayAddress newBytes t.memory t.memaddrs t.be,
                              ffi := newFfi }, ?_, ?_, hcode, ?_⟩
                          · rw [inline_extCall]
                            exact hgoal
                          · rw [hwrite_t]
                            exact ⟨hg, rfl, hma, hshm, hcl, hbe, rfl, hba, hta⟩
                          · simp only [crepInlineLocalsStrongRelExact]
                            rw [hlocals]

end CrepInlineExact

end Flapjack
