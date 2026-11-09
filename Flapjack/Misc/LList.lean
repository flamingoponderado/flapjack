module

public import Flapjack.HolRef

@[expose] public section

/-!
# HOL `llist` (possibly infinite lists)

Rendering of HOL4's lazy-list library, pinned at
`hol4/src/coalgebras/llistScript.sml`. Only individually compared declarations
carry `@[hol]` tags; the source pin alone approves no other port. HOL defines `'a llist` by
`new_type_definition` as the subtype of `num -> 'a option` satisfying the
coinductive `lrep_ok` (`llistScript.sml:22-64`); `HolLList` is that same
subtype, using HOL's proven characterisation `lrep_ok_alt`
(`lrep_ok f = !n. IS_SOME (f (SUC n)) ==> IS_SOME (f n)`) as its invariant.
The operations below follow the HOL definitions of the same names.  They are
noncomputable where HOL uses Hilbert choice (`LLENGTH`) or an undecidable
guard (`LFINITE` in `toList`).  Used by the exact CakeML `behaviour` datatype
(`Diverge (io_event llist)`) and `build_lprefix_lub`.
-/

namespace Flapjack

/-- HOL `lrep_ok`, in its equivalent characterisation `lrep_ok_alt`
    (`llistScript.sml:36`). -/
def HolLrepOk {α : Type} (f : Nat → Option α) : Prop :=
  ∀ n, (f (n + 1)).isSome → (f n).isSome

/-- HOL `'a llist` (`llistScript.sml:64`, `new_type_definition ("llist", ...)`):
    `llist_rep` is `rep`, `llist_abs` is the anonymous constructor. -/
structure HolLList (α : Type) where
  rep : Nat → Option α
  ok : HolLrepOk rep

namespace HolLList

variable {α β : Type}

/-- HOL `LNIL = llist_abs (λn. NONE)` (`llistScript.sml:121`). -/
def lnil : HolLList α := ⟨fun _ => none, fun _ h => by simp at h⟩

/-- HOL `LCONS h t = llist_abs (λn. if n = 0 then SOME h else llist_rep t (n - 1))`
    (`llistScript.sml:123-125`). -/
def lcons (h : α) (t : HolLList α) : HolLList α :=
  ⟨fun n => if n = 0 then some h else t.rep (n - 1), by
    intro n hn
    cases n with
    | zero => simp
    | succ n => simpa using t.ok n (by simpa using hn)⟩

/-- HOL `LHD ll = llist_rep ll 0` (`llistScript.sml:161`). -/
def lhd (ll : HolLList α) : Option α := ll.rep 0

/-- HOL `LTL ll = case LHD ll of NONE => NONE
    | SOME _ => SOME (llist_abs (\n. llist_rep ll (n + 1)))` (`llistScript.sml:163-167`). -/
def ltl (ll : HolLList α) : Option (HolLList α) :=
  match ll.lhd with
  | none => none
  | some _ => some ⟨fun n => ll.rep (n + 1), fun n h => ll.ok (n + 1) h⟩

/-- HOL `LNTH` (`llistScript.sml:320-323`):
    `LNTH 0 ll = LHD ll`, `LNTH (SUC n) ll = OPTION_JOIN (OPTION_MAP (LNTH n) (LTL ll))`. -/
def lnth : Nat → HolLList α → Option α
  | 0, ll => ll.lhd
  | n + 1, ll => (ll.ltl.map (lnth n)).join

/-- The `FUNPOW` iterate inside HOL `LUNFOLD_def`. -/
def lunfoldStep (f : β → Option (β × α)) (z : β) : Nat → Option (β × α)
  | 0 => f z
  | n + 1 => (lunfoldStep f z n).bind (fun p => f p.1)

/-- HOL `LUNFOLD f z = llist_abs (\n. OPTION_MAP SND
    (FUNPOW (\m. OPTION_BIND m (UNCURRY (K o f))) n (f z)))` (`llistScript.sml:367-369`);
    `UNCURRY (K o f) (b, a) = f b`. -/
def lunfold (f : β → Option (β × α)) (z : β) : HolLList α :=
  ⟨fun n => (lunfoldStep f z n).map Prod.snd, by
    intro n h
    simp only [lunfoldStep, Option.isSome_map] at h ⊢
    cases hs : lunfoldStep f z n with
    | none => rw [hs] at h; simp at h
    | some _ => simp⟩

/-- HOL `fromList` (`llistScript.sml:1154-1156`). -/
def fromList : List α → HolLList α
  | [] => lnil
  | h :: t => lcons h (fromList t)

/-- HOL `LFINITE` (`llistScript.sml:919-922`, `Hol_reln`). -/
inductive LFinite : HolLList α → Prop
  | lnil : LFinite lnil
  | lcons (h : α) (t : HolLList α) : LFinite t → LFinite (lcons h t)

/-- HOL `llength_rel` (`llistScript.sml:947-950`, `Hol_reln`). -/
inductive LLengthRel : HolLList α → Nat → Prop
  | lnil : LLengthRel lnil 0
  | lcons (h : α) (n : Nat) (t : HolLList α) : LLengthRel t n → LLengthRel (lcons h t) (n + 1)

open Classical in
/-- HOL `LLENGTH ll = if LFINITE ll then SOME (@n. llength_rel ll n) else NONE`
    (`llistScript.sml:981-983`); HOL `@` is `Classical.epsilon`. -/
noncomputable def llength (ll : HolLList α) : Option Nat :=
  if LFinite ll then some (Classical.epsilon (fun n => LLengthRel ll n)) else none

/-- HOL `LTAKE` (`llistScript.sml:622-630`); HOL `THE (LTL ll)` is taken only
    when `LHD ll` is `SOME`, where `LTL ll` is `SOME`. -/
def ltake : Nat → HolLList α → Option (List α)
  | 0, _ => some []
  | n + 1, ll =>
      match ll.lhd with
      | none => none
      | some hd =>
          match ll.ltl with
          | none => none
          | some tl =>
              match ltake n tl with
              | none => none
              | some rest => some (hd :: rest)

open Classical in
/-- HOL `toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE`
    (`llistScript.sml:1140-1142`). -/
noncomputable def toList (ll : HolLList α) : Option (List α) :=
  if LFinite ll then ltake ((llength ll).getD 0) ll else none

/-- HOL `LPREFIX` (`llistScript.sml:2655-2662`). -/
noncomputable def lprefix (l1 l2 : HolLList α) : Prop :=
  match toList l1 with
  | none => l1 = l2
  | some xs =>
      match toList l2 with
      | none => ltake xs.length l2 = some xs
      | some ys => xs <+: ys

theorem lcons_ne_lnil (h : α) (t : HolLList α) : lcons h t ≠ lnil := by
  intro heq
  have := congrArg (fun l : HolLList α => l.rep 0) heq
  simp [lcons, lnil] at this

theorem lcons_inj {h h' : α} {t t' : HolLList α} (heq : lcons h t = lcons h' t') :
    h = h' ∧ t = t' := by
  have h0 := congrArg (fun l : HolLList α => l.rep 0) heq
  simp only [lcons, if_pos] at h0
  refine ⟨Option.some.inj h0, ?_⟩
  cases t; cases t'
  simp only [mk.injEq]
  funext n
  have := congrArg (fun l : HolLList α => l.rep (n + 1)) heq
  simpa [lcons] using this

theorem lfinite_fromList : ∀ l : List α, LFinite (fromList l)
  | [] => .lnil
  | h :: t => .lcons h _ (lfinite_fromList t)

theorem llengthRel_fromList : ∀ l : List α, LLengthRel (fromList l) l.length
  | [] => .lnil
  | h :: t => .lcons h _ _ (llengthRel_fromList t)

theorem llengthRel_lnil_inv {m : Nat} (h : LLengthRel (lnil : HolLList α) m) : m = 0 := by
  generalize e : (lnil : HolLList α) = ll at h
  cases h with
  | lnil => rfl
  | lcons h' k t _ => exact absurd e.symm (lcons_ne_lnil h' t)

theorem llengthRel_lcons_inv {x : α} {t : HolLList α} {m : Nat}
    (h : LLengthRel (lcons x t) m) : ∃ k, m = k + 1 ∧ LLengthRel t k := by
  generalize e : lcons x t = ll at h
  cases h with
  | lnil => exact absurd e (lcons_ne_lnil x t)
  | lcons h' k t' hk =>
    obtain ⟨-, rfl⟩ := lcons_inj e
    exact ⟨k, rfl, hk⟩

theorem eq_lnil_of_LLengthRel_zero {ll : HolLList α} (h : LLengthRel ll 0) : ll = lnil := by
  cases h with
  | lnil => rfl

theorem llengthRel_unique {ll : HolLList α} {n m : Nat} (hn : LLengthRel ll n) :
    LLengthRel ll m → n = m := by
  induction hn generalizing m with
  | lnil => intro hm; exact (llengthRel_lnil_inv hm).symm
  | lcons h k t _ ih =>
    intro hm
    obtain ⟨k', rfl, hk'⟩ := llengthRel_lcons_inv hm
    rw [ih hk']

theorem llength_fromList (l : List α) : llength (fromList l) = some l.length := by
  have hr := llengthRel_fromList l
  unfold llength
  rw [if_pos (lfinite_fromList l)]
  congr 1
  exact llengthRel_unique (Classical.epsilon_spec ⟨_, hr⟩) hr

theorem ltake_fromList : ∀ l : List α, ltake l.length (fromList l) = some l
  | [] => rfl
  | h :: t => by
      simp only [List.length_cons, fromList, ltake, lhd, lcons, ltl, if_pos]
      have := ltake_fromList t
      have ht : (⟨fun n => (lcons h (fromList t)).rep (n + 1),
          fun n hn => (lcons h (fromList t)).ok (n + 1) hn⟩ : HolLList α) = fromList t := by
        cases fromList t; simp [lcons]
      simp only [lcons] at ht
      rw [ht, this]

theorem toList_fromList (l : List α) : toList (fromList l) = some l := by
  unfold toList
  rw [if_pos (lfinite_fromList l), llength_fromList]
  exact ltake_fromList l

/-- On finite lists, HOL `LPREFIX (fromList xs) (fromList ys) = isPREFIX xs ys`. -/
theorem lprefix_fromList (xs ys : List α) :
    lprefix (fromList xs) (fromList ys) ↔ xs <+: ys := by
  unfold lprefix; rw [toList_fromList, toList_fromList]

/-- Flapjack representation fact about the local `HolLList.fromList`:
    `(fromList l).rep n = l[n]?`, i.e. `fromList` reads the list and is absent
    beyond its end.  Untagged local representation/transport infrastructure:
    there is no independently reviewed exact HOL declaration with this
    statement to cite. -/
theorem fromList_rep (l : List α) (n : Nat) : (fromList l).rep n = l[n]? := by
  induction l generalizing n with
  | nil => rfl
  | cons h t ih =>
      cases n with
      | zero => rfl
      | succ k =>
          show (if k + 1 = 0 then some h else (fromList t).rep (k + 1 - 1)) = (h :: t)[k + 1]?
          rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, ih k]
          rfl

/-- A present read of `fromList l` is within the list. -/
theorem fromList_rep_lt {l : List α} {n : Nat} {x : α}
    (h : (fromList l).rep n = some x) : n < l.length := by
  rw [fromList_rep] at h
  by_cases hn : n < l.length
  · exact hn
  · exfalso
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at h
    exact absurd h (by simp)

/-- A `none` at `k` forces a `none` at `k+1` (downward closure of `HolLrepOk`). -/
theorem rep_none_succ (ll : HolLList α) {k : Nat} (h : ll.rep k = none) :
    ll.rep (k + 1) = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro v hv
  have hk' : (ll.rep (k + 1)) ≠ none := by rw [hv]; exact Option.some_ne_none v
  exact (Option.isSome_iff_ne_none.mp (ll.ok k (Option.isSome_iff_ne_none.mpr hk'))) h


/-- A `none` in the representation persists to every larger index. -/
theorem rep_none_of_le (ll : HolLList α) {m n : Nat} (hm : ll.rep m = none) (hle : m ≤ n) :
    ll.rep n = none := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hle
  clear hle
  induction d with
  | zero => simpa using hm
  | succ d ih =>
      rw [Nat.add_succ]
      exact rep_none_succ ll ih


/-- `lnth` reads the underlying representation. -/
theorem lnth_eq_rep (n : Nat) (ll : HolLList α) : lnth n ll = ll.rep n := by
  induction n generalizing ll with
  | zero => rfl
  | succ n ih =>
      show (ll.ltl.map (lnth n)).join = ll.rep (n + 1)
      cases h0 : ll.rep 0 with
      | none =>
          have hrep : ll.rep (n + 1) = none := rep_none_of_le ll h0 (Nat.zero_le _)
          have hltl : ll.ltl = none := by simp [ltl, lhd, h0]
          simp [hltl, hrep]
      | some hd =>
          have ht : ll.ltl =
              some ⟨fun k => ll.rep (k + 1), fun k hk => ll.ok (k + 1) hk⟩ := by
            simp [ltl, lhd, h0]
          rw [ht]
          simp only [Option.map_some, Option.join]
          rw [ih]
          rfl


/-- `lnth` is `none` from `m` on whenever it is `none` at `m` and `m ≤ n`. -/
theorem lnth_none_mono {m n : Nat} (ll : HolLList α) (h : lnth m ll = none) (hle : m ≤ n) :
    lnth n ll = none := by
  rw [lnth_eq_rep] at h ⊢
  exact rep_none_of_le ll h hle


/-- The tail of a cons exposes the shifted representation. Untagged Flapjack
    infrastructure used to relate `lprefix` (defined via `toList`/`ltake`) to the
    representation `rep`/`lnth`; HOL's `llist` library is outside the cakeml
    submodule, so there is no taggable HOL original. -/
theorem ltl_rep {ll tl : HolLList α} (h : ll.ltl = some tl) (j : Nat) :
    tl.rep j = ll.rep (j + 1) := by
  cases h0 : ll.rep 0 with
  | none => simp [ltl, lhd, h0] at h
  | some hd =>
      simp only [ltl, lhd, h0] at h
      injection h with h'
      subst h'
      rfl


/-- `ltake` reads the representation: if `ltake k ll = some xs` then `xs` has
    length `k` and `ll.rep i = some (xs[i])` for every in-range `i`.  Untagged
    Flapjack infrastructure (no taggable HOL original). -/
theorem ltake_spec (k : Nat) (ll : HolLList α) (xs : List α)
    (h : ltake k ll = some xs) :
    xs.length = k ∧ ∀ i (hi : i < xs.length), ll.rep i = some xs[i] := by
  induction k generalizing ll xs with
  | zero =>
      simp only [ltake] at h
      injection h with hxs
      subst hxs
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | succ k ih =>
      cases h0 : ll.rep 0 with
      | none => simp [ltake, lhd, h0] at h
      | some hd =>
          cases h1 : ll.ltl with
          | none => simp [ltake, lhd, h0, h1] at h
          | some tl =>
              cases hrest : ltake k tl with
              | none => simp [ltake, lhd, h0, h1, hrest] at h
              | some rest =>
                  simp only [ltake, lhd, h0, h1, hrest] at h
                  injection h with hxs
                  subst hxs
                  obtain ⟨hlen, hrep⟩ := ih tl rest hrest
                  refine ⟨by simp [hlen], ?_⟩
                  intro i hi
                  cases i with
                  | zero => simp [h0]
                  | succ j =>
                      have hj : j < rest.length := by simpa [hlen] using hi
                      rw [← ltl_rep h1 j]
                      simpa using hrep j hj


/-- Converse of `ltake_spec`: if the representation agrees with `xs` on its
    indices, `ltake` returns `xs`. -/
theorem ltake_of_rep (xs : List α) (ll : HolLList α)
    (h : ∀ i (hi : i < xs.length), ll.rep i = some xs[i]) :
    ltake xs.length ll = some xs := by
  induction xs generalizing ll with
  | nil => simp [ltake]
  | cons x xs ih =>
      rw [List.length_cons]
      cases h0 : ll.rep 0 with
      | none => exact absurd (h 0 (by simp)) (by simp [h0])
      | some hd =>
          have hhd : hd = x := by
            have := h 0 (by simp)
            rw [h0] at this
            exact Option.some.inj this
          subst hhd
          have htl : ll.ltl =
              some ⟨fun n => ll.rep (n + 1), fun n hk => ll.ok (n + 1) hk⟩ := by
            simp [ltl, lhd, h0]
          have h' : ∀ i (hi : i < xs.length),
              (⟨fun n => ll.rep (n + 1), fun n hk => ll.ok (n + 1) hk⟩ : HolLList α).rep i =
                some xs[i] := by
            intro i hi
            have hhi := h (i + 1) (by simp [hi])
            rw [List.getElem_cons_succ] at hhi
            exact hhi
          simp only [ltake, lhd, h0, htl]
          rw [ih _ h']


/-- Two lazy lists with pointwise-equal representations are equal. -/
theorem ext_of_rep {a b : HolLList α} (h : ∀ n, a.rep n = b.rep n) : a = b := by
  have hrep : a.rep = b.rep := funext h
  obtain ⟨ra, oka⟩ := a
  obtain ⟨rb, okb⟩ := b
  simp only at hrep
  subst hrep
  exact congrArg (fun o => (⟨ra, o⟩ : HolLList α)) (Subsingleton.elim oka okb)


/-- The empty lazy list is the only one whose representation is everywhere `none`. -/
theorem eq_lnil_of_rep_none {ll : HolLList α} (h : ∀ n, ll.rep n = none) : ll = lnil :=
  ext_of_rep (fun n => by rw [h n]; rfl)


/-- A lazy list that has a `none` in its representation is finite. -/
theorem LFinite_of_rep_none {ll : HolLList α} {n : Nat} (h : ll.rep n = none) :
    LFinite ll := by
  induction n generalizing ll with
  | zero =>
      have hr : ∀ k, ll.rep k = none := fun k => rep_none_of_le ll h (Nat.zero_le k)
      rw [eq_lnil_of_rep_none hr]
      exact LFinite.lnil
  | succ n ih =>
      cases h0 : ll.rep 0 with
      | none =>
          have hr : ∀ k, ll.rep k = none := fun k => rep_none_of_le ll h0 (Nat.zero_le k)
          rw [eq_lnil_of_rep_none hr]
          exact LFinite.lnil
      | some hd =>
          have htail : (⟨fun k => ll.rep (k + 1),
              fun k hk => ll.ok (k + 1) hk⟩ : HolLList α).rep n = none := h
          have ihf : LFinite ⟨fun k => ll.rep (k + 1), fun k hk => ll.ok (k + 1) hk⟩ :=
            ih htail
          have heq : ll = lcons hd ⟨fun k => ll.rep (k + 1), fun k hk => ll.ok (k + 1) hk⟩ := by
            apply ext_of_rep
            intro k
            cases k with
            | zero => rw [h0]; rfl
            | succ k => rfl
          rw [heq]
          exact LFinite.lcons hd _ ihf


/-- A finite lazy list has a length relation witness. -/
theorem exists_LLengthRel_of_LFinite {ll : HolLList α} (h : LFinite ll) :
    ∃ n, LLengthRel ll n :=
  LFinite.rec (motive := fun ll _ => ∃ n, LLengthRel ll n)
    ⟨0, LLengthRel.lnil⟩
    (fun hd t _ ih => by obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, LLengthRel.lcons hd n t hn⟩)
    h


/-- For a finite lazy list, `llength` returns a length relation witness. -/
theorem llength_spec {ll : HolLList α} (h : LFinite ll) :
    ∃ n, llength ll = some n ∧ LLengthRel ll n := by
  have hex : ∃ n, LLengthRel ll n := exists_LLengthRel_of_LFinite h
  refine ⟨Classical.epsilon (fun n => LLengthRel ll n), ?_, Classical.epsilon_spec hex⟩
  unfold llength
  rw [if_pos h]


/-- Beyond a length relation bound the representation is `none`. -/
theorem rep_none_of_LLengthRel {ll : HolLList α} {n : Nat} (h : LLengthRel ll n) :
    ∀ i, n ≤ i → ll.rep i = none :=
  LLengthRel.rec (motive := fun ll n _ => ∀ i, n ≤ i → ll.rep i = none)
    (fun i _ => rfl)
    (fun hd k t _ ih i hi => by
      cases i with
      | zero => exact absurd hi (Nat.not_succ_le_zero k)
      | succ j =>
          have hj : k ≤ j := Nat.le_of_succ_le_succ hi
          have hshift : (lcons hd t).rep (j + 1) = t.rep j := by simp [lcons]
          rw [hshift]
          exact ih j hj)
    h


/-- `toList ll = some xs` exposes the representation as `xs` with `none` beyond. -/
theorem toList_eq_some_rep {ll : HolLList α} {xs : List α} (h : toList ll = some xs) :
    ∀ i, ll.rep i = if hi : i < xs.length then some xs[i] else none := by
  unfold toList at h
  split at h
  · rename_i hfin
    obtain ⟨n, hnlen, hnrel⟩ := llength_spec hfin
    rw [hnlen] at h
    simp only [Option.getD_some] at h
    obtain ⟨hlen, hrep⟩ := ltake_spec n ll xs h
    intro i
    by_cases hi : i < xs.length
    · rw [dif_pos hi]; simpa using hrep i hi
    · rw [dif_neg hi]
      have hnrel' : LLengthRel ll xs.length := by rw [hlen]; exact hnrel
      exact rep_none_of_LLengthRel hnrel' i (Nat.le_of_not_lt hi)
  · simp at h


/-- A cons peels its head. -/
theorem lhd_lcons (h : α) (t : HolLList α) : lhd (lcons h t) = some h := by
  simp [lhd, lcons]


/-- The tail of a cons is the original tail. -/
theorem ltl_lcons (h : α) (t : HolLList α) : ltl (lcons h t) = some t := by
  have hrep : (⟨fun n => (lcons h t).rep (n + 1),
      fun n hk => (lcons h t).ok (n + 1) hk⟩ : HolLList α) = t :=
    ext_of_rep (fun n => by simp [lcons])
  simp only [ltl, lhd_lcons, Option.some.injEq]
  exact hrep


/-- A finite lazy list has a `some` prefix of any length up to its length. -/
theorem ltake_of_LLengthRel {ll : HolLList α} {n : Nat} (h : LLengthRel ll n) :
    ∃ xs : List α, ltake n ll = some xs := by
  induction h with
  | lnil => exact ⟨[], rfl⟩
  | lcons hd k t _ ih =>
      obtain ⟨xs, hxs⟩ := ih
      exact ⟨hd :: xs, by simp [ltake, lhd_lcons, ltl_lcons, hxs]⟩


/-- A finite lazy list has a finite `toList`. -/
theorem toList_of_LFinite {ll : HolLList α} (h : LFinite ll) :
    ∃ xs : List α, toList ll = some xs := by
  obtain ⟨n, hnlen, hnrel⟩ := llength_spec h
  obtain ⟨xs, hxs⟩ := ltake_of_LLengthRel hnrel
  refine ⟨xs, ?_⟩
  unfold toList
  rw [if_pos h, hnlen]
  simp only [Option.getD_some]
  exact hxs


/-- A finite lazy list is never the `none` of `toList`. -/
theorem toList_ne_none_of_LFinite {ll : HolLList α} (h : LFinite ll) :
    toList ll ≠ none := by
  obtain ⟨xs, hxs⟩ := toList_of_LFinite h
  rw [hxs]
  exact Option.some_ne_none xs


/-- If `toList` is `none` the list is infinite and defined at every index. -/
theorem rep_some_of_toList_none {ll : HolLList α} (h : toList ll = none) :
    ∀ n, ∃ x, ll.rep n = some x := by
  intro n
  by_cases hn : ll.rep n = none
  · exact absurd h (toList_ne_none_of_LFinite (LFinite_of_rep_none hn))
  · exact Option.ne_none_iff_exists'.mp hn

/-! ### `llist`-library helper lemmas

The `llist_shorter` ports (`llist_shorter_def`, `llist_shorter_fromList`,
`llist_shorter_lnth`) live in `Flapjack/Misc/LprefixLub.lean`, the primary Lean
counterpart of the pinned HOL script `lprefix_lubScript.sml`.  The helper
lemmas they depend on -- `LTAKE_LLENGTH_SOME`, `LTAKE_LNTH_EL` and
`lnth_some_down_closed` -- come from the external lazy-list library
(`HOL/src/coalgebras/llistScript.sml`), whose snapshot is not one of the pinned
external sources, so they stay here and are untagged. -/

/-- A `some` length forces finiteness. -/
theorem LFinite_of_llength_eq_some {ll : HolLList α} {n : Nat} (h : llength ll = some n) :
    LFinite ll := by
  by_cases hfin : LFinite ll
  · exact hfin
  · unfold llength at h
    rw [if_neg hfin] at h
    exact (Option.some_ne_none n h.symm).elim

/-- A `some` length is exactly the (unique) `LLengthRel` witness. -/
theorem LLengthRel_of_llength_eq_some {ll : HolLList α} {n : Nat}
    (h : llength ll = some n) : LLengthRel ll n := by
  obtain ⟨m, hm, hrel⟩ := llength_spec (LFinite_of_llength_eq_some h)
  rw [Option.some.inj (hm.symm.trans h)] at hrel
  exact hrel

/-- A `none` length means the list is infinite. -/
theorem not_LFinite_of_llength_eq_none {ll : HolLList α} (h : llength ll = none) :
    ¬ LFinite ll := by
  intro hfin
  unfold llength at h
  rw [if_pos hfin] at h
  exact Option.some_ne_none _ h

/-- A `LLengthRel` bound makes the representation defined at every earlier
    index. -/
theorem lnth_some_of_LLengthRel {ll : HolLList α} {n : Nat} (h : LLengthRel ll n) :
    ∀ k, k < n → ∃ x, lnth k ll = some x := by
  induction h with
  | lnil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | lcons hd m t _ ih =>
      intro k hk
      cases k with
      | zero => exact ⟨hd, by rw [lnth_eq_rep]; simp [lcons]⟩
      | succ j =>
          have hj : j < m := Nat.lt_of_succ_lt_succ hk
          obtain ⟨x, hx⟩ := ih j hj
          exact ⟨x, by rw [lnth_eq_rep] at hx ⊢; simpa [lcons] using hx⟩

/-- A `LLengthRel` bound makes the representation `none` from that bound on. -/
theorem lnth_none_of_LLengthRel {ll : HolLList α} {n k : Nat} (h : LLengthRel ll n)
    (hk : n ≤ k) : lnth k ll = none := by
  rw [lnth_eq_rep]
  exact rep_none_of_LLengthRel h k hk

/-- An infinite lazy list is defined at every index. -/
theorem lnth_some_of_not_LFinite {ll : HolLList α} (h : ¬ LFinite ll) (n : Nat) :
    ∃ x, lnth n ll = some x := by
  rw [lnth_eq_rep]
  exact Option.ne_none_iff_exists'.mp fun hn => h (LFinite_of_rep_none hn)

/-- `ltake` returns a list of exactly its first argument's length. -/
theorem ltake_length {n : Nat} {ll : HolLList α} {l : List α}
    (h : ltake n ll = some l) : l.length = n :=
  (ltake_spec n ll l h).1

/-- HOL `LTAKE_LLENGTH_SOME` (`llistScript.sml:2260-2262`). -/
theorem LTAKE_LLENGTH_SOME {ll : HolLList α} {n : Nat} (h : llength ll = some n) :
    ∃ l, ltake n ll = some l ∧ toList ll = some l := by
  have hfin := LFinite_of_llength_eq_some h
  obtain ⟨l, hl⟩ := ltake_of_LLengthRel (LLengthRel_of_llength_eq_some h)
  refine ⟨l, hl, ?_⟩
  unfold toList
  rw [if_pos hfin, h]
  simpa using hl

/-- HOL `LTAKE_LNTH_EL` (`llistScript.sml:1067-1075`); HOL's total `EL m l` is
    rendered as `l.get ⟨m, _⟩` under the length fact `l.length = n` supplied by
    `ltake n ll = some l`, so the index bound is discharged rather than total. -/
theorem LTAKE_LNTH_EL {n : Nat} {ll : HolLList α} {m : Nat} {l : List α}
    (h : ltake n ll = some l) (hm : m < n) :
    lnth m ll = some (l.get ⟨m, by rw [ltake_length h]; exact hm⟩) := by
  rw [lnth_eq_rep]
  exact (ltake_spec n ll l h).2 m (by rw [ltake_length h]; exact hm)

/-- HOL `lnth_some_down_closed` (`llistScript.sml:1478-1485`): a value at `n1`
    is witnessed at every smaller index by some (possibly different) value. -/
theorem lnth_some_down_closed {ll : HolLList α} {x : α} {n1 n2 : Nat}
    (h : lnth n1 ll = some x) (hle : n2 ≤ n1) : ∃ y, lnth n2 ll = some y := by
  by_cases hnone : lnth n2 ll = none
  · rw [lnth_none_mono ll hnone hle] at h
    exact absurd h (by simp)
  · exact Option.ne_none_iff_exists'.mp hnone


/-! Prefix-order support over the canonical lazy-list representation. -/

/-- Membership is inherited along `lprefix` at the representation level: an
    `lprefix`-smaller list is `some` at `n` only where the larger one is. -/
theorem lprefix_rep {a b : HolLList α} (h : lprefix a b) {n : Nat} {x : α}
    (ha : a.rep n = some x) : b.rep n = some x := by
  unfold lprefix at h
  cases hta : toList a with
  | none =>
      rw [hta] at h
      subst h
      exact ha
  | some xs =>
      rw [hta] at h
      have hra := toList_eq_some_rep hta n
      rw [hra] at ha
      by_cases hn : n < xs.length
      · rw [dif_pos hn] at ha
        injection ha with hx
        cases htb : toList b with
        | none =>
            rw [htb] at h
            obtain ⟨_, hrep⟩ := ltake_spec xs.length b xs h
            rw [hrep n hn, hx]
        | some ys =>
            rw [htb] at h
            have hrb := toList_eq_some_rep htb n
            rw [hrb]
            have hnys : n < ys.length := Nat.lt_of_lt_of_le hn h.length_le
            rw [dif_pos hnys]
            obtain ⟨zs, rfl⟩ := h
            rw [List.getElem_append_left hn, hx]
      · rw [dif_neg hn] at ha
        exact absurd ha (by simp)

/-- `lprefix` is reflexive. -/
theorem lprefix_refl (ll : HolLList α) : lprefix ll ll := by
  unfold lprefix
  cases toList ll with
  | none => rfl
  | some xs => exact ⟨[], by simp⟩

/-- Flapjack-only SOME-index corollary of prefix agreement. HOL LPREFIX_NTH
    is an iff using less_opt and LLENGTH, so this direction-only helper does
    not carry that theorem's tag. -/
theorem lprefix_lnth {a b : HolLList α} (h : lprefix a b) {n : Nat} {x : α}
    (ha : lnth n a = some x) : lnth n b = some x := by
  rw [lnth_eq_rep] at ha ⊢
  exact lprefix_rep h ha

/-- Curried convenience form of antisymmetry. The separately tagged
`lprefixAntisymHOL` retains HOL's conjunction premise. -/
theorem lprefix_antisym {a b : HolLList α} (hab : lprefix a b) (hba : lprefix b a) :
    a = b := by
  have hrep : a.rep = b.rep := funext fun n => by
    cases ha : a.rep n with
    | none =>
        cases hb : b.rep n with
        | none => rfl
        | some y =>
            have := lprefix_rep hba hb
            rw [ha] at this
            exact absurd this (by simp)
    | some x => exact (lprefix_rep hab ha).symm
  obtain ⟨ra, oka⟩ := a
  obtain ⟨rb, okb⟩ := b
  subst hrep
  exact congrArg (fun o => (⟨ra, o⟩ : HolLList α)) (Subsingleton.elim oka okb)

/-- Converse of `lprefix_rep`: if `b` is defined wherever `a` is, then `a` is
    an `lprefix` of `b`. -/
theorem lprefix_of_rep_agree {a b : HolLList α}
    (h : ∀ n x, a.rep n = some x → b.rep n = some x) : lprefix a b := by
  unfold lprefix
  cases ha : toList a with
  | none =>
      dsimp only
      apply ext_of_rep
      intro n
      obtain ⟨x, hx⟩ := rep_some_of_toList_none ha n
      rw [hx, h n x hx]
  | some xs =>
      dsimp only
      cases hb : toList b with
      | none =>
          dsimp only
          apply ltake_of_rep
          intro i hi
          have hai : a.rep i = some xs[i] := by
            rw [toList_eq_some_rep ha i, dif_pos hi]
          exact h i xs[i] hai
      | some ys =>
          dsimp only
          have hlt : xs.length ≤ ys.length := Nat.le_of_not_lt fun hys => by
            have hai : a.rep ys.length = some xs[ys.length] := by
              rw [toList_eq_some_rep ha ys.length, dif_pos hys]
            have hbi : b.rep ys.length = some xs[ys.length] := h _ _ hai
            have hby : b.rep ys.length = none := by
              rw [toList_eq_some_rep hb ys.length, dif_neg (Nat.lt_irrefl ys.length)]
            rw [hby] at hbi
            cases hbi
          rw [List.prefix_iff_eq_take]
          apply List.ext_getElem
          · simp [List.length_take, Nat.min_eq_left hlt]
          · intro j hj1 hj2
            rw [List.getElem_take]
            have haj : a.rep j = some xs[j] := by
              rw [toList_eq_some_rep ha j, dif_pos hj1]
            have hbj : b.rep j = some xs[j] := h j _ haj
            have hby : b.rep j = some ys[j] := by
              rw [toList_eq_some_rep hb j, dif_pos (Nat.lt_of_lt_of_le hj1 hlt)]
            rw [hby] at hbj
            exact (Option.some.inj hbj).symm

/-- Curried convenience form of transitivity. The separately tagged
`lprefixTransHOL` retains HOL's conjunction premise. -/
theorem lprefix_trans {a b c : HolLList α} (hab : lprefix a b) (hbc : lprefix b c) :
    lprefix a c :=
  lprefix_of_rep_agree fun _ _ h => lprefix_rep hbc (lprefix_rep hab h)

/-- Curried convenience form of common-upper-bound prefix comparability.
`prefixesLprefixTotalHOL` retains HOL's universal binders and conjunction premise.
-/
theorem lprefix_total_of_common {a b c : HolLList α} (ha : lprefix a c) (hb : lprefix b c) :
    lprefix a b ∨ lprefix b a := by
  by_cases hab : lprefix a b
  · exact Or.inl hab
  · right
    have hnot : ¬ ∀ n x, a.rep n = some x → b.rep n = some x :=
      fun hall => hab (lprefix_of_rep_agree hall)
    obtain ⟨n, hnotn⟩ : ∃ n, ¬ ∀ x, a.rep n = some x → b.rep n = some x :=
      Classical.not_forall.mp hnot
    obtain ⟨x, hnotx⟩ : ∃ x, ¬ (a.rep n = some x → b.rep n = some x) :=
      Classical.not_forall.mp hnotn
    have han : a.rep n = some x := by
      apply Classical.byContradiction
      intro h
      exact hnotx (fun h' => absurd h' h)
    have hbn : b.rep n ≠ some x := by
      intro h'
      exact hnotx (fun _ => h')
    have hbnone : b.rep n = none := by
      cases hbn' : b.rep n with
      | none => rfl
      | some y =>
          exfalso
          have hcx : c.rep n = some x := lprefix_rep ha han
          have hcy : c.rep n = some y := lprefix_rep hb hbn'
          rw [hcx] at hcy
          have hxy : x = y := Option.some.inj hcy
          exact hbn (by rw [hbn', hxy])
    apply lprefix_of_rep_agree
    intro m y hbm
    have hlt : m < n := by
      apply Classical.byContradiction
      intro hge
      have hmn : n ≤ m := Nat.le_of_not_lt hge
      have hnone := rep_none_of_le b hbnone hmn
      rw [hbm] at hnone
      exact absurd hnone (by simp)
    have hcy : c.rep m = some y := lprefix_rep hb hbm
    cases ham : a.rep m with
    | none =>
        have hnone := rep_none_of_le a ham (Nat.le_of_lt hlt)
        rw [han] at hnone
        exact absurd hnone (by simp)
    | some w =>
        have hcw : c.rep m = some w := lprefix_rep ha ham
        rw [hcw] at hcy
        have hwy : w = y := Option.some.inj hcy
        rw [← hwy]

/-- HOL `LPREFIX_ANTISYM` (2713-2714), with its conjunction premise intact.
The lazy-list carrier is the invariant subtype of `Nat → Option α`; `lprefix`
retains the source's finite/infinite `toList` cases (2655-2662).
-/
@[hol "hol4/src/coalgebras/llistScript.sml" "LPREFIX_ANTISYM"]
theorem lprefixAntisymHOL (a b : HolLList α) :
    lprefix a b ∧ lprefix b a → a = b :=
  fun h => lprefix_antisym h.1 h.2

/-- HOL `LPREFIX_TRANS` (2722-2723), with the source's two prefix conjuncts.
No finite-list, index-range or chain premise is added.
-/
@[hol "hol4/src/coalgebras/llistScript.sml" "LPREFIX_TRANS"]
theorem lprefixTransHOL (a b c : HolLList α) :
    lprefix a b ∧ lprefix b c → lprefix a c :=
  fun h => lprefix_trans h.1 h.2

/-- HOL `prefixes_lprefix_total` (2744-2747), retaining the common upper bound
and the universal list binders. This is comparability of two prefixes of one
list, not totality of prefix order on arbitrary lazy lists.
-/
@[hol "hol4/src/coalgebras/llistScript.sml" "prefixes_lprefix_total"]
theorem prefixesLprefixTotalHOL : ∀ c a b : HolLList α,
    lprefix a c ∧ lprefix b c → lprefix a b ∨ lprefix b a :=
  fun _ _ _ h => lprefix_total_of_common h.1 h.2

/-! ## `LDROP`, `LAPPEND` and `LFLATTEN`

Source: `hol4/src/coalgebras/llistScript.sml`. HOL defines `LAPPEND` and
`LFLATTEN` by `new_specification` over the coinductive `llist`; here they are
constructed from the representation function, and the specification equations
are proved as theorems. -/

open Classical in
/-- The least `k ≤ bound` with `p k`, if any. Flapjack infrastructure for HOL's
    `LEAST`: a structural recursion bounded by an existence witness, so this
    library does not depend on Mathlib's `Nat.find`. -/
noncomputable def leastUpTo (p : Nat → Prop) : Nat → Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 =>
      match leastUpTo p n with
      | some k => some k
      | none => if p (n + 1) then some (n + 1) else none

theorem leastUpTo_succ_some {p : Nat → Prop} {n k : Nat} (h : leastUpTo p n = some k) :
    leastUpTo p (n + 1) = some k := by
  unfold leastUpTo
  rw [h]

theorem leastUpTo_succ_none_true {p : Nat → Prop} {n : Nat}
    (h : leastUpTo p n = none) (hp : p (n + 1)) :
    leastUpTo p (n + 1) = some (n + 1) := by
  unfold leastUpTo
  rw [h, if_pos hp]

theorem leastUpTo_succ_none_false {p : Nat → Prop} {n : Nat}
    (h : leastUpTo p n = none) (hp : ¬ p (n + 1)) :
    leastUpTo p (n + 1) = none := by
  unfold leastUpTo
  rw [h, if_neg hp]

theorem leastUpTo_none {p : Nat → Prop} {n : Nat} (h : leastUpTo p n = none) :
    ∀ m, m ≤ n → ¬ p m := by
  induction n with
  | zero =>
      unfold leastUpTo at h
      by_cases hp : p 0
      · rw [if_pos hp] at h
        exact absurd h (by simp)
      · rw [if_neg hp] at h
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        exact hp
  | succ n ih =>
      cases hn : leastUpTo p n with
      | some k =>
          rw [leastUpTo_succ_some hn] at h
          exact absurd h (by simp)
      | none =>
          by_cases hp : p (n + 1)
          · rw [leastUpTo_succ_none_true hn hp] at h
            exact absurd h (by simp)
          · rw [leastUpTo_succ_none_false hn hp] at h
            intro m hm
            by_cases hmn : m ≤ n
            · exact ih hn m hmn
            · have hm' : m = n + 1 := by omega
              subst hm'
              exact hp

theorem leastUpTo_some {p : Nat → Prop} {n k : Nat} (h : leastUpTo p n = some k) :
    k ≤ n ∧ p k ∧ ∀ m, m < k → ¬ p m := by
  induction n generalizing k with
  | zero =>
      unfold leastUpTo at h
      by_cases hp : p 0
      · rw [if_pos hp] at h
        injection h with hk
        subst hk
        exact ⟨Nat.le_refl 0, hp, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
      · rw [if_neg hp] at h
        exact absurd h (by simp)
  | succ n ih =>
      cases hn : leastUpTo p n with
      | some k' =>
          rw [leastUpTo_succ_some hn] at h
          injection h with hk
          subst hk
          obtain ⟨hle, hp, hmin⟩ := ih hn
          exact ⟨by omega, hp, hmin⟩
      | none =>
          by_cases hp : p (n + 1)
          · rw [leastUpTo_succ_none_true hn hp] at h
            injection h with hk
            subst hk
            refine ⟨Nat.le_refl _, hp, ?_⟩
            intro m hm
            exact leastUpTo_none hn m (by omega)
          · rw [leastUpTo_succ_none_false hn hp] at h
            exact absurd h (by simp)

theorem leastUpTo_eq_some_of {p : Nat → Prop} {n k : Nat}
    (hk : p k) (hmin : ∀ m, m < k → ¬ p m) (hkn : k ≤ n) :
    leastUpTo p n = some k := by
  induction n with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      unfold leastUpTo
      rw [if_pos hk]
  | succ n ih =>
      by_cases hkn' : k ≤ n
      · rw [leastUpTo_succ_some (ih hkn')]
      · have hkn'' : k = n + 1 := by omega
        subst hkn''
        cases hn : leastUpTo p n with
        | some k' =>
            obtain ⟨hle, hp, _⟩ := leastUpTo_some hn
            exact absurd hp (hmin k' (by omega))
        | none =>
            rw [leastUpTo_succ_none_true hn hk]

open Classical in
/-- The least index at which a lazy list's representation is `NONE`, if any.
    Flapjack infrastructure: HOL specifies `LAPPEND` coinductively, not by this
    scan. -/
noncomputable def firstNone (ll : HolLList α) : Option Nat :=
  if h : ∃ k, ll.rep k = none then
    leastUpTo (fun k => ll.rep k = none) (Classical.choose h)
  else none

theorem firstNone_spec {ll : HolLList α} {k : Nat} (h : firstNone ll = some k) :
    ll.rep k = none ∧ ∀ m, m < k → ll.rep m ≠ none := by
  unfold firstNone at h
  by_cases hex : ∃ k, ll.rep k = none
  · rw [dif_pos hex] at h
    obtain ⟨-, hk, hmin⟩ := leastUpTo_some h
    exact ⟨hk, hmin⟩
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

theorem firstNone_none {ll : HolLList α} (h : firstNone ll = none) :
    ∀ k, ll.rep k ≠ none := by
  unfold firstNone at h
  by_cases hex : ∃ k, ll.rep k = none
  · rw [dif_pos hex] at h
    exact absurd (Classical.choose_spec hex) (leastUpTo_none h _ (Nat.le_refl _))
  · exact fun k hk => hex ⟨k, hk⟩

theorem firstNone_eq_some_of_rep {ll : HolLList α} {k : Nat}
    (hk : ll.rep k = none) (hmin : ∀ m, m < k → ll.rep m ≠ none) :
    firstNone ll = some k := by
  have hex : ∃ j, ll.rep j = none := ⟨k, hk⟩
  have hk_le : k ≤ Classical.choose hex := by
    by_cases hlt : Classical.choose hex < k
    · exact absurd (Classical.choose_spec hex) (hmin (Classical.choose hex) hlt)
    · omega
  unfold firstNone
  rw [dif_pos hex]
  exact leastUpTo_eq_some_of hk hmin hk_le

theorem firstNone_eq_none_of_rep {ll : HolLList α} (h : ∀ k, ll.rep k ≠ none) :
    firstNone ll = none := by
  unfold firstNone
  rw [dif_neg]
  · intro hex
    obtain ⟨k, hk⟩ := hex
    exact h k hk

theorem firstNone_lnil : firstNone (lnil : HolLList α) = some 0 := by
  apply firstNone_eq_some_of_rep (k := 0)
  · rfl
  · intro m hm
    omega

theorem firstNone_lcons (h : α) (t : HolLList α) :
    firstNone (lcons h t) = (firstNone t).map (fun k => k + 1) := by
  cases ht : firstNone t with
  | none =>
      have hno := firstNone_none ht
      have hall : ∀ k, (lcons h t).rep k ≠ none := by
        intro k
        cases k with
        | zero => simp [lcons]
        | succ j => simpa [lcons] using hno j
      rw [firstNone_eq_none_of_rep hall]
      rfl
  | some k =>
      obtain ⟨hk, hmin⟩ := firstNone_spec ht
      have hk1 : (lcons h t).rep (k + 1) = none := by
        simpa [lcons] using hk
      have hmin1 : ∀ m, m < k + 1 → (lcons h t).rep m ≠ none := by
        intro m hm
        cases m with
        | zero => simp [lcons]
        | succ j =>
            have hj : j < k := by omega
            simpa [lcons] using hmin j hj
      rw [firstNone_eq_some_of_rep hk1 hmin1]
      rfl

/-- The representation of `LAPPEND l1 l2`: the elements of `l1` up to its first
    `NONE`, then the elements of `l2`. Flapjack infrastructure; the source
    equations are proved below as `lappendHOL_spec`. -/
noncomputable def lappendRep (l1 l2 : HolLList α) : Nat → Option α :=
  fun n =>
    match firstNone l1 with
    | some k => if n < k then l1.rep n else l2.rep (n - k)
    | none => l1.rep n

theorem lappendRep_ok (l1 l2 : HolLList α) : HolLrepOk (lappendRep l1 l2) := by
  intro n hn
  cases hf : firstNone l1 with
  | none =>
      have h1 : lappendRep l1 l2 n = l1.rep n := by simp [lappendRep, hf]
      have h2 : lappendRep l1 l2 (n + 1) = l1.rep (n + 1) := by simp [lappendRep, hf]
      rw [h2] at hn
      rw [h1]
      exact l1.ok n hn
  | some k =>
      obtain ⟨hk, hmin⟩ := firstNone_spec hf
      have h2 : lappendRep l1 l2 (n + 1) =
          if n + 1 < k then l1.rep (n + 1) else l2.rep (n + 1 - k) := by
        simp [lappendRep, hf]
      have h1 : lappendRep l1 l2 n =
          if n < k then l1.rep n else l2.rep (n - k) := by
        simp [lappendRep, hf]
      rw [h2] at hn
      rw [h1]
      by_cases hlt : n + 1 < k
      · rw [if_pos hlt] at hn
        rw [if_pos (by omega)]
        exact l1.ok n hn
      · rw [if_neg hlt] at hn
        by_cases hnk : n < k
        · rw [if_pos hnk]
          have hk1 : n = k - 1 := by omega
          rw [hk1]
          exact Option.isSome_iff_ne_none.mpr (hmin (k - 1) (by omega))
        · rw [if_neg hnk]
          have heq : n - k + 1 = n + 1 - k := by omega
          rw [← heq] at hn
          exact l2.ok (n - k) hn

/-- `LAPPEND` over the representation carrier. Carries no `@[hol]` tag:
    HOL declares `LAPPEND` by `new_specification` (`llistScript.sml:781`), and
    its specification statement is ported as the tagged `lappendHOL_spec`; this
    definition is the rep-level witness, the analogue of the `llist_Axiom`
    witness in HOL's own existence proof. -/
noncomputable def lappendHOL (l1 l2 : HolLList α) : HolLList α :=
  ⟨lappendRep l1 l2, lappendRep_ok l1 l2⟩

theorem lappendRep_lcons_zero (h : α) (t x : HolLList α) :
    lappendRep (lcons h t) x 0 = some h := by
  cases ht : firstNone t with
  | none =>
      have hf : firstNone (lcons h t) = none := by rw [firstNone_lcons, ht]; rfl
      have hlap : lappendRep (lcons h t) x 0 = (lcons h t).rep 0 := by
        simp [lappendRep, hf]
      have hrep : (lcons h t).rep 0 = some h := by simp [lcons]
      rw [hlap, hrep]
  | some k =>
      have hf : firstNone (lcons h t) = some (k + 1) := by rw [firstNone_lcons, ht]; rfl
      have hlap : lappendRep (lcons h t) x 0 = (lcons h t).rep 0 := by
        simp [lappendRep, hf]
      have hrep : (lcons h t).rep 0 = some h := by simp [lcons]
      rw [hlap, hrep]

theorem lappendRep_lcons_succ (h : α) (t x : HolLList α) (n : Nat) :
    lappendRep (lcons h t) x (n + 1) = lappendRep t x n := by
  cases ht : firstNone t with
  | none =>
      have hf : firstNone (lcons h t) = none := by rw [firstNone_lcons, ht]; rfl
      have h2 : lappendRep (lcons h t) x (n + 1) = (lcons h t).rep (n + 1) := by
        simp [lappendRep, hf]
      have h1 : lappendRep t x n = t.rep n := by simp [lappendRep, ht]
      have hrep : (lcons h t).rep (n + 1) = t.rep n := by simp [lcons]
      rw [h2, h1, hrep]
  | some k =>
      have hf : firstNone (lcons h t) = some (k + 1) := by rw [firstNone_lcons, ht]; rfl
      have h2 : lappendRep (lcons h t) x (n + 1) =
          if n + 1 < k + 1 then (lcons h t).rep (n + 1) else x.rep (n + 1 - (k + 1)) := by
        simp [lappendRep, hf]
      have h1 : lappendRep t x n =
          if n < k then t.rep n else x.rep (n - k) := by
        simp [lappendRep, ht]
      rw [h2, h1]
      by_cases hn : n < k
      · rw [if_pos (by omega), if_pos hn]
        simp [lcons]
      · rw [if_neg (by omega), if_neg hn]
        congr 1
        omega

/-- HOL `LAPPEND` (`llistScript.sml:781-785`, `new_specification`): the two
source equations for append (`:784-785`). -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LAPPEND"]
theorem lappendHOL_spec :
    (∀ x : HolLList α, lappendHOL lnil x = x) ∧
      (∀ (h : α) (t x : HolLList α),
        lappendHOL (lcons h t) x = lcons h (lappendHOL t x)) := by
  constructor
  · intro x
    apply ext_of_rep
    intro n
    have h1 : lappendRep (lnil : HolLList α) x n =
        if n < 0 then (lnil : HolLList α).rep n else x.rep (n - 0) := by
      simp [lappendRep, firstNone_lnil]
    simp only [lappendHOL]
    rw [h1]
    simp
  · intro h t x
    apply ext_of_rep
    intro n
    cases n with
    | zero =>
        simp only [lappendHOL]
        rw [lappendRep_lcons_zero]
        simp [lcons]
    | succ n =>
        simp only [lappendHOL]
        rw [lappendRep_lcons_succ]
        simp [lcons]

/-- HOL `LAPPEND_NIL_2ND` (`llistScript.sml:873-874`): appending nothing on the
right is the identity. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LAPPEND_NIL_2ND"]
theorem lappendHOL_nil_2nd : ∀ ll : HolLList α, lappendHOL ll lnil = ll := by
  intro ll
  apply ext_of_rep
  intro n
  cases hf : firstNone ll with
  | none =>
      have h : lappendRep ll lnil n = ll.rep n := by simp [lappendRep, hf]
      simpa [lappendHOL] using h
  | some k =>
      obtain ⟨hk, hmin⟩ := firstNone_spec hf
      have h : lappendRep ll lnil n =
          if n < k then ll.rep n else lnil.rep (n - k) := by
        simp [lappendRep, hf]
      simp only [lappendHOL]
      rw [h]
      by_cases hn : n < k
      · rw [if_pos hn]
      · rw [if_neg hn]
        have hnone : ll.rep n = none := rep_none_of_le ll hk (by omega)
        simp [lnil, hnone]

/-- HOL `LAPPEND_EQ_LNIL` (`llistScript.sml:836-837`): append is empty exactly
when both operands are. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LAPPEND_EQ_LNIL"]
theorem lappendHOL_eq_lnil (l1 l2 : HolLList α) :
    (lappendHOL l1 l2 = lnil) ↔ (l1 = lnil ∧ l2 = lnil) := by
  constructor
  · intro h
    have hall : ∀ n, lappendRep l1 l2 n = none := by
      intro n
      have : (lappendHOL l1 l2).rep n = none := by rw [h]; rfl
      simpa [lappendHOL] using this
    have h1 : l1 = lnil := by
      apply eq_lnil_of_rep_none
      intro n
      by_cases hrep : l1.rep n = none
      · exact hrep
      · cases hf : firstNone l1 with
        | none =>
            have hthis : lappendRep l1 l2 n = l1.rep n := by simp [lappendRep, hf]
            have hn_none : lappendRep l1 l2 n = none := hall n
            rw [hthis] at hn_none
            exact absurd hn_none hrep
        | some k =>
            obtain ⟨hk, hmin⟩ := firstNone_spec hf
            by_cases hn : n < k
            · have hthis : lappendRep l1 l2 n = l1.rep n := by simp [lappendRep, hf, hn]
              have hn_none : lappendRep l1 l2 n = none := hall n
              rw [hthis] at hn_none
              exact absurd hn_none hrep
            · have hnone : l1.rep n = none := rep_none_of_le l1 hk (by omega)
              exact absurd hnone hrep
    subst h1
    exact ⟨rfl, (lappendHOL_spec.1 l2).symm.trans h⟩
  · rintro ⟨rfl, rfl⟩
    exact lappendHOL_spec.1 lnil

/-- HOL `LDROP` (`llistScript.sml:1275-1277`): drop `n` elements. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LDROP"]
def ldropHOL : Nat → HolLList α → Option (HolLList α)
  | 0, ll => some ll
  | n + 1, ll => (ll.ltl.map (fun t => ldropHOL n t)).join

theorem ldropHOL_succ (n : Nat) (ll : HolLList α) :
    ldropHOL (n + 1) ll = (ll.ltl.map (fun t => ldropHOL n t)).join := rfl

theorem ldropHOL_succ_lcons (n : Nat) (h : α) (t : HolLList α) :
    ldropHOL (n + 1) (lcons h t) = ldropHOL n t := by
  rw [ldropHOL_succ, ltl_lcons]
  rfl

theorem ldropHOL_one_lcons {γ : Type} (inner : γ) (rest : HolLList γ) :
    ldropHOL 1 (lcons inner rest) = some rest := by
  have h1 : ldropHOL 1 (lcons inner rest) = ldropHOL (0 + 1) (lcons inner rest) := rfl
  rw [h1, ldropHOL_succ_lcons, show ldropHOL 0 rest = some rest from rfl]

open Classical in
/-- The index of the first nonempty member of a lazy list of lazy lists, if
    any. Flapjack infrastructure: HOL's `LFLATTEN` witness uses
    `LEAST n. ?e. (SOME e = LNTH n ll) /\ ~(e = [||])`. -/
noncomputable def firstNonempty (ll : HolLList (HolLList α)) : Option Nat :=
  if h : ∃ k, ∃ inner : HolLList α, ll.rep k = some inner ∧ inner.rep 0 ≠ none then
    leastUpTo (fun k => ∃ inner : HolLList α, ll.rep k = some inner ∧ inner.rep 0 ≠ none)
      (Classical.choose h)
  else none

theorem firstNonempty_spec {ll : HolLList (HolLList α)} {k : Nat}
    (h : firstNonempty ll = some k) :
    (∃ inner : HolLList α, ll.rep k = some inner ∧ inner.rep 0 ≠ none) ∧
      ∀ m, m < k → ¬ ∃ inner : HolLList α, ll.rep m = some inner ∧ inner.rep 0 ≠ none := by
  unfold firstNonempty at h
  by_cases hex : ∃ k, ∃ inner : HolLList α, ll.rep k = some inner ∧ inner.rep 0 ≠ none
  · rw [dif_pos hex] at h
    obtain ⟨-, hk, hmin⟩ := leastUpTo_some h
    exact ⟨hk, hmin⟩
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

theorem firstNonempty_none {ll : HolLList (HolLList α)} (h : firstNonempty ll = none) :
    ∀ (k : Nat) (inner : HolLList α), ll.rep k = some inner → inner.rep 0 = none := by
  intro k inner hk
  by_cases hne : inner.rep 0 = none
  · exact hne
  · have hex : ∃ j, ∃ inner : HolLList α, ll.rep j = some inner ∧ inner.rep 0 ≠ none :=
      ⟨k, inner, hk, hne⟩
    unfold firstNonempty at h
    rw [dif_pos hex] at h
    exact absurd (Classical.choose_spec hex) (leastUpTo_none h _ (Nat.le_refl _))

theorem firstNonempty_eq_some_of_rep {ll : HolLList (HolLList α)} {k : Nat}
    (hk : ∃ inner : HolLList α, ll.rep k = some inner ∧ inner.rep 0 ≠ none)
    (hmin : ∀ m, m < k → ¬ ∃ inner : HolLList α, ll.rep m = some inner ∧ inner.rep 0 ≠ none) :
    firstNonempty ll = some k := by
  have hex : ∃ j, ∃ inner : HolLList α, ll.rep j = some inner ∧ inner.rep 0 ≠ none :=
    ⟨k, hk⟩
  have hk_le : k ≤ Classical.choose hex := by
    by_cases hlt : Classical.choose hex < k
    · exact absurd (Classical.choose_spec hex) (hmin (Classical.choose hex) hlt)
    · omega
  unfold firstNonempty
  rw [dif_pos hex]
  exact leastUpTo_eq_some_of hk hmin hk_le

theorem firstNonempty_eq_none_of {ll : HolLList (HolLList α)}
    (h : ∀ (k : Nat) (inner : HolLList α), ll.rep k = some inner → inner.rep 0 = none) :
    firstNonempty ll = none := by
  unfold firstNonempty
  rw [dif_neg]
  · intro hex
    obtain ⟨k, inner, hk, hne⟩ := hex
    exact hne (h k inner hk)

theorem firstNonempty_lnil : firstNonempty (lnil : HolLList (HolLList α)) = none :=
  firstNonempty_eq_none_of (fun _ _ h => by simp [lnil] at h)

theorem firstNonempty_lcons (inner : HolLList α) (rest : HolLList (HolLList α)) :
    firstNonempty (lcons inner rest) =
      if inner.rep 0 = none then (firstNonempty rest).map (fun k => k + 1) else some 0 := by
  cases hinner : inner.rep 0 with
  | some v =>
      have hsome : ∃ i : HolLList α, (lcons inner rest).rep 0 = some i ∧ i.rep 0 ≠ none :=
        ⟨inner, by simp [lcons], by simp [hinner]⟩
      have hmin : ∀ m, m < 0 → ¬ ∃ i : HolLList α,
          (lcons inner rest).rep m = some i ∧ i.rep 0 ≠ none := by
        intro m hm
        omega
      rw [firstNonempty_eq_some_of_rep hsome hmin, if_neg (by simp)]
  | none =>
      rw [if_pos rfl]
      cases hr : firstNonempty rest with
      | none =>
          apply firstNonempty_eq_none_of
          intro k i hk
          cases k with
          | zero =>
              simp [lcons] at hk
              rw [← hk]
              exact hinner
          | succ j =>
              have hk' : rest.rep j = some i := by simpa [lcons] using hk
              exact firstNonempty_none hr j i hk'
      | some k =>
          obtain ⟨⟨i, hi, hne⟩, hmin⟩ := firstNonempty_spec hr
          have hsome : ∃ i' : HolLList α,
              (lcons inner rest).rep (k + 1) = some i' ∧ i'.rep 0 ≠ none :=
            ⟨i, by simpa [lcons] using hi, hne⟩
          have hmin' : ∀ m, m < k + 1 → ¬ ∃ i' : HolLList α,
              (lcons inner rest).rep m = some i' ∧ i'.rep 0 ≠ none := by
            intro m hm
            cases m with
            | zero =>
                intro ⟨i', hi0, hnei⟩
                simp [lcons] at hi0
                exact hnei (by rw [← hi0]; exact hinner)
            | succ j =>
                intro ⟨i', hj, hnei⟩
                have hj' : rest.rep j = some i' := by simpa [lcons] using hj
                exact hmin j (by omega) ⟨i', hj', hnei⟩
          rw [firstNonempty_eq_some_of_rep hsome hmin']
          rfl

/-- The representation of `LFLATTEN`: the elements of the first nonempty member,
    then the flattening of the remainder. Flapjack infrastructure. -/
noncomputable def lflattenRep (ll : HolLList (HolLList α)) : Nat → Option α
  | 0 =>
      match firstNonempty ll with
      | none => none
      | some k => ((ll.rep k).map (fun inner => inner.rep 0)).join
  | n + 1 =>
      match firstNonempty ll with
      | none => none
      | some k =>
          match ll.rep k with
          | none => none
          | some inner =>
              lflattenRep
                (lcons (inner.ltl.getD lnil) ((ldropHOL (k + 1) ll).getD lnil)) n

theorem lflattenRep_ok (ll : HolLList (HolLList α)) : HolLrepOk (lflattenRep ll) := by
  intro n
  induction n generalizing ll with
  | zero =>
      intro hn
      cases hf : firstNonempty ll with
      | none =>
          have h1 : lflattenRep ll (0 + 1) = none := by simp [lflattenRep, hf]
          rw [h1] at hn
          simp at hn
      | some k =>
          obtain ⟨⟨inner, hrep, hne⟩, _⟩ := firstNonempty_spec hf
          have h0 : lflattenRep ll 0 = inner.rep 0 := by
            simp [lflattenRep, hf, hrep]
          rw [h0]
          exact Option.isSome_iff_ne_none.mpr hne
  | succ n ih =>
      intro hn
      cases hf : firstNonempty ll with
      | none =>
          have h1 : lflattenRep ll (n + 1 + 1) = none := by simp [lflattenRep, hf]
          rw [h1] at hn
          simp at hn
      | some k =>
          obtain ⟨⟨inner, hrep, hne⟩, _⟩ := firstNonempty_spec hf
          have h2 : lflattenRep ll (n + 2) =
              lflattenRep
                (lcons (inner.ltl.getD lnil) ((ldropHOL (k + 1) ll).getD lnil)) (n + 1) := by
            simp [lflattenRep, hf, hrep]
          have h1 : lflattenRep ll (n + 1) =
              lflattenRep
                (lcons (inner.ltl.getD lnil) ((ldropHOL (k + 1) ll).getD lnil)) n := by
            simp [lflattenRep, hf, hrep]
          rw [h2] at hn
          rw [h1]
          exact ih _ hn

/-- `LFLATTEN` over the representation carrier. Carries no `@[hol]` tag: HOL
    declares `LFLATTEN` by `new_specification` (`llistScript.sml:1895`), whose
    stated equation inspects `LL_ALL ($= LNIL) ll`; that raw specification is
    not ported yet (it needs `LL_ALL`). The construction here is the rep-level
    `LEAST`-index flattening that HOL's existence proof uses, and the HOL
    characterising theorem `LFLATTEN_THM` is ported as `lflattenHOL_THM`. -/
noncomputable def lflatten (ll : HolLList (HolLList α)) : HolLList α :=
  ⟨lflattenRep ll, lflattenRep_ok ll⟩

theorem lflattenRep_lcons_lnil (t : HolLList (HolLList α)) (n : Nat) :
    lflattenRep (lcons (lnil : HolLList α) t) n = lflattenRep t n := by
  have hfe : firstNonempty (lcons (lnil : HolLList α) t) =
      (firstNonempty t).map (fun k => k + 1) := by
    rw [firstNonempty_lcons]
    simp [lnil]
  cases ht : firstNonempty t with
  | none =>
      have hf : firstNonempty (lcons (lnil : HolLList α) t) = none := by
        rw [hfe, ht]
        rfl
      cases n with
      | zero => simp [lflattenRep, hf, ht]
      | succ n => simp [lflattenRep, hf, ht]
  | some k =>
      have hf : firstNonempty (lcons (lnil : HolLList α) t) = some (k + 1) := by
        rw [hfe, ht]
        rfl
      obtain ⟨⟨inner, hrep, hne⟩, _⟩ := firstNonempty_spec ht
      have hrep' : (lcons (lnil : HolLList α) t).rep (k + 1) = some inner := by
        simpa [lcons] using hrep
      cases n with
      | zero =>
          simp [lflattenRep, hf, ht, hrep, hrep']
      | succ n =>
          have hX : lcons (inner.ltl.getD lnil)
              ((ldropHOL ((k + 1) + 1) (lcons (lnil : HolLList α) t)).getD lnil) =
              lcons (inner.ltl.getD lnil) ((ldropHOL (k + 1) t).getD lnil) := by
            rw [ldropHOL_succ_lcons]
          simp only [lflattenRep, hf, ht, hrep, hrep', hX]

/-- HOL `LFLATTEN_THM` (`llistScript.sml:1967-1971`): the three flattening
equations. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LFLATTEN_THM"]
theorem lflattenHOL_THM :
    lflatten (lnil : HolLList (HolLList α)) = lnil ∧
      (∀ t : HolLList (HolLList α),
        lflatten (lcons (lnil : HolLList α) t) = lflatten t) ∧
      (∀ (h : α) (t : HolLList α) (tl : HolLList (HolLList α)),
        lflatten (lcons (lcons h t) tl) = lcons h (lflatten (lcons t tl))) := by
  refine ⟨?_, ?_, ?_⟩
  · apply eq_lnil_of_rep_none
    intro n
    cases n with
    | zero => simp [lflatten, lflattenRep, firstNonempty_lnil]
    | succ n => simp [lflatten, lflattenRep, firstNonempty_lnil]
  · intro t
    apply ext_of_rep
    intro n
    simp only [lflatten]
    exact lflattenRep_lcons_lnil t n
  · intro h t tl
    apply ext_of_rep
    intro n
    have hf : firstNonempty (lcons (lcons h t) tl) = some 0 := by
      rw [firstNonempty_lcons]
      simp [lcons]
    cases n with
    | zero =>
        have h0 : lflattenRep (lcons (lcons h t) tl) 0 = some h := by
          simp only [lflattenRep, hf]
          simp [lcons]
        simp only [lflatten]
        rw [h0]
        simp [lcons]
    | succ n =>
        have hdrop : ldropHOL (0 + 1) (lcons (lcons h t) tl) = some tl :=
          ldropHOL_one_lcons (lcons h t) tl
        have htl : (lcons h t).ltl.getD (lnil : HolLList α) = t := by
          rw [ltl_lcons]
          rfl
        have hX : lcons ((lcons h t).ltl.getD lnil)
            ((ldropHOL (0 + 1) (lcons (lcons h t) tl)).getD lnil) =
            lcons t tl := by
          rw [hdrop, htl]
          rfl
        have hstep : lflattenRep (lcons (lcons h t) tl) (n + 1) =
            lflattenRep (lcons t tl) n := by
          simp only [lflattenRep, hf]
          have hrep : (lcons (lcons h t) tl).rep 0 = some (lcons h t) := by
            simp [lcons]
          rw [hrep]
          show lflattenRep (lcons ((lcons h t).ltl.getD lnil)
              ((ldropHOL (0 + 1) (lcons (lcons h t) tl)).getD lnil)) n =
            lflattenRep (lcons t tl) n
          rw [hX]
        simp only [lflatten]
        rw [hstep]
        simp [lcons]

/-! ## Append algebra

HOL's `LAPPEND_ASSOC` (`llistScript.sml:843`) and the finite facts about append
used by `pan_itreeEquivProofScript.sml`. -/

/-- Where `LAPPEND` stops: never when the left operand is infinite, at `k + j`
    when the left stops at `k` and the right at `j`. Flapjack infrastructure for
    the append laws below. -/
theorem firstNone_lappend (l1 l2 : HolLList α) :
    firstNone (lappendHOL l1 l2) =
      (match firstNone l1 with
       | none => none
       | some k =>
           match firstNone l2 with
           | none => none
           | some j => some (k + j)) := by
  cases h1 : firstNone l1 with
  | none =>
      have hno := firstNone_none h1
      rw [firstNone_eq_none_of_rep]
      intro n
      simp only [lappendHOL, lappendRep, h1]
      exact hno n
  | some k =>
      obtain ⟨hk, hmin⟩ := firstNone_spec h1
      cases h2 : firstNone l2 with
      | none =>
          have hno := firstNone_none h2
          rw [firstNone_eq_none_of_rep]
          intro n
          simp only [lappendHOL, lappendRep, h1]
          by_cases hn : n < k
          · rw [if_pos hn]
            exact hmin n hn
          · rw [if_neg hn]
            exact hno (n - k)
      | some j =>
          obtain ⟨hj, hmin2⟩ := firstNone_spec h2
          have hrep_none : (lappendHOL l1 l2).rep (k + j) = none := by
            simp only [lappendHOL, lappendRep, h1]
            rw [if_neg (by omega)]
            rw [show k + j - k = j from by omega]
            exact hj
          have hrep_min : ∀ m, m < k + j → (lappendHOL l1 l2).rep m ≠ none := by
            intro m hm
            simp only [lappendHOL, lappendRep, h1]
            by_cases hmk : m < k
            · rw [if_pos hmk]
              exact hmin m hmk
            · rw [if_neg hmk]
              exact hmin2 (m - k) (by omega)
          rw [firstNone_eq_some_of_rep hrep_none hrep_min]

/-- The representation of an append, exposed for rewriting. -/
theorem lappendRep_rep (l1 l2 : HolLList α) (n : Nat) :
    (lappendHOL l1 l2).rep n = lappendRep l1 l2 n := rfl

/-- An append whose left operand never stops copies that operand. -/
theorem lappendRep_of_firstNone_none {l1 l2 : HolLList α} (h : firstNone l1 = none)
    (n : Nat) : lappendRep l1 l2 n = l1.rep n := by
  simp [lappendRep, h]

/-- An append whose left operand stops at `k` copies it up to `k`, then the
    right operand. -/
theorem lappendRep_of_firstNone_some {l1 l2 : HolLList α} {k : Nat}
    (h : firstNone l1 = some k) (n : Nat) :
    lappendRep l1 l2 n = if n < k then l1.rep n else l2.rep (n - k) := by
  simp [lappendRep, h]

/-- HOL `LAPPEND_ASSOC` (`llistScript.sml:843-849`): append is associative. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LAPPEND_ASSOC"]
theorem lappendHOL_assoc (ll1 ll2 ll3 : HolLList α) :
    lappendHOL (lappendHOL ll1 ll2) ll3 = lappendHOL ll1 (lappendHOL ll2 ll3) := by
  apply ext_of_rep
  intro n
  simp only [lappendRep_rep]
  cases h1 : firstNone ll1 with
  | none =>
      have h12 : firstNone (lappendHOL ll1 ll2) = none := by
        rw [firstNone_lappend, h1]
      rw [lappendRep_of_firstNone_none h12, lappendRep_of_firstNone_none h1,
        lappendRep_rep, lappendRep_of_firstNone_none h1]
  | some k =>
      cases h2 : firstNone ll2 with
      | none =>
          have h12 : firstNone (lappendHOL ll1 ll2) = none := by
            rw [firstNone_lappend, h1, h2]
          rw [lappendRep_of_firstNone_none h12, lappendRep_of_firstNone_some h1,
            lappendRep_rep, lappendRep_of_firstNone_some h1]
          by_cases hn : n < k
          · rw [if_pos hn, if_pos hn]
          · rw [if_neg hn, if_neg hn]
            rw [lappendRep_rep, lappendRep_of_firstNone_none h2]
      | some j =>
          have h12 : firstNone (lappendHOL ll1 ll2) = some (k + j) := by
            rw [firstNone_lappend, h1, h2]
          rw [lappendRep_of_firstNone_some h12, lappendRep_of_firstNone_some h1,
            lappendRep_rep, lappendRep_of_firstNone_some h1,
            lappendRep_rep, lappendRep_of_firstNone_some h2]
          by_cases hn : n < k
          · rw [if_pos hn, if_pos hn, if_pos (by omega)]
          · rw [if_neg hn, if_neg hn]
            by_cases hnj : n - k < j
            · simp only [if_pos (by omega : n < k + j), if_pos hnj]
            · simp only [if_neg (by omega : ¬ n < k + j), if_neg hnj]
              congr 1
              omega


/-- A nonempty lazy list has an element at index zero: the coherence invariant
    forbids a `none` at `0` followed by a `some`. -/
theorem rep_zero_ne_none_of_ne_lnil {ll : HolLList α} (h : ll ≠ lnil) : ll.rep 0 ≠ none := by
  intro h0
  apply h
  apply eq_lnil_of_rep_none
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact rep_none_succ ll ih

/-- HOL `LFINITE_APPEND` (`llistScript.sml:1048-1049`): an append is finite
    exactly when both operands are. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LFINITE_APPEND"]
theorem lfinite_lappendHOL (ll1 ll2 : HolLList α) :
    LFinite (lappendHOL ll1 ll2) ↔ LFinite ll1 ∧ LFinite ll2 := by
  constructor
  · intro h
    obtain ⟨n, hnrel⟩ := exists_LLengthRel_of_LFinite h
    have hnone : (lappendHOL ll1 ll2).rep n = none :=
      rep_none_of_LLengthRel hnrel n (Nat.le_refl n)
    cases h1 : firstNone ll1 with
    | none =>
        have hn1 : ll1.rep n ≠ none := firstNone_none h1 n
        simp only [lappendHOL, lappendRep, h1] at hnone
        exact absurd hnone hn1
    | some k =>
        have hk : ll1.rep k = none := (firstNone_spec h1).1
        refine ⟨LFinite_of_rep_none hk, ?_⟩
        cases h2 : firstNone ll2 with
        | none =>
            have hn2 : ll2.rep (n - k) ≠ none := firstNone_none h2 (n - k)
            by_cases hnk : n < k
            · have hn1 : ll1.rep n ≠ none := (firstNone_spec h1).2 n hnk
              simp only [lappendHOL, lappendRep, h1] at hnone
              rw [if_pos hnk] at hnone
              exact absurd hnone hn1
            · simp only [lappendHOL, lappendRep, h1] at hnone
              rw [if_neg hnk] at hnone
              exact absurd hnone hn2
        | some j =>
            exact LFinite_of_rep_none (firstNone_spec h2).1
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := exists_LLengthRel_of_LFinite h1
    obtain ⟨j, hj⟩ := exists_LLengthRel_of_LFinite h2
    have hkrep : ll1.rep k = none := rep_none_of_LLengthRel hk k (Nat.le_refl k)
    have hjrep : ll2.rep j = none := rep_none_of_LLengthRel hj j (Nat.le_refl j)
    cases hf1 : firstNone ll1 with
    | none =>
        exact absurd (firstNone_none hf1 k) (by rw [hkrep]; simp)
    | some k' =>
        cases hf2 : firstNone ll2 with
        | none =>
            exact absurd (firstNone_none hf2 j) (by rw [hjrep]; simp)
        | some j' =>
            have hfl : firstNone (lappendHOL ll1 ll2) = some (k' + j') := by
              rw [firstNone_lappend, hf1, hf2]
            exact LFinite_of_rep_none (firstNone_spec hfl).1

/-- HOL `LFINITE_LAPPEND_IMP_NIL` (`llistScript.sml:1094-1096`): appending to a
    finite list leaves it unchanged only if the appended list is empty. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LFINITE_LAPPEND_IMP_NIL"]
theorem lfinite_lappendHOL_imp_lnil {ll l2 : HolLList α} (hfin : LFinite ll)
    (h : lappendHOL ll l2 = ll) : l2 = lnil := by
  by_cases hnil : l2 = lnil
  · exact hnil
  · exfalso
    have hrep0 : l2.rep 0 ≠ none := rep_zero_ne_none_of_ne_lnil hnil
    obtain ⟨k, hk⟩ := exists_LLengthRel_of_LFinite hfin
    have hkrep : ll.rep k = none := rep_none_of_LLengthRel hk k (Nat.le_refl k)
    cases hf : firstNone ll with
    | none =>
        exact absurd (firstNone_none hf k) (by rw [hkrep]; simp)
    | some k' =>
        have hk' : ll.rep k' = none := (firstNone_spec hf).1
        have hlhs : (lappendHOL ll l2).rep k' = l2.rep 0 := by
          simp only [lappendRep_rep, lappendRep_of_firstNone_some hf]
          rw [if_neg (by omega)]
          rw [show k' - k' = 0 from by omega]
        rw [h] at hlhs
        exact absurd (hlhs.symm.trans hk') hrep0

/-- HOL `LAPPEND11_FINITE1` (`llistScript.sml:4023-4025`): appending on the left
    of a finite list is injective. -/
@[hol "hol4/src/coalgebras/llistScript.sml" "LAPPEND11_FINITE1"]
theorem lappendHOL_left_cancel {l1 l2 l3 : HolLList α} (hfin : LFinite l1) :
    lappendHOL l1 l2 = lappendHOL l1 l3 ↔ l2 = l3 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_LLengthRel_of_LFinite hfin
    have hkrep : l1.rep k = none := rep_none_of_LLengthRel hk k (Nat.le_refl k)
    cases hf : firstNone l1 with
    | none =>
        exact absurd (firstNone_none hf k) (by rw [hkrep]; simp)
    | some m =>
        apply ext_of_rep
        intro n
        have hl : (lappendHOL l1 l2).rep (m + n) = l2.rep n := by
          simp only [lappendRep_rep, lappendRep_of_firstNone_some hf]
          rw [if_neg (by omega)]
          rw [show m + n - m = n from by omega]
        have hr : (lappendHOL l1 l3).rep (m + n) = l3.rep n := by
          simp only [lappendRep_rep, lappendRep_of_firstNone_some hf]
          rw [if_neg (by omega)]
          rw [show m + n - m = n from by omega]
        have := congrArg (fun ll => ll.rep (m + n)) h
        rw [hl, hr] at this
        exact this
  · intro h
    rw [h]


end HolLList

end Flapjack
