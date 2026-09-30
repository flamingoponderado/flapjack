import Flapjack.HolRef

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

/-- HOL `LNTH (fromList l) n = if n < LENGTH l then SOME (EL n l) else NONE`
    (`llistScript.sml:1154-1156` `fromList_LNTH`), i.e. the representation of
    `fromList` reads the list and is absent beyond its end. -/
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

end HolLList

end Flapjack
