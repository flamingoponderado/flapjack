/-!
# HOL `llist` (possibly infinite lists)

Untagged rendering of HOL4's own lazy-list library
(`HOL/src/coalgebras/llistScript.sml`), which lies outside the CakeML submodule
and so carries no `@[hol]` tags.  HOL defines `'a llist` by
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

end HolLList

end Flapjack
