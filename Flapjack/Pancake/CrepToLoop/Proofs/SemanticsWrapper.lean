import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.FfiHOL
import Flapjack.Misc.LprefixLub
import Flapjack.Pancake.Semantics.LoopSemStateExact.Semantics
import Flapjack.Pancake.Semantics.CrepSem.CrepObservationalSemantics

/-!
# crep_to_loop `semantics_run_res` over the exact carrier

`cakeml/pancake/proofs/crep_to_loopProofScript.sml:4127-4130` declares a fresh,
polymorphic `semantics_run_res` datatype

```
semantics_run_res = RunError | CompleteResult 'a | Incomplete
```

used by the pass-result wrapper `semantics_wrapper_def` (line 4132) and the
`state_rel_imp_semantics` wrapper.  Its text is identical to
`panPropsScript.sml:1818`'s same-named datatype, but every HOL `Datatype`
command introduces its own type constant, so the two are *distinct* types.  The
`panProps` declaration is ported separately as `SemanticsRunResHOL`
(`Flapjack/Pancake/Semantics/PanProps.lean`); this module ports the
`crep_to_loop` one as the distinct carrier `CrepToLoopSemanticsRunRes`.

Constructor order, arity, and the arbitrary result payload type match HOL
exactly, so no carrier qualifier is required.  Direct Lean constructor
observations are included below.
-/

namespace Flapjack

/-- Exact port of the `crep_to_loopProofScript.sml:4127` datatype
    `semantics_run_res = RunError | CompleteResult 'a | Incomplete`.

    This is a *separate* type constant from the structurally identical
    `panPropsScript.sml:1818` `semantics_run_res` (ported as
    `SemanticsRunResHOL`): matching constructor text does not make them the same
    HOL type.  Constructor names are Lean-qualified by this type only; the
    payload arity and order match HOL. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_run_res"]
inductive CrepToLoopSemanticsRunRes (α : Type u) where
  | RunError
  | CompleteResult (result : α)
  | Incomplete
  deriving DecidableEq, Repr

/-! Direct Lean constructor observations: the three constructors have HOL's
    nullary / one-payload / nullary arities, and the payload type is arbitrary. -/
example : CrepToLoopSemanticsRunRes Nat := .RunError
example (result : Nat) : CrepToLoopSemanticsRunRes Nat := .CompleteResult result
example : CrepToLoopSemanticsRunRes Nat := .Incomplete


open Classical in
/-- Exact HOL `semantics_wrapper_def` (`crep_to_loopProofScript.sml:4132-4136`):
    `semantics_wrapper f = (if ?k v. f k = (RunError, v) then Fail
       else case some res. ?k r ev. f k = (CompleteResult r, ev) /\ res = Terminate r ev
         of SOME res => res
          | NONE => Diverge (LUB (IMAGE (fromList o SND o f) (UNIV : num set))))`.
    HOL's arbitrary `f : num -> outcome semantics_run_res # io_event list` is kept with
    no chain premise.  `some` is `holOptionSome` (HOL `some P = if ?x. P x then
    SOME (@x. P x) else NONE`, Hilbert choice rendered by `Classical.choose` on the
    same predicate), `LUB` is HOL's overload for `build_lprefix_lub`, rendered by
    the chain-free `HolLList.buildLprefixLub` over HOL's exact `llist` subtype
    `HolLList` (as in the tagged loopSem/crepSem `semantics_def`), and
    `IMAGE g UNIV` is the predicate `fun l => ∃ k, l = g k`.

    Caveat (choice translation): HOL `@` and Lean `Classical.choose` are the standard
    translation of one another, and this definition states the same choice formula
    as HOL.  The value each selects when the predicate has several witnesses is
    unspecified in both logics, and no cross-language equality of those selections
    is proved.  This matters for non-chain event families, where
    `buildLprefixLub`'s per-index choice and `holOptionSome`'s choice among several
    completed runs may pick different witnesses than HOL.  Such equality is outside
    scope (see `docs/SOUNDNESS.md`, "HOL-to-Lean trust boundary"); the tag records a representation port of the
    same formula over the exact `lrep_ok` lazy-list subtype `HolLList`, not an
    extensional agreement on unspecified choices.  On `lprefixChain` families the LUB
    is characterised uniquely by `buildLprefixLub_thm` in both logics. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_wrapper_def"]
noncomputable def crepToLoopSemanticsWrapper
    (f : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent) : HolBehaviour :=
  if ∃ k v, f k = (.RunError, v) then .fail
  else
    match holOptionSome (fun res => ∃ k r ev,
        f k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k, l = HolLList.fromList (f k).2))

/-- Monotone event traces under an `Incomplete`-only family form an `lprefixChain`
    (the `prefix_chain_lprefix_chain` step of HOL's `semantics_wrapper_eq` proof). -/
private theorem crepToLoopSemanticsWrapper_chain
    (f : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent)
    (hinc : ∀ k, (f k).1 = .Incomplete)
    (hpre : ∀ k k' ev, f (k + k') = (.Incomplete, ev) →
      ∃ r' ev', f k = (r', ev') ∧ ev' <+: ev) :
    HolLList.lprefixChain (fun l => ∃ k, l = HolLList.fromList (f k).2) := by
  intro l1 l2 ⟨k1, e1⟩ ⟨k2, e2⟩
  subst e1; subst e2
  have mono : ∀ a b, a ≤ b → (f a).2 <+: (f b).2 := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨r', ev', he, hp⟩ := hpre a d (f (a + d)).2 (Prod.ext (hinc _) rfl)
    rw [he]; exact hp
  rcases Nat.le_total k1 k2 with h | h
  · exact Or.inl ((HolLList.lprefix_fromList _ _).2 (mono _ _ h))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).2 (mono _ _ h))

open Classical in
/-- Exact HOL `semantics_wrapper_eq` (`crep_to_loopProofScript.sml:4214-4228`):
    all six curried premises and the equality conclusion are kept, over arbitrary
    `absf`/`concf`.  HOL `IS_PREFIX ev ev'` (`ev'` is a prefix of `ev`) is Lean
    `ev' <+: ev`.  No chain premise is added: the proof derives both prefix chains
    from the premises, as HOL does.  Because the equality is between two
    applications of the same `crepToLoopSemanticsWrapper` formula, it does not
    depend on which witnesses HOL `@`/Lean `Classical.choose` select (see the
    caveat on `crepToLoopSemanticsWrapper`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_wrapper_eq"]
theorem crepToLoopSemanticsWrapper_eq
    (absf concf : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent) :
    crepToLoopSemanticsWrapper absf ≠ .fail →
    (∀ k r ev, absf k = (r, ev) → r ≠ .RunError → ∃ k', concf (k + k') = (r, ev)) →
    (∀ k k' r ev, concf k = (r, ev) → r ≠ .Incomplete → concf (k + k') = (r, ev)) →
    (∀ k k' r ev, absf k = (r, ev) → r ≠ .Incomplete → absf (k + k') = (r, ev)) →
    (∀ k k' ev, absf (k + k') = (.Incomplete, ev) →
      ∃ r' ev', absf k = (r', ev') ∧ ev' <+: ev) →
    (∀ k k' ev, concf (k + k') = (.Incomplete, ev) →
      ∃ r' ev', concf k = (r', ev') ∧ ev' <+: ev) →
    crepToLoopSemanticsWrapper concf = crepToLoopSemanticsWrapper absf := by
  intro hfail h1 h2 _h3 h4 h5
  have hnoErrA : ¬ ∃ k v, absf k = (.RunError, v) := by
    intro h; apply hfail; unfold crepToLoopSemanticsWrapper; rw [if_pos h]
  cases hA : holOptionSome (fun res => ∃ k r ev,
      absf k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) with
  | some res =>
    obtain ⟨ka, r, ev, hka, rfl⟩ := holOptionSome_some hA
    obtain ⟨k', hc⟩ := h1 ka _ _ hka (by intro h; cases h)
    have claim : ∀ k2 r2 v2, concf k2 = (r2, v2) →
        (r2, v2) = (.CompleteResult r, ev) ∨ r2 = .Incomplete := by
      intro k2 r2 v2 hk2
      by_cases hr2 : r2 = .Incomplete
      · exact Or.inr hr2
      left
      rcases Nat.le_total k2 (ka + k') with h | h
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
        have := h2 k2 d r2 v2 hk2 hr2
        rw [← hd, hc] at this; exact this.symm
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
        have := h2 (ka + k') d _ _ hc (by intro h; cases h)
        rw [← hd, hk2] at this; exact this
    have hnoErrC : ¬ ∃ k v, concf k = (.RunError, v) := by
      rintro ⟨k, v, hk⟩
      rcases claim k _ _ hk with h | h <;> cases h
    have hC : holOptionSome (fun res => ∃ k r ev,
        concf k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) =
        some (HolBehaviour.terminate r ev) := by
      apply HolLList.holOptionSome_eq_some ⟨ka + k', r, ev, hc, rfl⟩
      rintro y ⟨k2, r2, v2, hk2, rfl⟩
      rcases claim k2 _ _ hk2 with h | h
      · cases h; rfl
      · cases h
    unfold crepToLoopSemanticsWrapper
    rw [if_neg hnoErrC, if_neg hnoErrA, hC, hA]
  | none =>
    have hnoCR : ∀ k r ev, absf k ≠ (.CompleteResult r, ev) := fun k r ev hk =>
      holOptionSome_none hA _ ⟨k, r, ev, hk, rfl⟩
    have hincA : ∀ k, (absf k).1 = .Incomplete := by
      intro k
      match hk : absf k with
      | (.RunError, v) => exact absurd ⟨k, v, hk⟩ hnoErrA
      | (.CompleteResult r, ev) => exact absurd hk (hnoCR k r ev)
      | (.Incomplete, _) => rfl
    have hpfx : ∀ k, ∃ k', concf (k + k') = (.Incomplete, (absf k).2) := fun k =>
      h1 k _ _ (Prod.ext (hincA k) rfl) (by intro h; cases h)
    have hincC : ∀ k, (concf k).1 = .Incomplete := by
      intro k
      by_cases hr : (concf k).1 = .Incomplete
      · exact hr
      obtain ⟨k', hk'⟩ := hpfx k
      have := h2 k k' _ _ (Prod.ext rfl rfl) hr
      rw [hk'] at this
      exact absurd (congrArg Prod.fst this).symm hr
    have hnoErrC : ¬ ∃ k v, concf k = (.RunError, v) := by
      rintro ⟨k, v, hk⟩
      have := hincC k; rw [hk] at this; cases this
    have hC : holOptionSome (fun res => ∃ k r ev,
        concf k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) = none := by
      unfold holOptionSome
      rw [dif_neg]
      rintro ⟨_, k, r, ev, hk, _⟩
      have := hincC k; rw [hk] at this; cases this
    have cA := crepToLoopSemanticsWrapper_chain absf hincA h4
    have cC := crepToLoopSemanticsWrapper_chain concf hincC h5
    have hnth : ∀ n,
        HolLList.lprefixChainNth n (fun l => ∃ k, l = HolLList.fromList (concf k).2) =
        HolLList.lprefixChainNth n (fun l => ∃ k, l = HolLList.fromList (absf k).2) := by
      intro n
      unfold HolLList.lprefixChainNth
      congr 1
      funext x
      apply propext
      constructor
      · rintro ⟨l, ⟨k, rfl⟩, hl⟩
        refine ⟨_, ⟨k, rfl⟩, ?_⟩
        obtain ⟨k', hk'⟩ := hpfx k
        obtain ⟨r', ev', he, hp⟩ := h5 k k' _ hk'
        have hpre : (concf k).2 <+: (absf k).2 := by rw [he]; exact hp
        exact HolLList.lprefix_lnth ((HolLList.lprefix_fromList _ _).2 hpre) hl
      · rintro ⟨l, ⟨k, rfl⟩, hl⟩
        obtain ⟨k', hk'⟩ := hpfx k
        exact ⟨_, ⟨k + k', rfl⟩, by rw [hk']; exact hl⟩
    have hlub :
        HolLList.buildLprefixLub (fun l => ∃ k, l = HolLList.fromList (concf k).2) =
        HolLList.buildLprefixLub (fun l => ∃ k, l = HolLList.fromList (absf k).2) := by
      apply HolLList.ext_of_rep
      intro n
      rw [← HolLList.lnth_eq_rep, ← HolLList.lnth_eq_rep,
        HolLList.lnth_buildLprefixLub cC, HolLList.lnth_buildLprefixLub cA, hnth]
    unfold crepToLoopSemanticsWrapper
    rw [if_neg hnoErrC, if_neg hnoErrA, hC, hA, hlub]


/-- HOL's result classification in `loop_sem_is_wrapper`, named for the proof only. -/
private def loopSemWrapperClass {width : Nat} [NeZero width] :
    Option (LoopSemStateFiniteExact.LoopResultExact width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.result _) => .CompleteResult HolOutcome.success
  | _ => .RunError

open Classical in
/-- `loop_sem_is_wrapper` over an abstract clock-indexed evaluation `E`. -/
private theorem loopSemIsWrapper_aux {width : Nat} [NeZero width] {F : Type}
    (E : Nat → Option (LoopSemStateFiniteExact.LoopResultExact width) ×
      LoopSemStateFiniteExact width F) :
    (if ∃ k, (match (E k).1 with
        | some .timeOut => False
        | some (.finalFfi _) => False
        | some (.result _) => False
        | _ => True)
      then HolBehaviour.fail
      else
        match holOptionSome (fun res => ∃ k t r outcome,
            E k = (r, t) ∧
            (match r with
             | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
             | some (.result _) => outcome = HolOutcome.success
             | _ => False) ∧
            res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
        | some res => res
        | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
            l = HolLList.fromList (E k).2.ffi.ioEvents))) =
      crepToLoopSemanticsWrapper
        (Prod.map loopSemWrapperClass
          (fun t : LoopSemStateFiniteExact width F => t.ffi.ioEvents) ∘ E) := by
  have hk : ∀ k, (match (E k).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.result _) => False
      | _ => True) ↔
      ∃ v, (Prod.map loopSemWrapperClass
        (fun t : LoopSemStateFiniteExact width F => t.ffi.ioEvents) ∘ E) k = (.RunError, v) := by
    intro k
    simp only [Function.comp_apply]
    generalize E k = e
    rcases e with ⟨r, t⟩
    rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [loopSemWrapperClass]
  have hP : (fun res => ∃ k t r outcome,
      E k = (r, t) ∧
      (match r with
       | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
       | some (.result _) => outcome = HolOutcome.success
       | _ => False) ∧
      res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
      (fun res => ∃ k r ev,
        (Prod.map loopSemWrapperClass
          (fun t : LoopSemStateFiniteExact width F => t.ffi.ioEvents) ∘ E) k =
          (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, outcome, he, hm, rfl⟩
      refine ⟨k, outcome, t.ffi.ioEvents, ?_, rfl⟩
      simp only [Function.comp_apply, he, Prod.map]
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp at hm <;>
        simp [loopSemWrapperClass, hm]
    · rintro ⟨k, r', ev, hf, rfl⟩
      simp only [Function.comp_apply] at hf
      rcases he : E k with ⟨r, t⟩
      rw [he] at hf
      simp only [Prod.map, Prod.mk.injEq] at hf
      obtain ⟨hg, rfl⟩ := hf
      refine ⟨k, t, r, r', he, ?_, rfl⟩
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [loopSemWrapperClass] at hg ⊢ <;>
        exact hg.symm
  unfold crepToLoopSemanticsWrapper
  rw [exists_congr hk, hP]
  rfl

namespace LoopSemIsWrapperFiniteSupport

/-- Same-module re-export of the checked canonical finite-support witness for
`LoopSemStateFiniteExact`, used by the `fmap_as_finite_support := [globals]`
qualified `loop_sem_is_wrapper` port below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopSemIsWrapperFiniteSupport

/-- Exact HOL `loop_sem_is_wrapper` (`crep_to_loopProofScript.sml:4178-4185`):
    ```
    loopSem$semantics s start =
      let prog = loopLang$Call NONE (SOME start) [] NONE in
      semantics_wrapper (((\res. case res of
        | SOME TimeOut => Incomplete
        | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
        | SOME (Result _) => CompleteResult Success
        | _ => RunError) ## (\s. s.ffi.io_events)) o
        (\k. loopSem$evaluate (prog, s with clock := k)))
    ```
    over the tagged exact `LoopSemStateFiniteExact.semantics` and `evaluate`.  HOL
    `f ## g` is `Prod.map f g` and `o` is `∘`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "loop_sem_is_wrapper"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopSemIsWrapper {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) :
    LoopSemStateFiniteExact.semantics s start =
      let prog : HolLoopProg width := .call none (some start) [] none
      crepToLoopSemanticsWrapper
        ((Prod.map (fun res : Option (LoopSemStateFiniteExact.LoopResultExact width) => match res with
            | some .timeOut => CrepToLoopSemanticsRunRes.Incomplete
            | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
            | some (.result _) => .CompleteResult HolOutcome.success
            | _ => .RunError)
          (fun t : LoopSemStateFiniteExact width F => t.ffi.ioEvents)) ∘
          (fun k => LoopSemStateFiniteExact.evaluate prog { s with clock := k })) := by
  unfold LoopSemStateFiniteExact.semantics
  exact loopSemIsWrapper_aux _

/-- HOL's result classification in `crep_sem_is_wrapper`, named for the proof only. -/
private def crepSemWrapperClass {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.return _) => .CompleteResult HolOutcome.success
  | _ => .RunError

open Classical in
/-- `crep_sem_is_wrapper` over an abstract clock-indexed evaluation `E`. -/
private theorem crepSemIsWrapper_aux {width : Nat} [NeZero width] {σ : Type}
    (E : Nat → Option (CrepResultHOLExact width) ×
      CrepSemHOLState width σ) :
    (if ∃ k, (match (E k).1 with
        | some .timeOut => False
        | some (.finalFfi _) => False
        | some (.return _) => False
        | _ => True)
      then HolBehaviour.fail
      else
        match holOptionSome (fun res => ∃ k t r outcome,
            E k = (r, t) ∧
            (match r with
             | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
             | some (.return _) => outcome = HolOutcome.success
             | _ => False) ∧
            res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
        | some res => res
        | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
            l = HolLList.fromList (E k).2.ffi.ioEvents))) =
      crepToLoopSemanticsWrapper
        (Prod.map crepSemWrapperClass
          (fun t : CrepSemHOLState width σ => t.ffi.ioEvents) ∘ E) := by
  have hk : ∀ k, (match (E k).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.return _) => False
      | _ => True) ↔
      ∃ v, (Prod.map crepSemWrapperClass
        (fun t : CrepSemHOLState width σ => t.ffi.ioEvents) ∘ E) k = (.RunError, v) := by
    intro k
    simp only [Function.comp_apply]
    generalize E k = e
    rcases e with ⟨r, t⟩
    rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [crepSemWrapperClass]
  have hP : (fun res => ∃ k t r outcome,
      E k = (r, t) ∧
      (match r with
       | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
       | some (.return _) => outcome = HolOutcome.success
       | _ => False) ∧
      res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
      (fun res => ∃ k r ev,
        (Prod.map crepSemWrapperClass
          (fun t : CrepSemHOLState width σ => t.ffi.ioEvents) ∘ E) k =
          (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, outcome, he, hm, rfl⟩
      refine ⟨k, outcome, t.ffi.ioEvents, ?_, rfl⟩
      simp only [Function.comp_apply, he, Prod.map]
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp at hm <;>
        simp [crepSemWrapperClass, hm]
    · rintro ⟨k, r', ev, hf, rfl⟩
      simp only [Function.comp_apply] at hf
      rcases he : E k with ⟨r, t⟩
      rw [he] at hf
      simp only [Prod.map, Prod.mk.injEq] at hf
      obtain ⟨hg, rfl⟩ := hf
      refine ⟨k, t, r, r', he, ?_, rfl⟩
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [crepSemWrapperClass] at hg ⊢ <;>
        exact hg.symm
  unfold crepToLoopSemanticsWrapper
  rw [exists_congr hk, hP]
  rfl

namespace CrepSemIsWrapperFiniteSupport

/-- Same-module re-export of the checked canonical finite-support witness for
`CrepSemHOLState`, used by the `fmap_as_finite_support := [locals, globals, code]`
qualified `crep_sem_is_wrapper` port below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemShMemExact.holFmapAsFiniteSupportWitness

end CrepSemIsWrapperFiniteSupport

/-- Exact HOL `crep_sem_is_wrapper` (`crep_to_loopProofScript.sml:4138-4147`):
    ```
    crepSem$semantics s start =
      let prog = crepLang$Call NONE start [] in
      semantics_wrapper (((\res. case res of
        | SOME TimeOut => Incomplete
        | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
        | SOME (Return _) => CompleteResult Success
        | _ => RunError) ## (\s. s.ffi.io_events)) o
        (\k. crepSem$evaluate (prog, s with clock := k)))
    ```
    over the tagged exact `crepSemantics` and `evalCrepSemHOLProgExact` (HOL
    `evaluate (prog, s)` is `evalCrepSemHOLProgExact s prog`).  HOL `f ## g` is
    `Prod.map f g` and `o` is `∘`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_sem_is_wrapper"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem crepSemIsWrapper {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (start : Flapjack.Basis.Pure.MlString.MlString) :
    crepSemantics s start =
      let prog : CrepProgHOL width := .call none start []
      crepToLoopSemanticsWrapper
        ((Prod.map (fun res : Option (CrepResultHOLExact width) => match res with
            | some .timeOut => CrepToLoopSemanticsRunRes.Incomplete
            | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
            | some (.return _) => .CompleteResult HolOutcome.success
            | _ => .RunError)
          (fun t : CrepSemHOLState width σ => t.ffi.ioEvents)) ∘
          (fun k => evalCrepSemHOLProgExact { s with clock := k } prog)) := by
  unfold crepSemantics
  exact crepSemIsWrapper_aux _

end Flapjack
