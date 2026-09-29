import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper

/-!
# Crep start-code lookup from non-`Fail` semantics

`cakeml/pancake/proofs/crep_to_loopProofScript.sml:4334-4346`, inside
`state_rel_imp_semantics`, derives

```
∃prog. ALOOKUP crep_code start = SOME ([],prog)
```

from `semantics s start <> Fail`, `s.code = alist_to_fmap crep_code`, and
`s.locals = FEMPTY` by unfolding `semantics_wrapper_def` (`4132`) after
`crep_sem_is_wrapper` (`4139`) and reading the one clock-`1` `Call` evaluation.
The fact is derived inline; HOL has no named declaration for it, so the Lean
lemma below is Flapjack-specific infrastructure and carries **no** `@[hol]`
tag.  Its docstring records the HOL proof step it ports.

The HOL script's inner tactic block

```
pop_assum mp_tac
\\ qpat_x_assum ‘s.code = _’ mp_tac
\\ rpt $ pop_assum kall_tac
\\ simp[semantics_wrapper_def,AllCaseEqs()]
\\ rpt strip_tac
\\ pop_assum kall_tac
\\ pop_assum $ qspec_then ‘1’ mp_tac
\\ rw[crepSemTheory.evaluate_def,AllCaseEqs(),lookup_code_def]
\\ Cases_on ‘ALOOKUP crep_code start’
\\ gvs[]
\\ metis_tac[FST,SND,PAIR]
```

discards every premise except the code-map equality and the non-`Fail`
assumption; in particular the empty-locals premise is not consulted by this
subderivation, which is why it is kept only for statement fidelity here.  The
clock-`1` `Call` evaluation with an empty argument list makes `lookup_code`
succeed only for an entry with an empty parameter list; a missing entry or a
nonempty parameter list yields `SOME Error`, hence `RunError`, contradicting
non-`Fail`.  The `RunError` classification is the `crep_sem_is_wrapper`
result map at `:4139-4147`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- The result classification of `crep_sem_is_wrapper`
(`crep_to_loopProofScript.sml:4139-4147`), named locally for the proof of
`crepSemantics_ne_fail_imp_holAlookup`.  Flapjack-specific infrastructure; it
has no separate HOL declaration (the wrapper inlines this map). -/
private def crepSemRunResClass {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.return _) => .CompleteResult HolOutcome.success
  | _ => .RunError

/-- Flapjack infrastructure: a wrapper whose clock-indexed family never reaches
`RunError` is not `Fail`.  HOL derives this while unfolding
`semantics_wrapper_def` (`crep_to_loopProofScript.sml:4132-4136`); it has no
named HOL declaration. -/
theorem crepToLoopSemanticsWrapper_ne_fail_of_no_error
    {f : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent}
    (hnoErr : ¬ ∃ k v, f k = (.RunError, v)) :
    crepToLoopSemanticsWrapper f ≠ .fail := by
  classical
  unfold crepToLoopSemanticsWrapper
  rw [if_neg hnoErr]
  intro h
  cases hsome : holOptionSome (fun res => ∃ k r ev,
      f k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) with
  | some res =>
      have hres_ne : res ≠ .fail := by
        obtain ⟨k, r, ev, _, hres⟩ := holOptionSome_some hsome
        rw [hres]
        intro hc
        cases hc
      rw [hsome] at h
      exact hres_ne h
  | none =>
      rw [hsome] at h
      cases h

/-- Flapjack list infrastructure (HOL library `ALOOKUP`, no theorem of its
own): a duplicate-free association list returns the value paired with `key`.
This is the membership direction of HOL `ALOOKUP` used by the inline
`ALOOKUP` reasoning at `crep_to_loopProofScript.sml:4346`. -/
private theorem holAlookup_of_mem_of_nodup {α β : Type} [DecidableEq α]
    (entries : List (α × β)) (hdistinct : (entries.map Prod.fst).Nodup)
    {key : α} {value : β} (hmem : (key, value) ∈ entries) :
    holAlookup entries key = some value := by
  induction entries with
  | nil => simp at hmem
  | cons entry entries ih =>
      obtain ⟨x, y⟩ := entry
      rw [List.map_cons, List.nodup_cons] at hdistinct
      obtain ⟨hnotin, htail⟩ := hdistinct
      rcases List.mem_cons.mp hmem with hhead | htailmem
      · obtain ⟨rfl, rfl⟩ := hhead
        simp [holAlookup]
      · have hne : x ≠ key := by
          intro he
          apply hnotin
          rw [he]
          exact List.mem_map.mpr ⟨(key, value), htailmem, rfl⟩
        simp only [holAlookup, if_neg hne]
        exact ih htail htailmem

/-- Flapjack bridge for the code-map representation: on a duplicate-free
association list, the exact `alist_to_fmap` rendering `alistToFmapCodeExact`
(`CodeRel2.lean`) and HOL `ALOOKUP` (`holAlookup`) return the same value.  This
is the membership direction only, matching the `Cases_on ‘ALOOKUP crep_code
start’` / `gvs[]` step of `crep_to_loopProofScript.sml:4344-4346`. -/
theorem holAlookup_eq_of_alistToFmapCodeExact_lookup {width : Nat} [NeZero width]
    (entries : List (MlString × List Nat × CrepProgHOL width))
    (key : MlString) (value : List Nat × CrepProgHOL width)
    (hdistinct : (entries.map Prod.fst).Nodup)
    (hlookup : (alistToFmapCodeExact entries).lookup key = some value) :
    holAlookup entries key = some value := by
  have hraw : FLOOKUP
      (FUPDATE_LIST (FEMPTY : FiniteMap MlString (List Nat × CrepProgHOL width))
        entries.reverse) key = some value := by
    simp only [alistToFmapCodeExact, HolFiniteMapExact.lookup_updateList] at hlookup
    exact hlookup
  rcases flookupFupdateList_mem_or_base
      (FEMPTY : FiniteMap MlString (List Nat × CrepProgHOL width))
      entries.reverse key value hraw with ⟨entry, hentry, hkey, hvalue⟩ | hbase
  · have hmem : (key, value) ∈ entries := by
      have hpair : (key, value) = entry := by
        rcases entry with ⟨entryKey, entryValue⟩
        simp only [Prod.mk.injEq] at hkey hvalue ⊢
        exact ⟨hkey.symm, hvalue.symm⟩
      rw [hpair]
      exact List.mem_reverse.mp hentry
    exact holAlookup_of_mem_of_nodup entries hdistinct hmem
  · exact absurd hbase (by simp [FLOOKUP_empty])

/-- Inline HOL step `crep_to_loopProofScript.sml:4334-4346`: from a non-`Fail`
Crep entry semantics, the start entry of the source association list exists
with an empty parameter list.

Flapjack-specific port of the inline derivation (no named HOL declaration, so
no `@[hol]` tag).  `crepSemantics` is the tagged exact port of
`crepSem$semantics_def`, `crepSemIsWrapper` the tagged exact
`crep_sem_is_wrapper`, `s.code = alistToFmapCodeExact crep_code` the exact
`alist_to_fmap` rendering, `s.locals = HolFiniteMapExact.empty` the exact
`FEMPTY` rendering, `(crep_code.map Prod.fst).Nodup` the exact
`ALL_DISTINCT (MAP FST crep_code)`, and `holAlookup` the exact
`alist$ALOOKUP`.  As in the HOL subderivation, the empty-locals premise is
retained for statement fidelity but is not consulted. -/
theorem crepSemantics_ne_fail_imp_holAlookup {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString)
    (hcode : s.code = alistToFmapCodeExact crep_code)
    (_hlocals : s.locals = HolFiniteMapExact.empty)
    (hdistinct : (crep_code.map Prod.fst).Nodup)
    (hfail : crepSemantics s start ≠ .fail) :
    ∃ prog, holAlookup crep_code start = some ([], prog) := by
  classical
  have hfail' := hfail
  rw [crepSemIsWrapper] at hfail'
  change crepToLoopSemanticsWrapper
      ((Prod.map crepSemRunResClass (fun t : CrepSemHOLState width σ => t.ffi.ioEvents)) ∘
        (fun k => evalCrepSemHOLProgExact { s with clock := k } (.call none start []))) ≠
      .fail at hfail'
  have hnoErr : ¬ ∃ k v,
      ((Prod.map crepSemRunResClass (fun t : CrepSemHOLState width σ => t.ffi.ioEvents)) ∘
        (fun k => evalCrepSemHOLProgExact { s with clock := k } (.call none start []))) k =
      (.RunError, v) := by
    intro h
    unfold crepToLoopSemanticsWrapper at hfail'
    rw [if_pos h] at hfail'
    exact hfail' rfl
  have h1 : crepSemRunResClass
        (evalCrepSemHOLProgExact { s with clock := 1 } (.call none start [])).1 ≠
      CrepToLoopSemanticsRunRes.RunError := by
    intro hc
    refine hnoErr ⟨1, (evalCrepSemHOLProgExact { s with clock := 1 }
      (.call none start [])).2.ffi.ioEvents, ?_⟩
    simp only [Function.comp_apply, Prod.map, hc]
  cases hlookup : s.code.lookup start with
  | none =>
      exfalso
      apply h1
      rw [evalCrepSemHOLProgExact_call]
      simp only [List.mapM_nil, hlookup]
      split <;> simp [crepSemRunResClass]
  | some entry =>
      obtain ⟨parameters, body⟩ := entry
      cases hguard :
          (decide (parameters.length = ([] : List (CrepExpHOL width)).length) &&
            decide parameters.Nodup) with
      | false =>
          exfalso
          apply h1
          rw [evalCrepSemHOLProgExact_call]
          simp only [List.mapM_nil, Option.pure_def, hlookup]
          have hgt : ¬ ((decide (parameters.length = ([] : List (CrepExpHOL width)).length) &&
              decide parameters.Nodup) = true) := by
            rw [hguard]
            simp
          split
          · exact absurd (by assumption) hgt
          · simp [crepSemRunResClass]
      | true =>
          have hparams : parameters = [] := by
            have hlen : parameters.length = 0 := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
              simpa using hguard.1
            exact List.eq_nil_of_length_eq_zero hlen
          refine ⟨body, ?_⟩
          have hval : (alistToFmapCodeExact crep_code).lookup start = some ([], body) := by
            have hthis := hlookup
            rw [hcode, hparams] at hthis
            exact hthis
          exact holAlookup_eq_of_alistToFmapCodeExact_lookup crep_code start ([], body)
            hdistinct hval

end Flapjack
