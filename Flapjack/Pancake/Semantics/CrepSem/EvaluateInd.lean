import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-!
Module for the HOL theorem `crepSem$evaluate_ind`
(`cakeml/pancake/semantics/crepSemScript.sml:440`,
`REWRITE_RULE [fix_clock_evaluate] evaluate_ind`).

The statement is captured in
`scripts/hol-probes/crep_sem_evaluate_ind_probe.out`.  This module
reconstructs the clause-for-clause Lean statement over the exact carriers
`CrepProgHOL`, `CrepSemHOLState`, `CrepResultHOLExact`, and proves it from the
decider-free well-founded induction principle
`evalCrepSemHOLProgExact_inductLex`.  The extra ingredient is the clock
non-increase property (`evaluate_clock` in HOL), which is what justifies
`fix_clock_evaluate`; here it is `evalCrepSemHOLProgExact_clock_le`.

FLAPJACK-SPECIFIC (currently untagged; tag decision with the coordinator,
beads `flapjack-2de.1` / `flapjack-2de.1.1`).  The two previously open
translation deltas are now closed inside this module, with no extra theorem
premise and no qualifier:

* expression guards are written in the classical spelling
  `crepExactEvalExpClassical`, and `crepExactEvalExpClassical_eq` proves this is
  *extensionally equal to the reviewed exact evaluator* `crepExactEvalExp` at any
  decider for the same memory domain: `Decidable` instances of one proposition
  are subsingletons, so the evaluator's `DecidablePred` argument is
  proof-irrelevant.  The classical spelling therefore names the same function as
  the reviewed evaluator, matching HOL `eval`;
* the `Call` clause goes through the reviewed exact `lookupCodeHOL`
  (`CrepSem/LookupCode.lean`).  The reviewed `lookupCodeHOL` returns a raw
  `CrepLocalsExact` (`Nat → Option (HolWordLab width)`) while the state's
  `locals` field is the finite-support `HolFiniteMapExact`; the helper
  `updateList_empty_lookup_eq_FUPDATE_LIST` records that the finite-support
  callee locals' lookup is definitionally that raw map, and
  `lookupCodeHOL_eq_some_of_code_lookup` records that a successful HOL-shaped
  code lookup of duplicate-free formals of the right arity produces exactly the
  raw locals underlying `HolFiniteMapExact.empty.updateList (parameters.zip args)`.

The `fix_clock` wrapper is rewritten away as in the HOL line-440 `rewrite`.

Clause-by-clause comparison with `scripts/hol-probes/crep_sem_evaluate_ind_probe.out`
(19 clauses, checked 2026-09-27 against the probe; order and hypotheses match):

* `Skip` - exact.
* `Dec` - hypothesis `crepExactEvalExpClassical s e = some value`, i.e. the
  reviewed `crepExactEvalExp` at the classical decider by
  `crepExactEvalExpClassical_eq`; HOL `s.locals⟨v ↦ value⟩` is
  `CrepSemHOLState.setVar v value s`.
* `Primitive` (varname list, primop, varname list), `Assign`, `Store`,
  `Store32`, `StoreByte` - exact; `StoreGlob`'s destination is HOL's fixed
  `5 word`, rendered `BitVec 5` (not width-indexed); `ShMem memop varname exp` -
  exact.
* `Seq` - both IHs, `(res, s1) = evalCrepSemHOLProgExact s c1` with `res = none`
  (HOL `evaluate (c1,s)`); exact.
* `If` - `crepExactEvalExpClassical s e = some v1`, `v1 = .word w`, then
  `P (if w ≠ 0 then c1 else c2, s)`.
* `Break n`, `Continue n` (`num` -> `Nat`) - exact.
* `While` - the three HOL IHs (continue with `v8 = 0`; `res = none`; body at
  `decClockCrepSemHOL s`), all guarded by `crepExactEvalExpClassical s e =
  some v2`, `v2 = .word w`, `w ≠ 0`, `s.clock ≠ 0`.
* `Return`, `Raise` (HOL `'a word` -> `BitVec width`), `Tick` - exact.
* `Call` - the two HOL IHs; the caltyp selector
  `¬(match caltyp with | none => False | some (rts, _) => ¬ rts.Nodup)` and the
  argument/clock guards are exact; the `lookup_code` hypothesis is the reviewed
  `lookupCodeHOL s.code.lookup fname args 0 = some (body,
  (HolFiniteMapExact.empty.updateList (parameters.zip args)).lookup)`, whose
  guards are recovered by `lookupCodeHOL_eq_some_of_code_lookup`, and whose raw
  locals are the finite-support callee locals by
  `updateList_empty_lookup_eq_FUPDATE_LIST`.
* `ExtCall` - exact.
* Conclusion `∀ v v1, P (v, v1)` - the probe's uncurried motive, exact.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack-only decider-free wrapper for the exact expression evaluator,
matching HOL `eval`. -/
noncomputable def crepExactEvalExpClassical {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expression : CrepExpHOL width) :
    Option (HolWordLab width) :=
  crepExactEvalExp state (fun a => Classical.propDecidable (state.memaddrs a)) expression

/-- The classical-decider rendering of the exact expression evaluator is
extensionally equal to the reviewed `crepExactEvalExp` at *any* decider for the
same memory-domain predicate.  `Decidable` instances of one proposition are
subsingletons, so the evaluator's `DecidablePred` argument is proof-irrelevant
and the two readings coincide.  This justifies keeping the classical spelling
`crepExactEvalExpClassical` in the clause hypotheses. -/
theorem crepExactEvalExpClassical_eq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (expression : CrepExpHOL width) :
    crepExactEvalExpClassical state expression = crepExactEvalExp state memDec expression := by
  classical
  unfold crepExactEvalExpClassical crepExactEvalExp
  congr 1

/-- The lookup function of the finite-support `HolFiniteMapExact` callee locals
installed by the `Call` clause is definitionally the raw `FiniteMap` computed by
the reviewed exact `lookupCodeHOL`. -/
theorem updateList_empty_lookup_eq_FUPDATE_LIST {width : Nat} [NeZero width]
    (parameters : List Nat) (args : List (HolWordLab width)) :
    (HolFiniteMapExact.empty.updateList (parameters.zip args)).lookup =
      FUPDATE_LIST (FEMPTY : FiniteMap Nat (HolWordLab width)) (parameters.zip args) :=
  rfl

/-- Forward direction of the reviewed exact `lookupCodeHOL`
(`CrepSem/LookupCode.lean:46`) over the exact code map: a successful HOL-shaped
code lookup of duplicate-free formals of the right arity returns exactly the raw
local map underlying the finite-support callee locals
`HolFiniteMapExact.empty.updateList (parameters.zip args)`.  This is the
conversion used to phrase the `Call` clause through `lookupCodeHOL`. -/
theorem lookupCodeHOL_eq_some_of_code_lookup {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width) (fname : MlString)
    (args : List (HolWordLab width)) (parameters : List Nat)
    (body : CrepProgHOL width)
    (hcode : code fname = some (parameters, body))
    (hlen : parameters.length = args.length) (hnodup : parameters.Nodup) :
    lookupCodeHOL code fname args 0 =
      some (body, (HolFiniteMapExact.empty.updateList (parameters.zip args)).lookup) := by
  unfold lookupCodeHOL FLOOKUP
  simp only [hcode]
  rw [if_pos ⟨hlen, hnodup⟩]
  rfl

/-- Exact cache-free `Dec` equation over the no-decider evaluator. -/
theorem evalCrepSemHOLProgExact_dec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : Nat) (value : CrepExpHOL width)
    (body : CrepProgHOL width) :
    evalCrepSemHOLProgExact state (.dec name value body) =
      (match crepExactEvalExpClassical state value with
       | none => (some .error, state)
       | some v =>
           let boundState := CrepSemHOLState.setVar name v state
           let old := state.locals.lookup name
           let step := evalCrepSemHOLProgExact boundState body
           (step.1, { step.2 with locals := step.2.locals.resVarEq (name, old) })) := by
  rw [evalCrepSemHOLProgExact_eq_core state (.dec name value body)
      (fun a => Classical.propDecidable (state.memaddrs a))
      (fun a => Classical.propDecidable (state.shMemaddrs a))]
  rw [evalCrepSemHOLProg_dec]
  rfl

/-- HOL `evaluate_clock` over the exact evaluator. -/
theorem evalCrepSemHOLProgExact_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (program : CrepProgHOL width) :
    (evalCrepSemHOLProgExact state program).2.clock ≤ state.clock := by
  rw [evalCrepSemHOLProgExact_eq_core state program
      (fun a => Classical.propDecidable (state.memaddrs a))
      (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_clock_le state _ _ program

/-- The exact clause-for-clause Lean statement of HOL `crepSem$evaluate_ind`
(`cakeml/pancake/semantics/crepSemScript.sml:440`,
`REWRITE_RULE [fix_clock_evaluate] evaluate_ind`), reconstructed over the exact
carriers `CrepProgHOL`, `CrepSemHOLState`, and `CrepResultHOLExact`.  Expression
guards use the classical spelling `crepExactEvalExpClassical`, proved
extensionally equal to the reviewed `crepExactEvalExp` by
`crepExactEvalExpClassical_eq`.  The `Call` clauses go through the reviewed
exact `lookupCodeHOL`, with the raw `CrepLocalsExact` result converted to the
finite-support `HolFiniteMapExact` carrier by
`updateList_empty_lookup_eq_FUPDATE_LIST` /
`lookupCodeHOL_eq_some_of_code_lookup`.  `fix_clock` has been rewritten away
(`evaluate_clock` is `evalCrepSemHOLProgExact_clock_le`). -/
theorem evalCrepSemHOLProgExact_induct {width : Nat} [NeZero width] {σ : Type}
    (P : CrepProgHOL width × CrepSemHOLState width σ → Prop)
    (hskip : ∀ s, P (.skip, s))
    (hdec : ∀ (v : Nat) (e : CrepExpHOL width) (prog : CrepProgHOL width)
        (s : CrepSemHOLState width σ),
        (∀ value, crepExactEvalExpClassical s e = some value →
          P (prog, CrepSemHOLState.setVar v value s)) →
        P (.dec v e prog, s))
    (hprimitive : ∀ lhss pop rhss s, P (.primitive lhss pop rhss, s))
    (hassign : ∀ v src s, P (.assign v src, s))
    (hstore : ∀ dst src s, P (.store dst src, s))
    (hstore32 : ∀ dst src s, P (.store32 dst src, s))
    (hstoreByte : ∀ dst src s, P (.storeByte dst src, s))
    (hstoreGlob : ∀ (dst : BitVec 5) src s, P (.storeGlob dst src, s))
    (hshMem : ∀ op v ad s, P (.shMem op v ad, s))
    (hseq : ∀ c1 c2 s,
        (∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
          P (c2, s1)) →
        P (c1, s) → P (.seq c1 c2, s))
    (hite : ∀ e c1 c2 s,
        (∀ v1 w, crepExactEvalExpClassical s e = some v1 → v1 = .word w →
          P (if w ≠ 0 then c1 else c2, s)) →
        P (.ite e c1 c2, s))
    (hbreak : ∀ n s, P (.break n, s))
    (hcontinue : ∀ n s, P (.continue n, s))
    (hwhile : ∀ e c s,
        (∀ v2 w res s1 v1 v8,
          crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
          (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
          res = some v1 → v1 = .continue v8 → v8 = 0 →
          P (.while e c, s1)) →
        (∀ v2 w res s1,
          crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
          (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
          res = none →
          P (.while e c, s1)) →
        (∀ v2 w,
          crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
          P (c, decClockCrepSemHOL s)) →
        P (.while e c, s))
    (hreturn : ∀ es s, P (.return es, s))
    (hraise : ∀ eid s, P (.raise eid, s))
    (htick : ∀ s, P (.tick, s))
    (hcall : ∀ caltyp fname argexps s,
        (∀ (args : List (HolWordLab width)) (parameters : List Nat)
            body eval_prog v4 st v7 eid v v1 v2 v3 eid' p,
          argexps.mapM (crepExactEvalExpClassical s) = some args →
          lookupCodeHOL s.code.lookup fname args 0 =
            some (body,
              (HolFiniteMapExact.empty.updateList (parameters.zip args)).lookup) →
          (¬ (match caltyp with
              | none => False
              | some (rts, _) => ¬ rts.Nodup)) →
          s.clock ≠ 0 →
          eval_prog = evalCrepSemHOLProgExact
            { decClockCrepSemHOL s with
              locals := HolFiniteMapExact.empty.updateList (parameters.zip args) } body →
          eval_prog = (v4, st) →
          v4 = some v7 → v7 = .exception eid →
          caltyp = some v → v = (v1, v2) → v2 = some v3 → v3 = (eid', p) →
          eid = eid' →
          P (p, { st with locals := s.locals })) →
        (∀ (args : List (HolWordLab width)) (parameters : List Nat) body,
          argexps.mapM (crepExactEvalExpClassical s) = some args →
          lookupCodeHOL s.code.lookup fname args 0 =
            some (body,
              (HolFiniteMapExact.empty.updateList (parameters.zip args)).lookup) →
          (¬ (match caltyp with
              | none => False
              | some (rts, _) => ¬ rts.Nodup)) →
          s.clock ≠ 0 →
          P (body, { decClockCrepSemHOL s with
              locals := HolFiniteMapExact.empty.updateList (parameters.zip args) })) →
        P (.call caltyp fname argexps, s))
    (hextCall : ∀ ffi_index ptr1 len1 ptr2 len2 s,
        P (.extCall ffi_index ptr1 len1 ptr2 len2, s)) :
    ∀ v v1, P (v, v1) := by
  have hlexSize : ∀ {p q : CrepProgHOL width} {s : CrepSemHOLState width σ},
      sizeOf p < sizeOf q →
      Prod.Lex Nat.lt Nat.lt (s.clock, sizeOf p) (s.clock, sizeOf q) := by
    intro p q s h
    rw [Prod.lex_def]
    exact Or.inr ⟨rfl, h⟩
  have hlexClock : ∀ {p q : CrepProgHOL width} {s t : CrepSemHOLState width σ},
      t.clock < s.clock →
      Prod.Lex Nat.lt Nat.lt (t.clock, sizeOf p) (s.clock, sizeOf q) := by
    intro p q s t h
    rw [Prod.lex_def]
    exact Or.inl h
  have hlexLe : ∀ {p q : CrepProgHOL width} {s t : CrepSemHOLState width σ},
      t.clock ≤ s.clock → sizeOf p < sizeOf q →
      Prod.Lex Nat.lt Nat.lt (t.clock, sizeOf p) (s.clock, sizeOf q) := by
    intro p q s t hle hsz
    rw [Prod.lex_def]
    by_cases hlt : t.clock < s.clock
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, hsz⟩
  refine evalCrepSemHOLProgExact_inductLex
    (motive := fun prog state => P (prog, state)) ?_
  intro program state ih
  cases program with
  | skip => exact hskip state
  | dec name value body =>
      refine hdec name value body state ?_
      intro val _
      exact ih body (CrepSemHOLState.setVar name val state)
        (hlexSize (by decreasing_trivial))
  | assign name src => exact hassign name src state
  | primitive names operator args => exact hprimitive names operator args state
  | store dst src => exact hstore dst src state
  | store32 dst src => exact hstore32 dst src state
  | storeByte dst src => exact hstoreByte dst src state
  | storeGlob dst src => exact hstoreGlob dst src state
  | shMem operator name address => exact hshMem operator name address state
  | seq first second =>
      refine hseq first second state ?_ ?_
      · intro res s1 heq hres
        have hclk : s1.clock ≤ state.clock := by
          have h := evalCrepSemHOLProgExact_clock_le state first
          rw [heq.symm] at h
          simpa using h
        exact ih second s1 (hlexLe hclk (by decreasing_trivial))
      · exact ih first state (hlexSize (by decreasing_trivial))
  | ite condition thenBranch elseBranch =>
      refine hite condition thenBranch elseBranch state ?_
      intro v1 w _ _
      by_cases hw : w ≠ 0
      · rw [if_pos hw]
        exact ih thenBranch state (hlexSize (by decreasing_trivial))
      · rw [if_neg hw]
        exact ih elseBranch state (hlexSize (by decreasing_trivial))
  | «break» label => exact hbreak label state
  | «continue» label => exact hcontinue label state
  | «while» condition body =>
      refine hwhile condition body state ?_ ?_ ?_
      · intro v2 w res s1 v1 v8 _ _ _ hclock heq hres hv1 hv8
        have hclk : s1.clock < state.clock := by
          have h := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL state) body
          rw [heq.symm] at h
          have hd : (decClockCrepSemHOL state).clock < state.clock := by
            simp only [decClockCrepSemHOL]; omega
          have hs1 : s1.clock ≤ (decClockCrepSemHOL state).clock := by simpa using h
          omega
        exact ih (.while condition body) s1 (hlexClock hclk)
      · intro v2 w res s1 _ _ _ hclock heq hres
        have hclk : s1.clock < state.clock := by
          have h := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL state) body
          rw [heq.symm] at h
          have hd : (decClockCrepSemHOL state).clock < state.clock := by
            simp only [decClockCrepSemHOL]; omega
          have hs1 : s1.clock ≤ (decClockCrepSemHOL state).clock := by simpa using h
          omega
        exact ih (.while condition body) s1 (hlexClock hclk)
      · intro v2 w _ _ _ _
        exact ih body (decClockCrepSemHOL state)
          (hlexClock (by simp only [decClockCrepSemHOL]; omega))
  | «return» values => exact hreturn values state
  | «raise» exception => exact hraise exception state
  | tick => exact htick state
  | extCall function configuration configurationLength array arrayLength =>
      exact hextCall function configuration configurationLength array arrayLength state
  | call =>
      rename_i ri fn ar
      refine hcall ri fn ar state ?_ ?_
      · intro args parameters body eval_prog v4 st v7 eid v v1 v2 v3 eid' p
          _ _ _ hclock heval1 heval2 _ _ _ _ _ _ _
        have hclk : st.clock < state.clock := by
          have h := evalCrepSemHOLProgExact_clock_le
            { decClockCrepSemHOL state with
              locals := HolFiniteMapExact.empty.updateList (parameters.zip args) } body
          rw [heval1.symm] at h
          rw [heval2] at h
          have hd : ({ decClockCrepSemHOL state with
                locals := HolFiniteMapExact.empty.updateList (parameters.zip args) }).clock <
              state.clock := by
            simp only [decClockCrepSemHOL]; omega
          have hst : st.clock ≤ ({ decClockCrepSemHOL state with
                locals := HolFiniteMapExact.empty.updateList (parameters.zip args) }).clock := by
            simpa using h
          omega
        exact ih p { st with locals := state.locals } (hlexClock hclk)
      · intro args parameters body _ _ _ hclock
        exact ih body { decClockCrepSemHOL state with
            locals := HolFiniteMapExact.empty.updateList (parameters.zip args) }
          (hlexClock (by simp only [decClockCrepSemHOL]; omega))

end Flapjack
