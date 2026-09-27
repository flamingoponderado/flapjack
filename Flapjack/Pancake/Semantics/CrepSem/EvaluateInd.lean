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
  `locals` field is the finite-support `HolFiniteMapExact`; the internal wrapper
  `lookupCodeHOLFinite` repackages a successful lookup into the finite-support
  carrier, and `lookupCodeHOLFinite_eq_some` / `lookupCodeHOLFinite_eq_some_iff`
  record that its `.lookup` projection is exactly the reviewed `lookupCodeHOL`.
  The helper `fupdateList_fempty_finiteSupport` and
  `lookupCodeHOL_calleeLocals_finiteSupport` supply the finite-support witness
  for the zipped callee locals.  These declarations are Flapjack-internal
  infrastructure: no `@[hol]` tag and no qualifier.

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
  argument/clock guards are exact.  The `lookup_code` hypothesis quantifies HOL's
  own binders `args v6 prog newlocals` and reads
  `lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6`
  together with `v6 = (prog, newlocals)`, matching HOL
  `lookup_code s.code fname args (LENGTH args) = SOME v6 ∧ v6 = (prog,newlocals)`.
  The internal wrapper `lookupCodeHOLFinite` converts the reviewed
  `lookupCodeHOL`'s raw `CrepLocalsExact` result to the finite-support
  `HolFiniteMapExact` carrier; its `.lookup` projection recovers
  `lookupCodeHOL` by `lookupCodeHOLFinite_eq_some` /
  `lookupCodeHOLFinite_eq_some_iff`.
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
    (args : List (HolWordLab width)) (len : Nat) (parameters : List Nat)
    (body : CrepProgHOL width)
    (hcode : code fname = some (parameters, body))
    (hlen : parameters.length = args.length) (hnodup : parameters.Nodup) :
    lookupCodeHOL code fname args len =
      some (body, (HolFiniteMapExact.empty.updateList (parameters.zip args)).lookup) := by
  unfold lookupCodeHOL FLOOKUP
  simp only [hcode]
  rw [if_pos ⟨hlen, hnodup⟩]
  rfl

/-- The zipped callee-local map built by the reviewed exact code lookup has
finite support.  This is the support obligation needed to repackage the raw
`CrepLocalsExact` result of `lookupCodeHOL` as a `HolFiniteMapExact`. -/
theorem fupdateList_fempty_finiteSupport {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) :
    ∃ keys : List α, ∀ key, FUPDATE_LIST (FEMPTY : FiniteMap α β) entries key ≠ none →
      key ∈ keys := by
  refine ⟨entries.map Prod.fst, ?_⟩
  intro key hkey
  cases hlookup : FUPDATE_LIST (FEMPTY : FiniteMap α β) entries key with
  | none => exact absurd hlookup hkey
  | some value =>
      rcases flookupFupdateList_mem_or_base (FEMPTY : FiniteMap α β) entries key value
        hlookup with hmem | hbase
      · obtain ⟨entry, hentry, hkeyeq, _⟩ := hmem
        exact List.mem_map.mpr ⟨entry, hentry, hkeyeq⟩
      · exact absurd hbase (by simp)

/-- The second component of a successful reviewed exact `lookupCodeHOL` has
finite support, so it can be represented as the `.lookup` of a
`HolFiniteMapExact`.  Derived from the reviewed lookup's own definition (the
successful branch is `FUPDATE_LIST FEMPTY (parameters.zip args)`) via
`fupdateList_fempty_finiteSupport`. -/
theorem lookupCodeHOL_calleeLocals_finiteSupport {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width) (fname : MlString)
    (args : List (HolWordLab width)) (len : Nat) (body : CrepProgHOL width)
    (calleeLocals : CrepLocalsExact width)
    (h : lookupCodeHOL code fname args len = some (body, calleeLocals)) :
    ∃ keys : List Nat, ∀ key, calleeLocals key ≠ none → key ∈ keys := by
  unfold lookupCodeHOL at h
  split at h
  · exact absurd h (by simp)
  · rename_i parameters body' hcode
    by_cases hcond : parameters.length = args.length ∧ parameters.Nodup
    · rw [if_pos hcond] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hlocals⟩ := h
      subst hlocals
      exact fupdateList_fempty_finiteSupport (parameters.zip args)
    · rw [if_neg hcond] at h
      exact absurd h (by simp)

/-- Internal canonical finite-support wrapper around the reviewed exact
`lookupCodeHOL` (`CrepSem/LookupCode.lean:46`).  The reviewed lookup returns a
raw `CrepLocalsExact` (`Nat → Option (HolWordLab width)`), whereas the state's
`locals` field is the finite-support `HolFiniteMapExact`; this wrapper
repackages a successful result into that carrier, with support witness supplied
by `lookupCodeHOL_calleeLocals_finiteSupport`.  Its `.lookup` projection is
exactly the reviewed lookup's second component on success, recorded by
`lookupCodeHOLFinite_eq_some` / `lookupCodeHOLFinite_eq_some_iff`.  Flapjack
internal infrastructure: no `@[hol]` tag and no qualifier. -/
noncomputable def lookupCodeHOLFinite {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width) (fname : MlString)
    (args : List (HolWordLab width)) (len : Nat) :
    Option (CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width)) :=
  match h : lookupCodeHOL code fname args len with
  | none => none
  | some (body, calleeLocals) =>
      some (body,
        { lookup := calleeLocals,
          finiteSupport := lookupCodeHOL_calleeLocals_finiteSupport
            code fname args len body calleeLocals h })

/-- Two finite-support maps with the same `.lookup` are equal, because the
`finiteSupport` field is a proof of a proposition. -/
theorem holFiniteMapExact_eq_of_lookup_eq {α β : Type}
    {m n : HolFiniteMapExact α β} (h : m.lookup = n.lookup) : m = n := by
  obtain ⟨lm, pm⟩ := m
  obtain ⟨ln, pn⟩ := n
  simp only at h
  subst h
  rfl

/-- Forward bridge for `lookupCodeHOLFinite`: a successful wrapper result
forgets to the reviewed exact `lookupCodeHOL`, with the finite-support locals
projected through `.lookup`.  This is the exact HOL `lookup_code ... = SOME v6`
fact underlying the `Call` clause guard. -/
theorem lookupCodeHOLFinite_eq_some {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width) (fname : MlString)
    (args : List (HolWordLab width)) (len : Nat)
    (prog : CrepProgHOL width) (callee : HolFiniteMapExact Nat (HolWordLab width))
    (h : lookupCodeHOLFinite code fname args len = some (prog, callee)) :
    lookupCodeHOL code fname args len = some (prog, callee.lookup) := by
  unfold lookupCodeHOLFinite at h
  split at h
  · simp at h
  · rename_i body' calleeLocals' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hcallee⟩ := h
    have hlookup : calleeLocals' = callee.lookup := by
      rw [← hcallee]
    rw [hb, hlookup] at heq
    exact heq

/-- Bridge for `lookupCodeHOLFinite` in both directions: the wrapper succeeds
with `(prog, newlocals)` exactly when the reviewed exact `lookupCodeHOL`
succeeds with `(prog, newlocals.lookup)`. -/
theorem lookupCodeHOLFinite_eq_some_iff {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width) (fname : MlString)
    (args : List (HolWordLab width)) (len : Nat)
    (prog : CrepProgHOL width) (newlocals : HolFiniteMapExact Nat (HolWordLab width)) :
    lookupCodeHOLFinite code fname args len = some (prog, newlocals) ↔
      lookupCodeHOL code fname args len = some (prog, newlocals.lookup) := by
  constructor
  · intro h
    exact lookupCodeHOLFinite_eq_some code fname args len prog newlocals h
  · intro h
    unfold lookupCodeHOLFinite
    split
    · rename_i heq
      have hsome : some (prog, newlocals.lookup) = none := h.symm.trans heq
      simp at hsome
    · rename_i body' calleeLocals' heq
      have hsome : some (body', calleeLocals') = some (prog, newlocals.lookup) :=
        heq.symm.trans h
      injection hsome with hpair
      injection hpair with hbody hlookup
      subst hbody
      apply congrArg (fun m => some (body', m))
      exact holFiniteMapExact_eq_of_lookup_eq hlookup

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

namespace CrepEvaluateIndFiniteSupport

/-- Local same-module witness for the canonical finite-support `CrepSemHOLState`
carrier used by the qualified `evaluate_ind` port below (an imported witness may
be re-exported as a local one). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepEvaluateIndFiniteSupport

/-- FLAPJACK-SPECIFIC (not a tagged HOL port, so no `@[hol]` tag): clause-for-clause
reconstruction of HOL `crepSem$evaluate_ind` (`cakeml/pancake/semantics/crepSemScript.sml:440`,
`REWRITE_RULE [fix_clock_evaluate] evaluate_ind`) over the exact carriers `CrepProgHOL`,
`CrepSemHOLState`, and `CrepResultHOLExact`.  An earlier exact tag here was WITHDRAWN
2026-09-27 on coordinator review: the Seq/While clause-equation tags over this same
evaluator were already withdrawn pending whole-evaluator source review (Call
domain-stamping and FFI effect agreement), so this induction principle inherits the same
pending dependency and cannot be tagged until that review is complete.  Expression guards
use the classical spelling `crepExactEvalExpClassical`, proved extensionally equal to the
reviewed `crepExactEvalExp` by `crepExactEvalExpClassical_eq`.  The `Call` clause
quantifies HOL's own binders `args v6 prog newlocals` and goes through the internal
finite-support wrapper `lookupCodeHOLFinite`, whose `.lookup` projection is the reviewed
exact `lookupCodeHOL`; the raw `CrepLocalsExact` result is repackaged as the
finite-support `HolFiniteMapExact` carrier (support witness from
`lookupCodeHOL_calleeLocals_finiteSupport`).  `fix_clock` has been rewritten away
(`evaluate_clock` is `evalCrepSemHOLProgExact_clock_le`).  The faithful tagged port is
tracked by `flapjack-2de.1.1`, blocked by `flapjack-4ac.5.16.5`. -/
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
        (∀ (args : List (HolWordLab width))
            (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
            (prog : CrepProgHOL width)
            (newlocals : HolFiniteMapExact Nat (HolWordLab width))
            eval_prog v4 st v7 eid v v1 v2 v3 eid' p,
          argexps.mapM (crepExactEvalExpClassical s) = some args →
          lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
          v6 = (prog, newlocals) →
          (¬ (match caltyp with
              | none => False
              | some (rts, _) => ¬ rts.Nodup)) →
          s.clock ≠ 0 →
          eval_prog = evalCrepSemHOLProgExact
            { decClockCrepSemHOL s with locals := newlocals } prog →
          eval_prog = (v4, st) →
          v4 = some v7 → v7 = .exception eid →
          caltyp = some v → v = (v1, v2) → v2 = some v3 → v3 = (eid', p) →
          eid = eid' →
          P (p, { st with locals := s.locals })) →
        (∀ (args : List (HolWordLab width))
            (v6 : CrepProgHOL width × HolFiniteMapExact Nat (HolWordLab width))
            (prog : CrepProgHOL width)
            (newlocals : HolFiniteMapExact Nat (HolWordLab width)),
          argexps.mapM (crepExactEvalExpClassical s) = some args →
          lookupCodeHOLFinite s.code.lookup fname args (List.length args) = some v6 →
          v6 = (prog, newlocals) →
          (¬ (match caltyp with
              | none => False
              | some (rts, _) => ¬ rts.Nodup)) →
          s.clock ≠ 0 →
          P (prog, { decClockCrepSemHOL s with locals := newlocals })) →
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
      · intro args v6 prog newlocals eval_prog v4 st v7 eid v v1 v2 v3 eid' p
          _ _ _ _ hclock heval1 heval2 _ _ _ _ _ _ _
        have hclk : st.clock < state.clock := by
          have h := evalCrepSemHOLProgExact_clock_le
            { decClockCrepSemHOL state with locals := newlocals } prog
          rw [heval1.symm] at h
          rw [heval2] at h
          have hd : ({ decClockCrepSemHOL state with
                locals := newlocals }).clock <
              state.clock := by
            simp only [decClockCrepSemHOL]; omega
          have hst : st.clock ≤ ({ decClockCrepSemHOL state with
                locals := newlocals }).clock := by
            simpa using h
          omega
        exact ih p { st with locals := state.locals } (hlexClock hclk)
      · intro args v6 prog newlocals _ _ _ _ hclock
        exact ih prog { decClockCrepSemHOL state with locals := newlocals }
          (hlexClock (by simp only [decClockCrepSemHOL]; omega))

end Flapjack
