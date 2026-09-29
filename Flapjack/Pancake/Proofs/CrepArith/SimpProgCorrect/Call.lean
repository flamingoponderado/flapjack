import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# Call case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule contains the exact `Call` case of
`crep_arithProofScript.sml:186-212` (`Case (Call _ _ _)` at 196-206).  The
arguments are simplified with `simp_exp` and still evaluate to the same values
(`opt_mmap_simp_exp_correct`).  The callee is looked up in the `mapcs`-mapped
code and comes back with its body simplified and the same callee locals
(`lookup_code`).  The callee body and the optional exception handler are
related by the `evaluate_ind` Call induction hypotheses.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectCallSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectCallSupport

/-- Flapjack-only abbreviation (no HOL declaration) of the `simp_prog_correct`
    statement at a fixed program and state, over the shared `mapcs` renderer
    `crepSimpMapcsHOL`: the `evaluate_ind` predicate the case proofs receive for
    a sub-program. -/
def simpProgCorrectAt {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) : Prop :=
  ∀ (result : Option (CrepResultHOLExact width)) (finalState : CrepSemHOLState width σ),
    evalCrepSemHOLProgExact state program = (result, finalState) →
    result ≠ some .error →
    evalCrepSemHOLProgExact (crepSimpMapcsHOL state) (crepSimpProgHOL program) =
      (result, crepSimpMapcsHOL finalState)

/-- `lookup_code` at the evaluator's `lookupCodeFiniteHOL` on the mapped code. -/
private theorem lookupCodeFiniteHOL_mapcs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (fname : MlString)
    (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeFiniteHOL (crepSimpMapcsHOL state).code fname args len =
      (lookupCodeFiniteHOL state.code fname args len).map (Prod.map crepSimpProgHOL id) := by
  unfold lookupCodeFiniteHOL crepSimpMapcsHOL
  simp only [HolFiniteMapExact.lookup_map2]
  cases state.code.lookup fname with
  | none => rfl
  | some entry =>
      obtain ⟨parameters, body⟩ := entry
      simp only [Option.map_some]
      split <;> rfl

/-- The `simp_prog` return-information map for a Call
    (`crep_arithScript.sml:93-99`): simplify the handler body, if any. -/
private def simpCallReturnInfo {width : Nat} [NeZero width] :
    Option (List Nat × Option (BitVec width × CrepProgHOL width)) →
      Option (List Nat × Option (BitVec width × CrepProgHOL width))
  | none => none
  | some (returns, none) => some (returns, none)
  | some (returns, some (handler, body)) => some (returns, some (handler, crepSimpProgHOL body))

private theorem crepSimpProgHOL_call {width : Nat} [NeZero width]
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : MlString) (argexps : List (CrepExpHOL width)) :
    crepSimpProgHOL (.call caltyp fname argexps) =
      .call (simpCallReturnInfo caltyp) fname (argexps.map crepSimpExpHOL) := by
  conv => lhs; unfold crepSimpProgHOL
  rcases caltyp with _ | ⟨returns, _ | ⟨handler, body⟩⟩ <;> rfl

/-- The `Call` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:186-212`, Call case 196-206), with the two
    `evaluate_ind` Call induction hypotheses in the one-point-normalized form
    used by the other exact Call pieces (`v6 = (prog, newlocals)`,
    `eval_prog = (v4, st)`, `v4 = SOME v7`, … eliminated).  The first is the
    predicate for the exception handler `p` at `st with locals := s.locals`
    when the callee raises `eid` and the caller installs a handler for `eid`.
    The second is the predicate for the callee body at
    `dec_clock s with locals := newlocals`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectCallCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
      (fname : MlString) (argexps : List (CrepExpHOL width))
      (state : CrepSemHOLState width σ),
      (∀ (args : List (HolWordLab width)) (prog : CrepProgHOL width)
          (newlocals : HolFiniteMapExact Nat (HolWordLab width))
          (st : CrepSemHOLState width σ) (eid : BitVec width) (rts : List Nat)
          (p : CrepProgHOL width),
        argexps.mapM (evalCrepSemHOLExp state) = some args ∧
          lookupCodeFiniteHOL state.code fname args args.length = some (prog, newlocals) ∧
          ¬ (match caltyp with | none => False | some (rts, _) => ¬ rts.Nodup) ∧
          state.clock ≠ 0 ∧
          evalCrepSemHOLProgExact { decClockCrepSemHOL state with locals := newlocals } prog =
            (some (.exception eid), st) ∧
          caltyp = some (rts, some (eid, p)) →
        simpProgCorrectAt p { st with locals := state.locals }) →
      (∀ (args : List (HolWordLab width)) (prog : CrepProgHOL width)
          (newlocals : HolFiniteMapExact Nat (HolWordLab width)),
        argexps.mapM (evalCrepSemHOLExp state) = some args ∧
          lookupCodeFiniteHOL state.code fname args args.length = some (prog, newlocals) ∧
          ¬ (match caltyp with | none => False | some (rts, _) => ¬ rts.Nodup) ∧
          state.clock ≠ 0 →
        simpProgCorrectAt prog { decClockCrepSemHOL state with locals := newlocals }) →
      ∀ (result : Option (CrepResultHOLExact width))
        (finalState : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact state (.call caltyp fname argexps) =
            (result, finalState) →
        result ≠ some .error →
        evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
            (crepSimpProgHOL (.call caltyp fname argexps)) =
          (result, crepSimpMapcsHOL finalState) := by
  intro caltyp fname argexps state ihh ihb result finalState he hne
  rw [crepSimpProgHOL_call]
  rw [evalCrepSemHOLProgExact_call_holShape] at he ⊢
  have herr : ∀ {st : CrepSemHOLState width σ},
      (some CrepResultHOLExact.error, st) = (result, finalState) → False := by
    intro st h
    exact hne (congrArg Prod.fst h).symm
  cases hargs : argexps.mapM (evalCrepSemHOLExp state) with
  | none =>
      rw [hargs] at he
      exact (herr he).elim
  | some args =>
  have hargsT : (argexps.map crepSimpExpHOL).mapM
      (evalCrepSemHOLExp (crepSimpMapcsHOL state)) = some args := by
    rw [crepSimpMapcsHOL_eq_mapc]
    exact crepOptMmapSimpExpCorrectNativeHOL _ state argexps args hargs
  rw [hargs] at he
  rw [hargsT]
  simp only at he ⊢
  cases hlc : lookupCodeFiniteHOL state.code fname args args.length with
  | none =>
      rw [hlc] at he
      exact (herr he).elim
  | some pn =>
  obtain ⟨prog, newlocals⟩ := pn
  have hlcT : lookupCodeFiniteHOL (crepSimpMapcsHOL state).code fname args args.length =
      some (crepSimpProgHOL prog, newlocals) := by
    rw [lookupCodeFiniteHOL_mapcs, hlc]
    rfl
  rw [hlc] at he
  rw [hlcT]
  simp only at he ⊢
  have hnodupIff : crepReturnInfoNodupError (simpCallReturnInfo caltyp) ↔
      crepReturnInfoNodupError caltyp := by
    rcases caltyp with _ | ⟨returns, _ | ⟨handler, body⟩⟩ <;> rfl
  by_cases hnd : crepReturnInfoNodupError caltyp
  · rw [if_pos hnd] at he
    exact (herr he).elim
  rw [if_neg hnd] at he
  rw [if_neg (fun h => hnd (hnodupIff.mp h))]
  by_cases hc : state.clock = 0
  · rw [if_pos hc] at he
    rw [if_pos (show (crepSimpMapcsHOL state).clock = 0 from hc)]
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rfl
  rw [if_neg hc] at he
  rw [if_neg (show ¬ (crepSimpMapcsHOL state).clock = 0 from hc)]
  rcases hcall : evalCrepSemHOLProgExact
      { decClockCrepSemHOL state with locals := newlocals } prog with ⟨r0, st⟩
  rw [hcall] at he
  have hr0 : r0 ≠ some .error := by
    intro h
    subst h
    exact herr he
  have hcallT : evalCrepSemHOLProgExact
      { decClockCrepSemHOL (crepSimpMapcsHOL state) with locals := newlocals }
      (crepSimpProgHOL prog) = (r0, crepSimpMapcsHOL st) :=
    ihb args prog newlocals ⟨hargs, hlc, hnd, hc⟩ r0 st hcall hr0
  rw [hcallT]
  rcases r0 with _ | r0
  · exact (herr he).elim
  cases r0 with
  | error => exact (hr0 rfl).elim
  | timeOut =>
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rfl
  | finalFfi event =>
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rfl
  | «break» label => exact (herr he).elim
  | «continue» label => exact (herr he).elim
  | «return» retvs =>
      rcases caltyp with _ | ⟨rts, handler⟩
      · simp only [simpCallReturnInfo, Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨rfl, rfl⟩
      · have hsr : simpCallReturnInfo (some (rts, handler)) =
            some (rts, match handler with
              | none => none
              | some (h, body) => some (h, crepSimpProgHOL body)) := by
          rcases handler with _ | ⟨h, body⟩ <;> rfl
        rw [hsr]
        simp only at he ⊢
        by_cases hlen : retvs.length ≠ rts.length
        · rw [if_pos hlen] at he
          exact (herr he).elim
        rw [if_neg hlen] at he
        rw [if_neg hlen]
        cases hloc : rts.mapM state.locals.lookup with
        | none =>
            rw [hloc] at he
            exact (herr he).elim
        | some vals =>
            rw [hloc] at he
            rw [show rts.mapM (crepSimpMapcsHOL state).locals.lookup = some vals from hloc]
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            rfl
  | exception eid =>
      rcases caltyp with _ | ⟨rts, _ | ⟨eid', p⟩⟩
      · simp only [simpCallReturnInfo, Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨rfl, rfl⟩
      · simp only [simpCallReturnInfo, Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨rfl, rfl⟩
      · simp only [simpCallReturnInfo] at he ⊢
        by_cases heid : eid = eid'
        · subst heid
          rw [if_pos rfl] at he
          rw [if_pos rfl]
          exact ihh args prog newlocals st eid rts p
            ⟨hargs, hlc, hnd, hc, hcall, rfl⟩ result finalState he hne
        · rw [if_neg heid] at he
          rw [if_neg heid]
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rfl

end Flapjack
