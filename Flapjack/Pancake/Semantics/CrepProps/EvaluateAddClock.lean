import Flapjack.HolRef
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd
import Flapjack.Pancake.Semantics.CrepProps

/-!
Exact port of HOL `crepPropsScript.sml:886 evaluate_add_clock_eq` over the exact
finite-support `CrepSemHOLState` carrier and width-indexed words.

HOL:
  !p t res st ck. evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
    evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)

The carriers are the reviewed canonical `HolFiniteMapExact` translation for the
state's finite-map fields (`locals`, `globals`, `code`) and Lean's positive-width
`BitVec width` for HOL's type-indexed `'a word`, so the tagged declaration carries
both qualifiers.  The clock-shift helper `CrepAddClock` and the supporting
commutation lemmas are Flapjack-specific infrastructure.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Clock-add helper mirroring HOL `t with clock := t.clock + ck`. -/
abbrev CrepAddClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) : CrepSemHOLState width σ :=
  { state with clock := state.clock + ck }

@[simp] theorem CrepAddClock_clock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).clock = state.clock + ck := rfl

@[simp] theorem CrepAddClock_locals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).locals = state.locals := rfl

@[simp] theorem CrepAddClock_globals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).globals = state.globals := rfl

@[simp] theorem CrepAddClock_code {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).code = state.code := rfl

@[simp] theorem CrepAddClock_memory {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).memory = state.memory := rfl

@[simp] theorem CrepAddClock_memaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).memaddrs = state.memaddrs := rfl

@[simp] theorem CrepAddClock_shMemaddrs {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).shMemaddrs = state.shMemaddrs := rfl

@[simp] theorem CrepAddClock_be {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).be = state.be := rfl

@[simp] theorem CrepAddClock_ffi {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).ffi = state.ffi := rfl

@[simp] theorem CrepAddClock_baseAddr {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).baseAddr = state.baseAddr := rfl

@[simp] theorem CrepAddClock_topAddr {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    (CrepAddClock state ck).topAddr = state.topAddr := rfl

theorem fixClockCrepSemHOL_addClock {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (old : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) (ck : Nat) :
    fixClockCrepSemHOL (CrepAddClock old ck) (step.1, CrepAddClock step.2 ck) =
      (step.1, CrepAddClock (fixClockCrepSemHOL old step).2 ck) := by
  obtain ⟨res, st⟩ := step
  simp only [fixClockCrepSemHOL, CrepAddClock]
  congr 1
  by_cases h : old.clock < st.clock
  · simp [h, Nat.add_lt_add_iff_right]
  · simp [h, Nat.add_lt_add_iff_right]

theorem decClockCrepSemHOL_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) (h : state.clock ≠ 0) :
    decClockCrepSemHOL (CrepAddClock state ck) =
      CrepAddClock (decClockCrepSemHOL state) ck := by
  simp only [decClockCrepSemHOL, CrepAddClock]
  rw [show state.clock + ck - 1 = state.clock - 1 + ck by omega]

@[simp] theorem CrepSemHOLState.setVar_addClock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : HolWordLab width) (state : CrepSemHOLState width σ) (ck : Nat) :
    CrepSemHOLState.setVar name value (CrepAddClock state ck) =
      CrepAddClock (CrepSemHOLState.setVar name value state) ck := rfl

@[simp] theorem CrepSemHOLState.setGlobals_addClock {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : HolWordLab width) (state : CrepSemHOLState width σ) (ck : Nat) :
    CrepSemHOLState.setGlobals key value (CrepAddClock state ck) =
      CrepAddClock (CrepSemHOLState.setGlobals key value state) ck := rfl

@[simp] theorem CrepSemHOLState.emptyLocals_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    CrepSemHOLState.emptyLocals (CrepAddClock state ck) =
      CrepAddClock (CrepSemHOLState.emptyLocals state) ck := rfl

theorem evalCrepSemHOLExp_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (expression : CrepExpHOL width) (ck : Nat) :
    evalCrepSemHOLExp (CrepAddClock state ck) expression =
      evalCrepSemHOLExp state expression :=
  evalCrepSemHOLExp_upd_clock_eq state expression (state.clock + ck)

theorem crepExactEvalExpClassical_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expression : CrepExpHOL width) (ck : Nat) :
    crepExactEvalExpClassical (CrepAddClock state ck) expression =
      crepExactEvalExpClassical state expression := by
  classical
  unfold crepExactEvalExpClassical crepExactEvalExp
  exact evalCrepSemHOLExp_addClock state expression ck

theorem crepShMemLoadExactHOL_addClock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] (ck : Nat) :
    crepShMemLoadExactHOL name address nb (CrepAddClock state ck) =
      (let p := crepShMemLoadExactHOL name address nb state
       (p.1, CrepAddClock p.2 ck)) := by
  by_cases hnb : nb = 0
  · subst hnb
    by_cases hmem : state.shMemaddrs address
    · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 0]
          ((crepClockWordToBytes address).map UInt8.toBitVec) <;>
        simp [crepShMemLoadExactHOL, hmem, hffi]
    · simp [crepShMemLoadExactHOL, hmem]
  · by_cases hmem : state.shMemaddrs (panByteAlignHOL address)
    · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          ((crepClockWordToBytes address).map UInt8.toBitVec) <;>
        simp [crepShMemLoadExactHOL, hnb, hmem, hffi]
    · simp [crepShMemLoadExactHOL, hnb, hmem]

theorem crepShMemStoreExactHOL_addClock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs] (ck : Nat) :
    crepShMemStoreExactHOL name address nb (CrepAddClock state ck) =
      (let p := crepShMemStoreExactHOL name address nb state
       (p.1, CrepAddClock p.2 ck)) := by
  rcases hlookup : state.locals.lookup name with _ | ⟨v⟩
  · simp [crepShMemStoreExactHOL, hlookup]
  · cases v with
    | word value =>
      by_cases hnb : nb = 0
      · subst hnb
        by_cases hmem : state.shMemaddrs address
        · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 0]
              (List.map UInt8.toBitVec (crepClockWordToBytes value) ++
                List.map UInt8.toBitVec (crepClockWordToBytes address)) <;>
            simp [crepShMemStoreExactHOL, hlookup, hmem, hffi]
        · simp [crepShMemStoreExactHOL, hlookup, hmem]
      · by_cases hmem : state.shMemaddrs (panByteAlignHOL address)
        · cases hffi : callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
              (List.take nb (List.map UInt8.toBitVec (crepClockWordToBytes value)) ++
                List.map UInt8.toBitVec (crepClockWordToBytes address)) <;>
            simp [crepShMemStoreExactHOL, hlookup, hnb, hmem, hffi]
        · simp [crepShMemStoreExactHOL, hlookup, hnb, hmem]

theorem crepExactEvalExp_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (value : CrepExpHOL width) (ck : Nat) :
    crepExactEvalExp (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).memaddrs a)) value =
      crepExactEvalExp state (fun a => Classical.propDecidable (state.memaddrs a)) value := by
  letI : DecidablePred state.memaddrs := fun a => Classical.propDecidable (state.memaddrs a)
  unfold crepExactEvalExp
  exact evalCrepSemHOLExp_addClock state value ck

theorem crepExactMemStore32_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (address : BitVec width) (value : BitVec 32) (ck : Nat) :
    crepExactMemStore32 (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).memaddrs a)) address value =
      crepExactMemStore32 state (fun a => Classical.propDecidable (state.memaddrs a))
        address value := by
  unfold crepExactMemStore32
  rfl

theorem crepExactMemStoreByte_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (address : BitVec width) (byte : UInt8) (ck : Nat) :
    crepExactMemStoreByte (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).memaddrs a)) address byte =
      crepExactMemStoreByte state (fun a => Classical.propDecidable (state.memaddrs a))
        address byte := by
  unfold crepExactMemStoreByte
  rfl

theorem crepShMemLoadHOL_addClock {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) (ck : Nat) :
    crepShMemLoadHOL operator name address (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).shMemaddrs a)) =
      (let p := crepShMemLoadHOL operator name address state
          (fun a => Classical.propDecidable (state.shMemaddrs a))
       (p.1, CrepAddClock p.2 ck)) := by
  letI : DecidablePred state.shMemaddrs := fun a => Classical.propDecidable (state.shMemaddrs a)
  unfold crepShMemLoadHOL
  exact crepShMemLoadExactHOL_addClock name address (crepShMemByteWidth operator) state ck

theorem crepShMemStoreHOL_addClock {width : Nat} [NeZero width] {σ : Type}
    (operator : CrepMemOp) (name : Nat) (address : BitVec width)
    (state : CrepSemHOLState width σ) (ck : Nat) :
    crepShMemStoreHOL operator name address (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).shMemaddrs a)) =
      (let p := crepShMemStoreHOL operator name address state
          (fun a => Classical.propDecidable (state.shMemaddrs a))
       (p.1, CrepAddClock p.2 ck)) := by
  letI : DecidablePred state.shMemaddrs := fun a => Classical.propDecidable (state.shMemaddrs a)
  unfold crepShMemStoreHOL
  exact crepShMemStoreExactHOL_addClock name address (crepShMemByteWidth operator) state ck

theorem crepExactMemLoadByteWord8_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (ck : Nat) :
    crepExactMemLoadByteWord8 (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).memaddrs a)) =
      crepExactMemLoadByteWord8 state (fun a => Classical.propDecidable (state.memaddrs a)) := by
  unfold crepExactMemLoadByteWord8
  rfl

theorem crepExactWriteBytearrayWord8_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (address : BitVec width) (bytes : List (BitVec 8))
    (ck : Nat) :
    crepExactWriteBytearrayWord8 (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).memaddrs a)) address bytes =
      crepExactWriteBytearrayWord8 state (fun a => Classical.propDecidable (state.memaddrs a))
        address bytes := by
  unfold crepExactWriteBytearrayWord8
  rfl

theorem evalCrepSemHOLExps_addClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expressions : List (CrepExpHOL width)) (ck : Nat) :
    expressions.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ (CrepAddClock state ck)
        (fun a => Classical.propDecidable ((CrepAddClock state ck).memaddrs a))) =
      expressions.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ state
        (fun a => Classical.propDecidable (state.memaddrs a))) := by
  letI : DecidablePred state.memaddrs := fun a => Classical.propDecidable (state.memaddrs a)
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [List.mapM_cons]
      rw [evalCrepSemHOLExp_addClock, ih]

theorem crepStampExactDomains_addClock {width : Nat} [NeZero width] {σ : Type}
    (base : CrepSemHOLState width σ) (state : CrepSemHOLState width σ) (ck : Nat) :
    crepStampExactDomains (CrepAddClock base ck) (CrepAddClock state ck) =
      CrepAddClock (crepStampExactDomains base state) ck := rfl

theorem CrepAddClock_setLocals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (ck : Nat) :
    { CrepAddClock state ck with locals := locals } =
      CrepAddClock { state with locals := locals } ck := rfl

namespace CrepPropsEvaluateAddClockFiniteSupport

/-- Local same-module witness for the canonical finite-support `CrepSemHOLState`
carrier used by the qualified `evaluate_add_clock_eq` port below (an imported
witness may be re-exported as a local one). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepPropsEvaluateAddClockFiniteSupport

/-- Exact port of HOL `crepPropsScript.sml:886 evaluate_add_clock_eq`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_add_clock_eq" 886
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalCrepSemHOLProgExact_add_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (t : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (st : CrepSemHOLState width σ) (ck : Nat)
    (h : evalCrepSemHOLProgExact t p = (res, st))
    (hnt : res ≠ some CrepResultHOLExact.timeOut) :
    evalCrepSemHOLProgExact { t with clock := t.clock + ck } p =
      (res, { st with clock := st.clock + ck }) := by
  let P : CrepProgHOL width × CrepSemHOLState width σ → Prop :=
    fun pair => match pair with
    | (prog, state) =>
        ∀ (res : Option (CrepResultHOLExact width)) (st : CrepSemHOLState width σ)
          (ck : Nat),
          evalCrepSemHOLProgExact state prog = (res, st) →
          res ≠ some CrepResultHOLExact.timeOut →
          evalCrepSemHOLProgExact (CrepAddClock state ck) prog =
            (res, CrepAddClock st ck)
  have hmain : ∀ v v1, P (v, v1) := by
    refine evalCrepSemHOLProgExact_induct P ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_skip] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      rw [evalCrepSemHOLProgExact_skip]
    · intro v e prog s ih res st ck heval hnt
      rw [evalCrepSemHOLProgExact_dec] at heval ⊢
      rw [crepExactEvalExpClassical_addClock] at ⊢
      cases hval : crepExactEvalExpClassical s e with
      | none =>
          simp only [hval] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some value =>
          simp only [hval] at heval ⊢
          cases hstep : evalCrepSemHOLProgExact (CrepSemHOLState.setVar v value s) prog with
          | mk r1 s1 =>
              simp only [hstep] at heval
              obtain ⟨hr, hs⟩ := Prod.mk.inj heval
              have hne : r1 ≠ some CrepResultHOLExact.timeOut := fun hbad => hnt (hr ▸ hbad)
              have ih' := ih value hval r1 s1 ck hstep hne
              rw [CrepSemHOLState.setVar_addClock]
              rw [ih']
              rw [Prod.mk.injEq]
              exact ⟨hr, by subst hs; rfl⟩
    · intro lhss pop rhss s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_primitive] at heval ⊢
      cases hmap : rhss.mapM s.locals.lookup with
      | none =>
          simp only [hmap] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some ws =>
          simp only [hmap] at heval ⊢
          cases hprim : crepPrimopHOLExact pop ws with
          | none =>
              simp only [hprim] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | some results =>
              simp only [hprim] at heval ⊢
              by_cases hcond : ((decide (lhss.length = results.length) &&
                  lhss.all (fun v => (s.locals.lookup v).isSome)) && decide lhss.Nodup) = true
              · rw [if_pos hcond] at heval ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                rfl
              · rw [if_neg hcond] at heval ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                rfl
    · intro v src s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_assign] at heval ⊢
      rw [crepExactEvalExp_addClock] at ⊢
      cases hsrc : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
      | none =>
          simp only [hsrc] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some w =>
          simp only [hsrc] at heval ⊢
          cases hlook : s.locals.lookup v with
          | none =>
              simp only [hlook] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | some val =>
              simp only [hlook] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
    · intro dst src s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_store] at heval ⊢
      rw [crepExactEvalExp_addClock, crepExactEvalExp_addClock] at ⊢
      cases hdst : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) dst with
      | none =>
          simp only [hdst] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some dv =>
          cases hsrc : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
          | none =>
              simp only [hdst, hsrc] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | some sv =>
              cases dv with
              | word account =>
                  cases sv with
                  | word w =>
                      cases hdec : (fun a => Classical.propDecidable (s.memaddrs a)) account with
                      | isTrue ht =>
                          simp only [hdst, hsrc, hdec] at heval ⊢
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
                      | isFalse hf =>
                          simp only [hdst, hsrc, hdec] at heval ⊢
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
    · intro dst src s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_store32] at heval ⊢
      rw [crepExactEvalExp_addClock, crepExactEvalExp_addClock] at ⊢
      cases hdst : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) dst with
      | none =>
          simp only [hdst] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some dv =>
          cases hsrc : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
          | none =>
              simp only [hdst, hsrc] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | some sv =>
              cases dv with
              | word address =>
                  cases sv with
                  | word w =>
                      simp only [crepExactMemStore32_addClock]
                      cases hstore : crepExactMemStore32 s
                          (fun a => Classical.propDecidable (s.memaddrs a)) address
                          (BitVec.ofNat 32 w.toNat) with
                      | none =>
                          simp only [hdst, hsrc, hstore] at heval ⊢
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
                      | some memory =>
                          simp only [hdst, hsrc, hstore] at heval ⊢
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
    · intro dst src s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_storeByte] at heval ⊢
      rw [crepExactEvalExp_addClock, crepExactEvalExp_addClock] at ⊢
      cases hdst : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) dst with
      | none =>
          simp only [hdst] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some dv =>
          cases hsrc : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
          | none =>
              simp only [hdst, hsrc] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | some sv =>
              cases dv with
              | word address =>
                  cases sv with
                  | word w =>
                      simp only [crepExactMemStoreByte_addClock]
                      cases hstore : crepExactMemStoreByte s
                          (fun a => Classical.propDecidable (s.memaddrs a)) address
                          (UInt8.ofNat w.toNat) with
                      | none =>
                          simp only [hdst, hsrc, hstore] at heval ⊢
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
                      | some memory =>
                          simp only [hdst, hsrc, hstore] at heval ⊢
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
    · intro dst src s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_storeGlob] at heval ⊢
      rw [crepExactEvalExp_addClock] at ⊢
      cases hsrc : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
      | none =>
          simp only [hsrc] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some w =>
          simp only [hsrc] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
    · intro operator name address s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_shMem] at heval ⊢
      rw [crepExactEvalExp_addClock] at ⊢
      cases haddr : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) address with
      | none =>
          simp only [haddr] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some av =>
          cases av with
          | word addressValue =>
              simp only [haddr] at heval ⊢
              by_cases hload : crepIsLoadMemOp operator
              · simp only [if_pos hload] at heval ⊢
                cases hlook : s.locals.lookup name with
                | none =>
                    simp only [hlook] at heval ⊢
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                    rfl
                | some val =>
                    simp only [crepShMemLoadHOL_addClock]
                    cases hrun : crepShMemLoadHOL operator name addressValue s
                        (fun a => Classical.propDecidable (s.shMemaddrs a)) with
                    | mk r1 s1 =>
                        rw [hlook] at heval
                        simp only [hrun] at heval ⊢
                        rw [Prod.mk.injEq] at heval ⊢
                        obtain ⟨hr, hs⟩ := heval
                        exact ⟨hr, by subst hs; rfl⟩
              · simp only [if_neg hload] at heval ⊢
                cases hlook : s.locals.lookup name with
                | none =>
                    simp only [hlook] at heval ⊢
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                    rfl
                | some val =>
                    cases val with
                    | word w =>
                        simp only [crepShMemStoreHOL_addClock]
                        cases hrun : crepShMemStoreHOL operator name addressValue s
                            (fun a => Classical.propDecidable (s.shMemaddrs a)) with
                        | mk r1 s1 =>
                            rw [hlook] at heval
                            simp only [hrun] at heval ⊢
                            rw [Prod.mk.injEq] at heval ⊢
                            obtain ⟨hr, hs⟩ := heval
                            exact ⟨hr, by subst hs; rfl⟩
    · intro c1 c2 s ih1 ih2 res st ck heval hnt
      rw [evalCrepSemHOLProgExact_seq_fixClockFree] at heval ⊢
      cases hfirst : evalCrepSemHOLProgExact s c1 with
      | mk r1 s1 =>
          simp only [hfirst] at heval ⊢
          cases r1 with
          | none =>
              simp only [] at heval ⊢
              have ihc1 := ih2 (none : Option (CrepResultHOLExact width)) s1 ck hfirst (by simp)
              rw [ihc1]
              dsimp only
              exact ih1 (none : Option (CrepResultHOLExact width)) s1 hfirst.symm rfl res st ck heval hnt
          | some r =>
              simp only [] at heval ⊢
              obtain ⟨hr, hs⟩ := Prod.mk.inj heval
              have hne : (some r : Option (CrepResultHOLExact width)) ≠
                  some CrepResultHOLExact.timeOut := hr.symm ▸ hnt
              have ihc1 := ih2 (some r) s1 ck hfirst hne
              rw [ihc1]
              rw [Prod.mk.injEq]
              exact ⟨hr, by subst hs; rfl⟩
    · intro e c1 c2 s ih res st ck heval hnt
      rw [evalCrepSemHOLProgExact_ite] at heval ⊢
      rw [crepExactEvalExp_addClock] at ⊢
      cases hcond : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) e with
      | none =>
          simp only [hcond] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some cv =>
          cases cv with
          | word w =>
              by_cases hw : w ≠ 0
              · simp only [hcond, if_pos hw] at heval ⊢
                have hP := ih (.word w) w hcond rfl
                rw [if_pos hw] at hP
                exact hP res st ck heval hnt
              · simp only [hcond, if_neg hw] at heval ⊢
                have hP := ih (.word w) w hcond rfl
                rw [if_neg hw] at hP
                exact hP res st ck heval hnt
    · intro n s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_break] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      rw [evalCrepSemHOLProgExact_break]
    · intro n s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_continue] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      rw [evalCrepSemHOLProgExact_continue]
    · intro e c s ih1 ih2 ih3 res st ck heval hnt
      rw [evalCrepSemHOLProgExact_while_fixClockFree] at heval ⊢
      rw [crepExactEvalExp_addClock] at ⊢
      cases hcond : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) e with
      | none =>
          simp only [hcond] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some cv =>
          cases cv with
          | word w =>
              by_cases hw : w ≠ 0
              · by_cases hclk : s.clock = 0
                · simp only [hcond, if_pos hw, dif_pos hclk] at heval
                  obtain ⟨hr, _⟩ := Prod.mk.inj heval
                  exact absurd hr.symm hnt
                · simp only [hcond, if_pos hw] at heval ⊢
                  rw [dif_neg hclk] at heval
                  rw [dif_neg (by change s.clock + ck ≠ 0; omega)]
                  conv =>
                    lhs
                    rw [decClockCrepSemHOL_addClock s ck hclk]
                  cases hbody : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c with
                  | mk r t =>
                      have hne_body : r ≠ some CrepResultHOLExact.timeOut := by
                        intro hbad
                        subst hbad
                        rw [hbody] at heval
                        exact hnt (Prod.mk.inj heval).1.symm
                      have ihb := (ih3 (.word w) w hcond rfl hw hclk) r t ck hbody hne_body
                      conv =>
                        lhs
                        rw [ihb]
                      rw [hbody] at heval
                      cases r with
                      | none =>
                          have hp := ih2 (.word w) w none t hcond rfl hw hclk hbody.symm rfl
                          exact hp res st ck heval hnt
                      | some r' =>
                          cases r' with
                          | timeOut =>
                              exact absurd rfl hne_body
                          | «continue» k =>
                              cases k with
                              | zero =>
                                  have hp := ih1 (.word w) w (some (.continue 0)) t (.continue 0) 0 hcond rfl hw hclk hbody.symm rfl rfl rfl
                                  exact hp res st ck heval hnt
                              | succ k' =>
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                  rfl
                          | «break» k =>
                              cases k with
                              | zero =>
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                  rfl
                              | succ k' =>
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                  rfl
                          | error =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              rfl
                          | «return» vs =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              rfl
                          | «exception» ex =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              rfl
                          | finalFfi ev =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              rfl
              · simp only [hcond, if_neg hw] at heval ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                rfl
    · intro es s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_return] at heval ⊢
      rw [evalCrepSemHOLExps_addClock] at ⊢
      cases hval : es.mapM (@evalCrepSemHOLExp width ‹NeZero width› σ s
          (fun a => Classical.propDecidable (s.memaddrs a))) with
      | none =>
          simp only [hval] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some ws =>
          simp only [hval] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
    · intro e s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_raise] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      rw [evalCrepSemHOLProgExact_raise]
      rfl
    · intro s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_tick] at heval
      by_cases hclk : s.clock = 0
      · rw [if_pos hclk] at heval
        obtain ⟨hr, _⟩ := Prod.mk.inj heval
        exact absurd hr.symm hnt
      · rw [if_neg hclk] at heval
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        rw [evalCrepSemHOLProgExact_tick]
        rw [if_neg (by change s.clock + ck ≠ 0; omega)]
        rw [decClockCrepSemHOL_addClock s ck hclk]
    · intro caltyp fname argexps s ihexn ihnormal res st ck heval hnt
      classical
      rw [evalCrepSemHOLProgExact_call_holShape] at heval ⊢
      rw [evalCrepSemHOLExps_addClock] at ⊢
      have hargsconv : List.mapM (evalCrepSemHOLExp s) argexps =
          List.mapM (crepExactEvalExpClassical s) argexps := rfl
      rw [hargsconv] at heval ⊢
      cases hargs : List.mapM (crepExactEvalExpClassical s) argexps with
      | none =>
          simp only [hargs] at heval ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
          rfl
      | some args =>
          simp only [hargs] at heval ⊢
          cases hcode : lookupCodeFiniteHOL s.code fname args args.length with
          | none =>
              simp only [hcode] at heval ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
              rfl
          | some pair =>
              obtain ⟨prog, newlocals⟩ := pair
              simp only [hcode] at heval ⊢
              have hcode' : lookupCodeHOL s.code.lookup fname args args.length =
                  some (prog, newlocals.lookup) := by
                have h := lookupCodeFiniteHOL_lookup s.code fname args args.length
                rw [hcode] at h
                simpa using h.symm
              have hcodeFin : lookupCodeHOLFinite s.code.lookup fname args args.length =
                  some (prog, newlocals) :=
                (lookupCodeHOLFinite_eq_some_iff s.code.lookup fname args args.length
                  prog newlocals).mpr hcode'
              by_cases hbad : (crepCallFixed_domains.match_1
                  (fun _ => Prop) caltyp (fun _ => False) (fun rts snd => ¬ rts.Nodup))
              · rw [if_pos hbad] at heval ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                rfl
              · rw [if_neg hbad] at heval ⊢
                by_cases hclk : s.clock = 0
                · rw [if_pos hclk] at heval
                  obtain ⟨hr, _⟩ := Prod.mk.inj heval
                  exact absurd hr.symm hnt
                · rw [if_neg hclk] at heval
                  rw [if_neg (by omega)]
                  cases hbody : evalCrepSemHOLProgExact
                      { decClockCrepSemHOL s with locals := newlocals } prog with
                  | mk r t =>
                      have hne_body : r ≠ some CrepResultHOLExact.timeOut := by
                        intro hbadT
                        subst hbadT
                        rw [hbody] at heval
                        exact hnt (Prod.mk.inj heval).1.symm
                      have ihb := ihnormal args (prog, newlocals) prog newlocals
                        hargs hcodeFin rfl hbad hclk r t ck hbody hne_body
                      have hbodystate : ({ decClockCrepSemHOL (CrepAddClock s ck) with
                          locals := newlocals } : CrepSemHOLState width σ) =
                          CrepAddClock ({ decClockCrepSemHOL s with
                            locals := newlocals } : CrepSemHOLState width σ) ck := by
                        rw [decClockCrepSemHOL_addClock s ck hclk, CrepAddClock_setLocals]
                      rw [hbodystate] at ⊢
                      rw [ihb] at ⊢
                      rw [hbody] at heval
                      cases r with
                      | none =>
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                          rfl
                      | some r' =>
                          cases r' with
                          | timeOut => exact absurd rfl hne_body
                          | error =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              simp only [CrepSemHOLState.emptyLocals_addClock]
                          | finalFfi ev =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              simp only [CrepSemHOLState.emptyLocals_addClock]
                          | «break» l =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              rfl
                          | «continue» l =>
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                              rfl
                          | «return» retvs =>
                              cases caltyp with
                              | none =>
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                  simp only [CrepSemHOLState.emptyLocals_addClock]
                              | some cval =>
                                  obtain ⟨rts, handler⟩ := cval
                                  dsimp only at heval ⊢
                                  by_cases hlen : retvs.length ≠ rts.length
                                  · rw [if_pos hlen] at heval ⊢
                                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                    rfl
                                  · rw [if_neg hlen] at heval ⊢
                                    cases hmap : List.mapM s.locals.lookup rts with
                                    | none =>
                                        simp only [hmap] at heval ⊢
                                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                        rfl
                                    | some val =>
                                        simp only [hmap] at heval ⊢
                                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                        rw [CrepAddClock_setLocals]
                          | «exception» eid =>
                              cases caltyp with
                              | none =>
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                  simp only [CrepSemHOLState.emptyLocals_addClock]
                              | some cval =>
                                  obtain ⟨rts, handler⟩ := cval
                                  cases handler with
                                  | none =>
                                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                      simp only [CrepSemHOLState.emptyLocals_addClock]
                                  | some hval =>
                                      obtain ⟨eid', p⟩ := hval
                                      dsimp only at heval ⊢
                                      by_cases heq : eid = eid'
                                      · rw [if_pos heq] at heval ⊢
                                        have hihx := ihexn args (prog, newlocals) prog newlocals
                                          (evalCrepSemHOLProgExact { decClockCrepSemHOL s with
                                            locals := newlocals } prog)
                                          (some (.exception eid)) t (.exception eid) eid
                                          (rts, some (eid', p)) rts (some (eid', p))
                                          (eid', p) eid' p
                                          hargs hcodeFin rfl hbad hclk rfl hbody rfl rfl rfl rfl rfl rfl heq
                                        have hihx' := hihx res st ck heval hnt
                                        rw [CrepAddClock_setLocals]
                                        exact hihx'
                                      · rw [if_neg heq] at heval ⊢
                                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
                                        simp only [CrepSemHOLState.emptyLocals_addClock]
    · intro ffi_index ptr1 len1 ptr2 len2 s res st ck heval hnt
      rw [evalCrepSemHOLProgExact_extCall] at heval ⊢
      rw [CrepAddClock_locals] at ⊢
      rw [crepExactMemLoadByteWord8_addClock] at ⊢
      cases h1 : s.locals.lookup len1 with
      | none => simp only [h1] at heval ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
      | some v1 =>
          cases h2 : s.locals.lookup ptr1 with
          | none => simp only [h1, h2] at heval ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
          | some v2 =>
              cases h3 : s.locals.lookup len2 with
              | none => simp only [h1, h2, h3] at heval ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
              | some v3 =>
                  cases h4 : s.locals.lookup ptr2 with
                  | none => simp only [h1, h2, h3, h4] at heval ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
                  | some v4 =>
                      cases v1 with
                      | word configLength =>
                          cases v2 with
                          | word configAddress =>
                              cases v3 with
                              | word arrayLengthValue =>
                                  cases v4 with
                                  | word arrayAddress =>
                                      cases hread1 : readBytearrayWordHOL (byteWidth := 8)
                                          configAddress configLength.toNat
                                          (crepExactMemLoadByteWord8 s
                                            (fun a => Classical.propDecidable (s.memaddrs a))) with
                                      | none => simp only [h1, h2, h3, h4, hread1] at heval ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
                                      | some configBytes =>
                                          cases hread2 : readBytearrayWordHOL (byteWidth := 8)
                                              arrayAddress arrayLengthValue.toNat
                                              (crepExactMemLoadByteWord8 s
                                                (fun a => Classical.propDecidable (s.memaddrs a))) with
                                          | none => simp only [h1, h2, h3, h4, hread1, hread2] at heval ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
                                          | some arrayBytes =>
                                              cases hffi : callFFIHOL s.ffi (.extCall ffi_index)
                                                  configBytes arrayBytes with
                                              | final event =>
                                                  simp only [h1, h2, h3, h4, hread1, hread2, hffi] at heval ⊢
                                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
                                              | ret newFfi newBytes =>
                                                  simp only [h1, h2, h3, h4, hread1, hread2, hffi,
                                                    crepExactWriteBytearrayWord8_addClock] at heval ⊢
                                                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval; rfl
  exact hmain p t res st ck h hnt

end Flapjack
