import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.CutState
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.LoopRecursion

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

set_option maxRecDepth 4000 in
/-- Internal formulation of the full Loop helper using the shared case motive.
The exported HOL statement will spell out its error disjunction. -/
theorem evaluateApplyColourLoopCore {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : NumSet) (body : WordLangProgHOL (BitVec width))
    (ihBody : applyColourGoal C F body) :
    applyColourGoal C F (.loop names body exitNames) := by
  classical
  have hrenameLn : ∀ f, applyNummapKey f (.ln : NumSet) = .ln := fun _ => rfl
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  suffices ∀ n (st cst : WordSemStateFiniteExact width C F) f live lt,
      st.clock = n →
      colouringOk f (.loop names body exitNames) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain names) st.locals cst.locals →
      applyColourPost f (.loop names body exitNames) live lt st cst by
    intro st cst f live lt h
    exact this st.clock st cst f live lt rfl ⟨h.1, h.2.1, by simpa only [getLive] using h.2.2⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro st cst f live lt hn ⟨hc, hs, hl⟩
    cases hcut : cutState (names, .ln) st with
    | none =>
      refine ⟨cst.permute, ?_⟩
      have hcutp := cutState_withPermute st cst.permute (names, .ln)
      rw [hcut] at hcutp
      simp [ht, hcutp]
    | some entry =>
      obtain ⟨centry, hccut, hentry, hentrylocals⟩ :=
        cutStateColourTransportLive names .ln f (sptDomain (getLive body names ((names, exitNames) :: lt)))
          st cst entry
          (by simpa only [sptDomain_ln, or_false] using hc.1)
          hs (by simpa only [sptDomain_ln, or_false] using hl) hcut
      have hccut' : cutState (applyNummapKey f names, .ln) cst = some centry := by
        simpa only [applyNummapsKey, hrenameLn] using hccut
      obtain ⟨p, hp⟩ := ihBody entry centry f names ((names, exitNames) :: lt)
        ⟨hc.2.2, hentry, hentrylocals⟩
      rcases hb : evaluate body { entry with permute := p } with ⟨res, out⟩
      rw [hb] at hp
      dsimp only at hp
      have hcutp : cutState (names, .ln) { st with permute := p } =
          some { entry with permute := p } := by
        rw [cutState_withPermute, hcut]; rfl
      by_cases herr : res = some .error
      · refine ⟨p, ?_⟩
        simp [ht, hcutp, hb, herr, wordSemContLoop, wordSemExitLoop]
      · rw [if_neg herr] at hp
        rcases hcb : evaluate (applyColour f body) centry with ⟨cres, cout⟩
        rw [hcb] at hp
        dsimp only at hp
        obtain ⟨hres, hsout, hlout⟩ := hp
        subst cres
        have hbase : ∀ q, cutState (names, .ln) { st with permute := q } =
            some { entry with permute := q } := by
          intro q; rw [cutState_withPermute, hcut]; rfl
        by_cases hcont : wordSemContLoop res = true
        · have hnames : strongLocalsRel f (sptDomain names) out.locals cout.locals := by
            cases res with
            | none => exact hlout
            | some r =>
              cases r <;> simp [wordSemContLoop] at hcont
              case «continue» k =>
                subst k
                simpa [applyColourLocals, sptOel_eq_getElem?] using hlout
          have hclock := wsrClock hsout
          by_cases hz : out.clock = 0
          · refine ⟨p, ?_⟩
            have hcz : cout.clock = 0 := hclock.trans hz
            simp only [ht, hcutp, hb, applyColour, hccut', hcb, hcont, if_true, hz, hcz]
            simp_all [wordStateEqRel, applyColourLocals, flushState]
          · have hlt : (decClock out).clock < n := by
              have hbound := loopBodyRecursiveClockLt (names, .ln) body
                { st with permute := p } { entry with permute := p } out res hcutp hb hz
              simpa only [hn] using hbound
            obtain ⟨q, hq⟩ := ih (decClock out).clock hlt (decClock out) (decClock cout)
              f live lt rfl ⟨hc, wsrDecClock hsout, hnames⟩
            obtain ⟨p0, hcut0, hb0, hcomm⟩ := loopBodyOracleStitch (names, .ln) body
              { st with permute := p } { entry with permute := p } out res q hcutp hb herr
            have hcz : cout.clock ≠ 0 := by rwa [hclock]
            refine ⟨p0, ?_⟩
            have hcut0' : cutState (names, .ln) { st with permute := p0 } =
                some { entry with permute := p0 } := hcut0
            have hb0' : evaluate body { entry with permute := p0 } =
                (res, { out with permute := q }) := hb0
            have hsrc : evaluate (.loop names body exitNames) { st with permute := p0 } =
                evaluate (.loop names body exitNames) { decClock out with permute := q } := by
              rw [ht, hcut0']
              simp only [hb0', hcont, if_true, hz, if_false, wordSemSTOP, hcomm]
            have htgt : evaluate (applyColour f (.loop names body exitNames)) cst =
                evaluate (applyColour f (.loop names body exitNames)) (decClock cout) := by
              change evaluate (.loop (applyNummapKey f names) (applyColour f body)
                (applyNummapKey f exitNames)) cst = _
              rw [ht, hccut']
              simp only [hcb, hcont, if_true, hcz, if_false, wordSemSTOP, applyColour]
            rw [hsrc, htgt]
            exact hq
        · cases res with
          | none => simp [wordSemContLoop] at hcont
          | some r =>
            cases r with
            | «break» k =>
              cases k with
              | zero =>
                cases hexit : cutState (exitNames, .ln) out with
                | none =>
                    refine ⟨p, ?_⟩
                    simp only [ht, hcutp, hb, wordSemContLoop, Bool.false_eq_true, if_false, hexit]
                    trivial
                | some final =>
                    obtain ⟨cfinal, hcexit, hsfinal, hdom, hlocal, _⟩ :=
                      cutStateColourTransport exitNames .ln f out cout final
                        (by simpa only [sptDomain_ln, or_false] using hc.2.1)
                        hsout
                        (by simpa [applyColourLocals, sptOel_eq_getElem?, sptDomain_ln] using hlout)
                        hexit
                    have hcexit' : cutState (applyNummapKey f exitNames, .ln) cout = some cfinal := by
                      simpa only [applyNummapsKey, hrenameLn] using hcexit
                    refine ⟨p, ?_⟩
                    simp only [ht, hcutp, hb, applyColour, hccut', hcb, wordSemContLoop,
                      Bool.false_eq_true, if_false, hexit, hcexit']
                    refine ⟨trivial, hsfinal, ?_⟩
                    exact strongLocalsRelExtendAux f _ (sptDomain live) _ _
                      ⟨fun key hk => by rwa [hdom] at hk, hlocal⟩
              | succ k =>
                refine ⟨p, ?_⟩
                simp only [ht, hcutp, hb, applyColour, hccut', hcb, wordSemContLoop,
                  Bool.false_eq_true, if_false, wordSemExitLoop, Nat.add_sub_cancel]
                simpa [applyColourLocals, sptOel_eq_getElem?] using And.intro hsout hlout
            | «continue» k =>
              have hk : k ≠ 0 := by simpa [wordSemContLoop] using hcont
              cases k with
              | zero => contradiction
              | succ k =>
                refine ⟨p, ?_⟩
                simp only [ht, hcutp, hb, applyColour, hccut', hcb, hcont,
                  wordSemExitLoop, Nat.add_sub_cancel]
                simpa [applyColourLocals, sptOel_eq_getElem?] using And.intro hsout hlout
            | error => exact False.elim (herr rfl)
            | result a b | exception a b | timeOut | notEnoughSpace | finalFfi =>
                refine ⟨p, ?_⟩
                simp only [ht, hcutp, hb, applyColour, hccut', hcb, wordSemContLoop,
                  Bool.false_eq_true, if_false, wordSemExitLoop]
                simpa [applyColourLocals] using And.intro hsout hlout

/-- Local spelling of the Loop helper's literal error disjunction. It shares
the reviewed result-dependent locals motive and has no independent HOL original. -/
def applyColourPostDisj {width : Nat} [NeZero width] {C F : Type}
    (f : Nat → Nat) (prog : WordLangProgHOL (BitVec width)) (live : NumSet)
    (lt : List (NumSet × NumSet)) (st cst : WordSemStateFiniteExact width C F) : Prop :=
  ∃ perm',
    let (res, rst) := evaluate prog { st with permute := perm' }
    res = some .error ∨
      let (res', rcst) := evaluate (applyColour f prog) cst
      res = res' ∧ wordStateEqRel rst rcst ∧ applyColourLocals f live lt res rst.locals rcst.locals

/-- Logical conversion between the case motive and the helper's disjunction;
local infrastructure, not a new HOL theorem port. -/
theorem applyColourPost_iff_disj {width : Nat} [NeZero width] {C F : Type}
    (f : Nat → Nat) (prog : WordLangProgHOL (BitVec width)) (live : NumSet)
    (lt : List (NumSet × NumSet)) (st cst : WordSemStateFiniteExact width C F) :
    applyColourPost f prog live lt st cst ↔ applyColourPostDisj f prog live lt st cst := by
  classical
  unfold applyColourPost applyColourPostDisj
  apply exists_congr
  intro p
  rcases evaluate prog { st with permute := p } with ⟨res, rst⟩
  dsimp only
  by_cases he : res = some .error <;> simp [he]

namespace EvaluateApplyColourLoopWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateApplyColourLoopWitnesses

/-- HOL's full local Loop helper (931-1103). The four conjuncts are precisely
the original colouring/state/local premises and the sole universally quantified
body induction hypothesis. `applyColourPostDisj` spells the original error
disjunction; no target success, extra injection, clock, or oracle premise occurs. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColourLoopHelper {width : Nat} [NeZero width] {C F : Type} :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat)
      (names : NumSet) (body : WordLangProgHOL (BitVec width)) (exitNames live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.loop names body exitNames) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.loop names body exitNames) live lt)) st.locals cst.locals ∧
        (∀ (st cst : WordSemStateFiniteExact width C F) f live lt,
          colouringOk f body live lt ∧ wordStateEqRel st cst ∧
            strongLocalsRel f (sptDomain (getLive body live lt)) st.locals cst.locals →
          applyColourPostDisj f body live lt st cst) →
      applyColourPostDisj f (.loop names body exitNames) live lt st cst := by
  rintro st cst f names body exitNames live lt ⟨hc, hs, hl, ihBody⟩
  apply (applyColourPost_iff_disj _ _ _ _ _ _).mp
  apply evaluateApplyColourLoopCore names exitNames body ?_ st cst f live lt ⟨hc, hs, hl⟩
  intro st cst f live lt h
  exact (applyColourPost_iff_disj _ _ _ _ _ _).mpr (ihBody st cst f live lt h)

/-- Genuine Loop constructor case of HOL `evaluate_apply_colour`. Only the
body induction hypothesis supplements the original three premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_Loop {width : Nat} [NeZero width] {C F : Type}
    (names : NumSet) (body : WordLangProgHOL (BitVec width)) (exitNames : NumSet)
    (ihBody : applyColourGoal C F body) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.loop names body exitNames) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.loop names body exitNames) live lt)) st.locals cst.locals →
      applyColourPost f (.loop names body exitNames) live lt st cst :=
  evaluateApplyColourLoopCore names exitNames body ihBody

end Flapjack.WordAlloc
