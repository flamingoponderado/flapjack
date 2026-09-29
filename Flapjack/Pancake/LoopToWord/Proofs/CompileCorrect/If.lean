import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Pancake.Proofs.LoopToWord.AccVarsAcc

namespace Flapjack.LoopToWord.CompileCorrect

namespace IfWitnesses

/-- Same-module roundtrip for the If case's loopSem finite-map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the If case's wordSem finite-map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end IfWitnesses

/-- Flapjack-specific proof support for the If case: restricting source locals
preserves the lookup simulation. HOL uses `lookup_inter_alt` inline rather than
declaring this lemma separately. -/
theorem localsRel_inter_if {width : Nat} [NeZero width]
    (ctxt : Spt Nat) (src dst : Spt (WordLocW width)) (live : NumSet)
    (h : localsRelHOL ctxt src dst) : localsRelHOL ctxt (sptInter src live) dst := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro name value hv
  rw [sptLookup_sptInter] at hv
  split at hv
  · exact h.2.2 name value hv
  · contradiction

/-- Flapjack-specific proof support for HOL's If case. A non-error source
`cut_res` after a simulated branch is implemented by the target's trailing
Tick. No target evaluation is assumed: it is constructed from the branch
result relation. -/
theorem cutRes_tick {width : Nat} [NeZero width] {C F : Type}
    (ctxt : Spt Nat) (retv : WordLocW width)
    (initial target : WordSemStateFiniteExact width C F)
    (source final : LoopSemStateFiniteExact width F) (live : NumSet)
    (branchResult : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (targetResult : Option (WordSemResult width))
    (result : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (hcut : LoopSemStateFiniteExact.cutRes live (branchResult, source) = (result, final))
    (hne : result ≠ some .error) (hffi : target.ffi = source.ffi)
    (hrel : resultCase ctxt retv initial branchResult source targetResult target) :
    ∃ targetFinal resultFinal,
      (match targetResult with
        | none => WordSemStateFiniteExact.evaluate .tick target
        | some r => (some r, target)) = (resultFinal, targetFinal) ∧
      targetFinal.ffi = final.ffi ∧
      resultCase ctxt retv initial result final resultFinal targetFinal := by
  cases branchResult with
  | some r =>
    simp only [LoopSemStateFiniteExact.cutRes, Prod.mk.injEq] at hcut
    rcases hcut with ⟨rfl, rfl⟩
    have ht : targetResult ≠ none := by
      intro he
      cases r <;> simp_all [resultCase]
    cases targetResult with
    | none => exact False.elim (ht rfl)
    | some r => exact ⟨target, some r, rfl, hffi, hrel⟩
  | none =>
    rcases hrel with ⟨hstate, rfl, hret, hlocals, hstack, hhandler⟩
    have hclock := loopToWordStateRelImpClockHOLExact source target hstate
    simp only [LoopSemStateFiniteExact.cutRes] at hcut
    cases hc : LoopSemStateFiniteExact.cutState live source with
    | none => simp [hc] at hcut; obtain ⟨rfl, rfl⟩ := hcut; exact False.elim (hne rfl)
    | some cut =>
      rw [hc] at hcut
      have hsub : LoopSemStateFiniteExact.sptSubsetLive live source.locals := by
        classical
        exact Classical.byContradiction fun hn => by
          rw [LoopSemStateFiniteExact.cutState_eq_none_of_not_subset live source hn] at hc
          contradiction
      rw [LoopSemStateFiniteExact.cutState_of_subset live source hsub] at hc
      cases hc
      by_cases hz : source.clock = 0
      · simp [hz] at hcut
        obtain ⟨rfl, rfl⟩ := hcut
        refine ⟨WordSemStateFiniteExact.flushState true target, some .timeOut, ?_, ?_, rfl⟩
        · simp [WordSemStateFiniteExact.evaluate, hclock, hz]
        · exact hffi
      · simp [hz] at hcut
        obtain ⟨rfl, rfl⟩ := hcut
        refine ⟨WordSemStateFiniteExact.decClock target, none, ?_, hffi, ?_⟩
        · simp [WordSemStateFiniteExact.evaluate, hclock, hz]
        · refine ⟨?_, rfl, hret, localsRel_inter_if ctxt source.locals target.locals live hlocals,
            hstack, hhandler⟩
          simpa [loopToWordStateRelHOLExact, LoopSemStateFiniteExact.decClock,
            WordSemStateFiniteExact.decClock, hclock] using hstate

/-- Genuine If induction case of HOL `compile_correct`, resumed at line 982.
The sole IH is conditional on the exact source operand lookups and comparison;
it retains every original goal premise and the full existential conclusion. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_If {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : RegImm (BitVec width)) (c1 c2 : HolLoopProg width)
    (live : NumSet) (s : LoopSemStateFiniteExact width F)
    (ih : ∀ (v2 v3 : Option (WordLocW width)) (v5 : WordLocW width) (x : BitVec width)
        (v13 : WordLocW width) (y : BitVec width) (b : Bool),
      (sptLookup r1 s.locals, LoopSemStateFiniteExact.getVarImm ri s) = (v2, v3) →
      v2 = some v5 → v5 = .word x → v3 = some v13 → v13 = .word y →
      b = Compiler.Encoders.Asm.wordCmpHOL cmp x y →
      PropertyAt C (if b then c1 else c2) s) :
    PropertyAt C (.ite cmp r1 ri c1 c2 live) s := by
  intro res final t ctxt retv l ⟨heval, hne, hstate, hlocals, hret, hdim, hword, hacc⟩
  have hchildAcc (b : Bool) :
      ∀ k, sptMem k (accVarsHOL (if b then c1 else c2) .ln) → sptMem k ctxt := by
    intro k hk
    have hs : sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k ↔
        sptDomain (accVarsHOL c1 .ln) k ∨ sptDomain (accVarsHOL c2 .ln) k := by
      rw [accVarsAccHOL c1 (accVarsHOL c2 .ln)]
    apply hacc k
    change sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k
    apply hs.mpr
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hk
    · exact Or.inr hk
    · exact Or.inl hk
  simp only [LoopSemStateFiniteExact.evaluate] at heval
  cases hx : sptLookup r1 s.locals with
  | none => simp [hx] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
  | some xv =>
    cases xv with
    | loc a b => simp [hx] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
    | word x =>
      cases hy : LoopSemStateFiniteExact.getVarImm ri s with
      | none => simp [hx, hy] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
      | some yv =>
        cases yv with
        | loc a b => simp [hx, hy] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
        | word y =>
          let b := Compiler.Encoders.Asm.wordCmpHOL cmp x y
          let child := if b then c1 else c2
          have hprop : PropertyAt C child s :=
            ih _ _ _ x _ y b (by rw [hx, hy]) rfl rfl rfl rfl rfl
          have htx := localsRelHOLGetVar ctxt s.locals t r1 (.word x) ⟨hlocals, hx⟩
          let targetRi : WordRegImm (BitVec width) :=
            match (generalizing := false) ri with
            | .imm w => .imm w
            | .reg n => .reg (findVarHOL ctxt n)
          have hty : WordSemStateFiniteExact.getVarImm targetRi t = some (.word y) := by
            cases ri with
            | imm w => simpa [LoopSemStateFiniteExact.getVarImm, targetRi,
                WordSemStateFiniteExact.getVarImm] using hy
            | reg n => exact localsRelHOLGetVar ctxt s.locals t n (.word y) ⟨hlocals, hy⟩
          have hcut : LoopSemStateFiniteExact.cutRes live
              (LoopSemStateFiniteExact.evaluate child s) = (res, final) := by
            cases hb : b <;> simpa [hx, hy, child, b, hb] using heval
          rcases hc : LoopSemStateFiniteExact.evaluate child s with ⟨cr, cs⟩
          have hcne : cr ≠ some .error := by
            intro h
            simp [hc, h, LoopSemStateFiniteExact.cutRes] at hcut
            obtain ⟨rfl, rfl⟩ := hcut
            exact hne rfl
          obtain ⟨ct, tr, htarget, hffi, hr⟩ := hprop cr cs t ctxt retv
            (if b then l else (compHOL ctxt c1 l).2)
            ⟨hc, hcne, hstate, hlocals, hret, hdim, hword, hchildAcc b⟩
          obtain ⟨tf, rf, htick, hff, hresult⟩ :=
            cutRes_tick ctxt retv t ct cs final live cr tr res (by simpa [hc] using hcut)
              hne hffi hr
          refine ⟨tf, rf, ?_, hff, hresult⟩
          rcases hcomp1 : compHOL ctxt c1 l with ⟨wc1, labels1⟩
          rcases hcomp2 : compHOL ctxt c2 labels1 with ⟨wc2, labels2⟩
          unfold compHOL
          simp only [hcomp1, hcomp2]
          change WordSemStateFiniteExact.evaluate
            (.seq (.ite cmp (findVarHOL ctxt r1) targetRi
              wc1 wc2) .tick) t =
            (rf, tf)
          rw [WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.fix_clock_evaluate]
          have hchoose : WordSemStateFiniteExact.evaluate
              (.ite cmp (findVarHOL ctxt r1) targetRi
                wc1 wc2) t =
              (tr, ct) := by
            rw [WordSemStateFiniteExact.evaluate]
            simp only [htx, hty, wordSemWordCmp]
            cases hb : b <;> simpa [child, b, hb, hcomp1, hcomp2] using htarget
          rw [hchoose]
          cases tr <;> exact htick

end Flapjack.LoopToWord.CompileCorrect
