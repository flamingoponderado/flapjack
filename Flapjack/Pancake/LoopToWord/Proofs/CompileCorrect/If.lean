import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Property
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.HandlerTail
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
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (final : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.ite cmp r1 ri c1 c2 live) s = (res, final) ∧
        res ≠ some .error ∧ loopToWordStateRelHOLExact s t ∧
        localsRelHOL ctxt s.locals t.locals ∧ sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧ ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (.ite cmp r1 ri c1 c2 live) .ln) → sptMem k ctxt) →
      ∃ tf rf,
        WordSemStateFiniteExact.evaluate (compHOL ctxt (.ite cmp r1 ri c1 c2 live) l).1 t =
          (rf, tf) ∧ tf.ffi = final.ffi ∧ resultCase ctxt retv t res final rf tf := by
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
            handlerTail ctxt retv t t live cr cs tr ct res final hr hffi rfl rfl
              (by simpa [hc] using hcut) hne
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
