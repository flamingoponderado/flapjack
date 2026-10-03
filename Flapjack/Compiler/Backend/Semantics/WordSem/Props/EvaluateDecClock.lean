import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock

/-!
# `wordProps$evaluate_dec_clock`

Port of `wordPropsScript.sml:1475-1581`: a run started with exactly the clock
it consumes ends with clock zero and is otherwise unchanged. Proved by recursion
on HOL's evaluator measure, using `evaluate_add_clock` to re-extend the clock of
a completed first phase, as HOL does.
-/

namespace Flapjack.WordSemStateFiniteExact

open Flapjack

section DecClock

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_dec_clock` (Flapjack infrastructure). -/
theorem evaluate_dec_clock_aux :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate p { s with clock := s.clock - (evaluate p s).2.clock } =
        ((evaluate p s).1, { (evaluate p s).2 with clock := 0 })
  | .tick, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      by_cases hz : s.clock = 0
      · simp only [ht, hz, if_true, flushState]
      · rw [ht s]
        simp only [hz, if_false]
        rw [ht]
        have hk : s.clock - (decClock s).clock = 1 := by simp only [decClock]; omega
        simp only [hk]
        simp [decClock]
  | .mustTerminate q, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      by_cases hz : s.termdep = 0
      · simp only [ht, hz, if_true, Nat.sub_self]
      · rw [ht s]
        simp only [hz, if_false]
        rcases he : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rcases r with _ | x
        · simp only [Nat.sub_self]
          rw [ht]
          simp only [hz, if_false]
          have hq : ({ { s with clock := 0 } with
                clock := wordSemMustTerminateLimit width
                termdep := s.termdep - 1 } : WordSemStateFiniteExact width C F) =
              { s with
                clock := wordSemMustTerminateLimit width
                termdep := s.termdep - 1 } := rfl
          rw [hq, he]
        · cases x <;> simp only [Nat.sub_self] <;> rw [ht] <;> simp only [hz, if_false] <;>
            (have hq : ({ { s with clock := 0 } with
                clock := wordSemMustTerminateLimit width
                termdep := s.termdep - 1 } : WordSemStateFiniteExact width C F) =
              { s with
                clock := wordSemMustTerminateLimit width
                termdep := s.termdep - 1 } := rfl) <;> rw [hq, he]
  | .seq c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht s]
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      have hc1 := evaluate_clock c1 s r1 s1 h1
      have ih1 := evaluate_dec_clock_aux c1 s
      rw [h1] at ih1
      cases r1 with
      | none =>
        simp only
        rcases h2 : evaluate c2 s1 with ⟨r2, s2⟩
        have hc2 := evaluate_clock c2 s1 r2 s2 h2
        have ih2 := evaluate_dec_clock_aux c2 s1
        rw [h2] at ih2
        simp only at ih1 ih2 ⊢
        rw [ht]
        have hadd := evaluate_add_clock (s1.clock - s2.clock) c1
          { s with clock := s.clock - s1.clock } none { s1 with clock := 0 } ⟨ih1, by simp⟩
        have harith : s.clock - s1.clock + (s1.clock - s2.clock) = s.clock - s2.clock := by omega
        simp only [harith, Nat.zero_add] at hadd
        rw [hadd]
        exact ih2
      | some x =>
        simp only at ih1 ⊢
        rw [ht, ih1]
  | .ite cmp r1 ri c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have ih1 := evaluate_dec_clock_aux c1 s
      have ih2 := evaluate_dec_clock_aux c2 s
      have hv : ∀ k, getVar r1 { s with clock := k } = getVar r1 s := fun _ => rfl
      have hi : ∀ k, getVarImm ri { s with clock := k } = getVarImm ri s := by
        intro k; cases ri <;> rfl
      rw [ht s, ht, hv, hi]
      rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
        simp only [Nat.sub_self]
      rcases hw : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [Nat.sub_self]
      · exact ih2
      · exact ih1
  | .loop names c exitNames, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht s]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · simp only [Nat.sub_self]
        rw [ht, cutState_withClock, hcs]
        rfl
      have hc2 := cutState_clock_termdep _ _ _ hcs
      simp only
      rcases hb : evaluate c s' with ⟨rb, s1⟩
      have hcb := evaluate_clock c s' rb s1 hb
      have ihb := evaluate_dec_clock_aux c s'
      rw [hb] at ihb
      simp only at ihb ⊢
      rw [hc2.1] at ihb
      by_cases hcont : wordSemContLoop rb = true
      · have hrb : rb ≠ some .timeOut := by
          intro hr; subst hr; simp [wordSemContLoop] at hcont
        by_cases hz : s1.clock = 0
        · simp only [hcont, hz, if_true]
          have hfc : (flushState true s1).clock = 0 := by simp [flushState, hz]
          rw [hfc, Nat.sub_zero]
          have hs : ({ s with clock := s.clock } : WordSemStateFiniteExact width C F) = s := rfl
          rw [hs, ht, hcs]
          simp only [hb, hcont, hz, if_true]
          have : ({ flushState true s1 with clock := 0 } : WordSemStateFiniteExact width C F) =
              flushState true s1 := by
            cases s1; simp_all [flushState]
          rw [this]
        · simp only [hcont, hz, if_true, if_false, wordSemSTOP]
          rcases hl : evaluate (.loop names c exitNames) (decClock s1) with ⟨rl, sl⟩
          have hcl := evaluate_clock _ _ rl sl hl
          have ihl := evaluate_dec_clock_aux (.loop names c exitNames) (decClock s1)
          rw [hl] at ihl
          simp only at ihl ⊢
          rw [ht, cutState_withClock, hcs]
          simp only [Option.map_some]
          have hadd := evaluate_add_clock (s1.clock - sl.clock) c
            { s' with clock := s.clock - s1.clock } rb { s1 with clock := 0 } ⟨ihb, hrb⟩
          have harith : s.clock - s1.clock + (s1.clock - sl.clock) = s.clock - sl.clock := by
            simp only [decClock] at hcl; omega
          simp only [harith, Nat.zero_add] at hadd
          rw [hadd]
          have hz' : s1.clock - sl.clock ≠ 0 := by simp only [decClock] at hcl; omega
          simp only [hcont, hz', if_true, if_false, wordSemSTOP]
          have hd : decClock { s1 with clock := s1.clock - sl.clock } =
              { decClock s1 with clock := (decClock s1).clock - sl.clock } := by
            simp only [decClock]
            congr 1
            omega
          rw [hd]
          exact ihl
      · simp only [hcont, Bool.false_eq_true, if_false]
        rcases rb with _ | ⟨x, ys⟩ | ⟨x, y⟩ | (_ | k) | k | _ | _ | _ | _
        · simp [wordSemContLoop] at hcont
        rotate_left 2
        · rcases hce : cutState (exitNames, .ln) s1 with _ | s2
          · dsimp only
            simp only [hce]
            rw [ht, cutState_withClock, hcs]
            simp only [Option.map_some]
            rw [ihb]
            simp [wordSemContLoop, cutState_withClock, hce]
          · have hc3 := cutState_clock_termdep _ _ _ hce
            dsimp only
            simp only [hce]
            rw [hc3.1, ht, cutState_withClock, hcs]
            simp only [Option.map_some]
            rw [ihb]
            simp [wordSemContLoop, cutState_withClock, hce]
        all_goals
          try dsimp only
          rw [ht, cutState_withClock, hcs]
          simp only [Option.map_some]
          rw [ihb]
          simp [hcont]
  | .call none dest args handler, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht s]
      rcases hg : getVars args s with _ | xs
      · simp only [Nat.sub_self]
        rw [ht, getVars_withClock, hg]
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true, Nat.sub_self]
        rw [ht, getVars_withClock, hg]
        simp [hbad]
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc none xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp only [Nat.sub_self]
        rw [ht, getVars_withClock, hg]
        simp only [hbad, Bool.false_eq_true, if_false]
        rw [show ({ s with clock := 0 } : WordSemStateFiniteExact width C F).code = s.code from rfl,
          show ({ s with clock := 0 } : WordSemStateFiniteExact width C F).stackSize = s.stackSize from rfl,
          hf]
      · cases handler with
        | some _ =>
          simp only [Nat.sub_self]
          rw [ht, getVars_withClock, hg]
          simp only [hbad, Bool.false_eq_true, if_false]
          rw [show ({ s with clock := 0 } : WordSemStateFiniteExact width C F).code = s.code from rfl,
            show ({ s with clock := 0 } : WordSemStateFiniteExact width C F).stackSize = s.stackSize from rfl,
            hf]
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dif_pos, Nat.zero_sub]
            rw [ht, getVars_withClock, hg]
            simp only [hbad, Bool.false_eq_true, if_false]
            rw [show ({ s with clock := 0 } : WordSemStateFiniteExact width C F).code = s.code from rfl,
              show ({ s with clock := 0 } : WordSemStateFiniteExact width C F).stackSize = s.stackSize from rfl,
              hf]
            cases s; simp_all [flushState]
          · simp only [hz, dif_neg, not_false_eq_true]
            rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
            have hc := evaluate_clock prog _ rc sc hcv
            have ih := evaluate_dec_clock_aux prog (callEnv args1 ss (decClock s))
            rw [hcv] at ih
            simp only [callEnv, decClock] at hc ih
            have hz' : ¬ (s.clock - sc.clock = 0) := by omega
            have hd : callEnv args1 ss (decClock { s with clock := s.clock - sc.clock }) =
                { callEnv args1 ss (decClock s) with
                  clock := (callEnv args1 ss (decClock s)).clock - sc.clock } := by
              simp only [callEnv, decClock]
              congr 1
              omega
            by_cases hb : wordSemBadFunReturn rc = true <;>
              simp only [hb, ↓reduceIte, Bool.false_eq_true] <;>
              rw [ht, getVars_withClock, hg] <;>
              simp only [hbad, Bool.false_eq_true, if_false] <;>
              rw [show ({ s with clock := s.clock - sc.clock } : WordSemStateFiniteExact width C F).code = s.code from rfl,
                show ({ s with clock := s.clock - sc.clock } : WordSemStateFiniteExact width C F).stackSize = s.stackSize from rfl,
                hf] <;>
              simp only [hz', ↓reduceIte, ↓reduceDIte, if_false, dite_false] <;>
              rw [hd] <;>
              simp only [callEnv, decClock] <;>
              simp only [ih] <;>
              simp [hb]
  | .call (some (n, names, retHandler, l1, l2)) dest args handler, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rcases hE : evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler) s with
        ⟨r, s'⟩
      have h := hE
      rw [ht] at h
      dsimp only
      rw [ht, getVars_withClock]
      dsimp only
      rcases hg : getVars args s with _ | xs
      · simp only [hg, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.sub_self]
      simp only [hg] at h ⊢
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.sub_self]
        exact ⟨rfl, rfl⟩
      simp only [hbad, Bool.false_eq_true, if_false] at h ⊢
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs)
          s.code s.stackSize with _ | ⟨args1, prog, ss⟩
      · simp only [hf, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.sub_self]
      simp only [hf] at h ⊢
      by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
      · simp only [hdc, if_true, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.sub_self]
        exact ⟨rfl, rfl⟩
      simp only [hdc, if_false] at h ⊢
      rcases hce : wordSemCutEnvs names s.locals with _ | envs
      · simp only [hce, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Nat.sub_self]
      simp only [hce] at h ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [if_pos (by simp [hz, flushState])]
        clear ht hE
        cases s
        simp_all [flushState, pushEnv_withClock]
      simp only [hz, if_false] at h
      rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
        ⟨rc, s2⟩
      rw [hcv] at h
      have hc1 := evaluate_clock prog _ rc s2 hcv
      have ih := evaluate_dec_clock_aux prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
      rw [hcv] at ih
      have hT : (callEnv args1 ss (pushEnv envs handler (decClock s))).clock = s.clock - 1 := by
        simp only [callEnv, pushEnv_clock, decClock]
      rw [hT] at hc1
      have hd : ∀ d, d ≤ s2.clock →
          callEnv args1 ss (pushEnv envs handler (decClock { s with clock := s.clock - d })) =
            { callEnv args1 ss (pushEnv envs handler (decClock s)) with
              clock := ((callEnv args1 ss (pushEnv envs handler (decClock s))).clock - s2.clock) +
                (s2.clock - d) } := by
        intro d hdl
        have hdc' : decClock { s with clock := s.clock - d } =
            { decClock s with clock := s.clock - d - 1 } := rfl
        rw [hdc', pushEnv_withClock]
        simp only [callEnv, pushEnv_clock, decClock]
        congr 1
        omega
      have ha : ∀ d, rc ≠ some .timeOut →
          evaluate prog { callEnv args1 ss (pushEnv envs handler (decClock s)) with
              clock := ((callEnv args1 ss (pushEnv envs handler (decClock s))).clock - s2.clock) +
                (s2.clock - d) } = (rc, { s2 with clock := s2.clock - d }) := by
        intro d hrc
        have := evaluate_add_clock (s2.clock - d) prog _ rc _ ⟨ih, hrc⟩
        rw [Nat.zero_add] at this
        exact this
      obtain ⟨hc1c, hc1t⟩ := hc1
      rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
      rotate_left
      · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
        · simp only [hx, if_true, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
          simp only [hx, if_true]
        simp only [hx, if_false] at h
        rcases hp : popEnv s2 with _ | s1
        · simp only [hp, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
          simp only [hx, if_false, popEnv_withClock, hp, Option.map_none]
        simp only [hp] at h
        have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
          ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
        by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
        · simp only [hdom, if_true] at h
          have hc3 := evaluate_clock retHandler _ r s' h
          have ihr := evaluate_dec_clock_aux retHandler (setVars n ys s1)
          rw [h] at ihr
          have hsc : (setVars n ys s1).clock = s2.clock := hc2.1
          rw [hsc] at hc3 ihr
          rw [if_neg (by omega), hd s'.clock (by omega), ha s'.clock (by simp)]
          dsimp only
          simp only [hx, if_false, popEnv_withClock, hp, Option.map_some]
          simp only [hdom, if_true]
          exact ihr
        · simp only [hdom, if_false, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [hc2.1]
          rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
          simp only [hx, if_false, popEnv_withClock, hp, Option.map_some]
          simp only [hdom, if_false]
      · cases handler with
        | none =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
        | some hv =>
          obtain ⟨n', hprog, l1', l2'⟩ := hv
          dsimp only at h ⊢
          by_cases hx : x ≠ WordLocW.loc l1' l2'
          · rw [if_pos hx, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
            dsimp only; rw [if_pos hx]
          rw [if_neg hx] at h
          by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
          · simp only [hdom, if_true] at h
            have hc3 := evaluate_clock hprog _ r s' h
            have ihh := evaluate_dec_clock_aux hprog (setVar n' y s2)
            rw [h] at ihh
            have hsc : (setVar n' y s2).clock = s2.clock := rfl
            rw [hsc] at hc3 ihh
            rw [if_neg (by omega), hd s'.clock (by omega), ha s'.clock (by simp)]
            dsimp only
            rw [if_neg hx]
            simp only [hdom, if_true]
            exact ihh
          · simp only [hdom, if_false, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
            dsimp only
            rw [if_neg hx]
            simp only [hdom, if_false]
      all_goals
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [if_neg (by omega), hd s2.clock (Nat.le_refl _), Nat.sub_self, Nat.add_zero, ih]
  | .skip, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .move a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .inst a, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .assign a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .get a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .set a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .store a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .alloc a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .storeConsts a b c d f, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .raise a, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | WordLangProgHOL.return a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | WordLangProgHOL.break a, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | WordLangProgHOL.continue a, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .opCurrHeap a b c, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .locValue a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .install a b c d f, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .codeBufferWrite a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .dataBufferWrite a b, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .ffi a b c d f g, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
  | .shareInst a b c, s => by
      rw [evaluate_const_clock s _ rfl, Nat.sub_self, evaluate_withClock_const s _ _ rfl]
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try (rcases hcb with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

end DecClock

/-- Exact HOL `wordProps$evaluate_dec_clock` (`wordPropsScript.sml:1475-1478`):

    ```
    ∀prog st res rst.
      evaluate(prog,st) = (res,rst) ⇒
      evaluate(prog,st with clock:=st.clock-rst.clock) = (res,rst with clock:=0)
    ```
-/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_dec_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_dec_clock {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
      evaluate prog st = (res, rst) →
      evaluate prog { st with clock := st.clock - rst.clock } = (res, { rst with clock := 0 }) := by
  intro prog st res rst h
  have := evaluate_dec_clock_aux prog st
  rw [h] at this
  exact this

end Flapjack.WordSemStateFiniteExact

namespace Flapjack.WordSemEvaluateDecClockSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end Flapjack.WordSemEvaluateDecClockSupport
