import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateIoEventsMono

/-!
# wordProps `evaluate_add_clock_io_events_mono` over the exact wordSem evaluator

Proof-side counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:1639-1730`
(bead `flapjack-pxn.18.5.9.1.3`):

```
∀exps s extra.
  (SND(evaluate(exps,s))).ffi.io_events ≼
  (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
```

HOL proves it by `evaluate_ind`, using `evaluate_add_clock` and
`evaluate_io_events_mono`.  The untagged recursive core
`evaluate_add_clock_io_events_mono_aux` follows that proof, on HOL's
termination measure, with the statement of `evaluate_io_events_mono` as the
hypothesis `hmono`.  Every run that does not time out is closed by the
tagged `evaluate_add_clock`.  The timing-out paths (`Tick`, the `Seq`/`Loop`
body, `Loop` re-entry, the `Call` callee and its return or exception
handler) are closed by the induction hypothesis and `hmono`.  The tagged
theorem instantiates `hmono` with the tagged `evaluate_io_events_mono`
(bead `flapjack-pxn.18.5.9.1.2`).
-/

namespace Flapjack

namespace WordSemEvaluateAddClockIoEventsMonoSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateAddClockIoEventsMonoSupport

namespace WordSemStateFiniteExact

section AddClockIoEventsMono

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem popEnv_ffi (s s1 : WordSemStateFiniteExact width C F) (h : popEnv s = some s1) :
    s1.ffi = s.ffi := by
  unfold popEnv at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem cutState_ffi (names : WordLangCutsetsHOL) (s s1 : WordSemStateFiniteExact width C F)
    (h : cutState names s = some s1) : s1.ffi = s.ffi := by
  unfold cutState at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- A run that does not time out extends its I/O events unchanged under more clock. -/
theorem ioEvents_addClock_of_ne_timeOut (e : Nat) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (h : (evaluate p s).1 ≠ some .timeOut) :
    (evaluate p s).2.ffi.ioEvents <+: (evaluate p { s with clock := s.clock + e }).2.ffi.ioEvents := by
  rw [evaluate_add_clock_aux e p s h]
  exact List.prefix_refl _

theorem flushState_ffi (b : Bool) (s : WordSemStateFiniteExact width C F) :
    (flushState b s).ffi = s.ffi := by
  unfold flushState
  split <;> rfl

/-- A `Call` at clock `0` returns with its input `ffi`. -/
theorem evaluate_call_clock_zero_ffi
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (hz : s.clock = 0) :
    (evaluate (.call ret dest args handler) s).2.ffi = s.ffi := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  repeat' split
  all_goals first | rfl | exact flushState_ffi _ _ | simp_all

/-- After the callee of a returning `Call`, the rest of the `Call` only
    extends the callee's I/O events. -/
theorem evaluate_call_some_callee_prefix
    (hmono : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (r : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate p s = (r, s') → s.ffi.ioEvents <+: s'.ffi.ioEvents)
    (n : List Nat) (names : WordLangCutsetsHOL) (retHandler : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (xs : List (WordLocW width))
    (args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (rc : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F)
    (hg : getVars args s = some xs) (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hf : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs)
      s.code s.stackSize = some (args1, prog, ss))
    (hdc : ¬ (sptDomainEmpty names.fst ∨ ¬ n.Nodup))
    (hce : wordSemCutEnvs names s.locals = some envs) (hz : ¬ s.clock = 0)
    (hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (rc, t)) :
    t.ffi.ioEvents <+:
      (evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler) s).2.ffi.ioEvents := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hdc, hce, hz, hcv]
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · exact List.prefix_refl _
  · simp only
    split
    · exact List.prefix_refl _
    rcases hp : popEnv t with _ | s1
    · exact List.prefix_refl _
    simp only
    have hpf := popEnv_ffi _ _ hp
    split
    · rw [← hpf]
      exact hmono _ (setVars n ys s1) _ _ rfl
    · rw [hpf]
      exact List.prefix_refl _
  · cases handler with
    | none => exact List.prefix_refl _
    | some hv =>
      obtain ⟨n', hprog, l1', l2'⟩ := hv
      simp only
      split
      · exact List.prefix_refl _
      split
      · exact hmono _ (setVar n' y t) _ _ rfl
      · exact List.prefix_refl _
  all_goals exact List.prefix_refl _

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_add_clock_io_events_mono`, with HOL
    `evaluate_io_events_mono` as the hypothesis `hmono`. -/
theorem evaluate_add_clock_io_events_mono_aux
    (hmono : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (r : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate p s = (r, s') → s.ffi.ioEvents <+: s'.ffi.ioEvents)
    (e : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      (evaluate p s).2.ffi.ioEvents <+: (evaluate p { s with clock := s.clock + e }).2.ffi.ioEvents
  | .tick, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      split <;> split <;> exact List.prefix_refl _
  | .mustTerminate q, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      by_cases hz : s.termdep = 0
      · simp only [hz, if_true]
        exact List.prefix_refl _
      · simp only [hz, if_false]
        have hq : ({ { s with clock := s.clock + e } with
              clock := wordSemMustTerminateLimit width
              termdep := s.termdep - 1 } : WordSemStateFiniteExact width C F) =
            { s with
              clock := wordSemMustTerminateLimit width
              termdep := s.termdep - 1 } := rfl
        rw [hq]
        rcases evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        cases r with
        | none => exact List.prefix_refl _
        | some x => cases x <;> exact List.prefix_refl _
  | .seq c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      have hseq : ∀ t : WordSemStateFiniteExact width C F,
          (evaluate c1 t).2.ffi.ioEvents <+: (evaluate (.seq c1 c2) t).2.ffi.ioEvents := by
        intro t
        rw [ht]
        rcases h1 : evaluate c1 t with ⟨r1, t1⟩
        cases r1 with
        | none => exact hmono c2 t1 _ _ rfl
        | some _ => exact List.prefix_refl _
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      have hc := evaluate_clock c1 s r1 s1 h1
      by_cases hto : r1 = some .timeOut
      · subst hto
        have ih := evaluate_add_clock_io_events_mono_aux hmono e c1 s
        rw [h1] at ih
        have hl : evaluate (.seq c1 c2) s = (some .timeOut, s1) := by rw [ht, h1]
        rw [hl]
        exact ih.trans (hseq _)
      · have ha := evaluate_add_clock_aux e c1 s (by rw [h1]; exact hto)
        rw [h1] at ha
        rw [ht, ht, h1, ha]
        cases r1 with
        | none => exact evaluate_add_clock_io_events_mono_aux hmono e c2 s1
        | some x => exact List.prefix_refl _
  | .ite cmp r1 ri c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      have hv : getVar r1 { s with clock := s.clock + e } = getVar r1 s := rfl
      have hi : getVarImm ri { s with clock := s.clock + e } = getVarImm ri s := by
        cases ri <;> rfl
      rw [hv, hi]
      rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
        simp only [hx, hy]
      all_goals first
        | exact List.prefix_refl _
        | (rcases hw : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hw]
           · exact List.prefix_refl _
           · exact evaluate_add_clock_io_events_mono_aux hmono e c2 s
           · exact evaluate_add_clock_io_events_mono_aux hmono e c1 s)
  | .loop names c exitNames, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht, cutState_withClock s (s.clock + e)]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · exact List.prefix_refl _
      simp only [Option.map_some]
      have hc2 := cutState_clock_termdep _ _ _ hcs
      rw [← hc2.1]
      rcases hb : evaluate c s' with ⟨rb, s1⟩
      have hc := evaluate_clock c s' rb s1 hb
      by_cases hrb : rb = some .timeOut
      · subst hrb
        have ih := evaluate_add_clock_io_events_mono_aux hmono e c s'
        rw [hb] at ih
        rcases hb' : evaluate c { s' with clock := s'.clock + e } with ⟨rb', s1'⟩
        rw [hb'] at ih
        have hl : wordSemContLoop (some (WordSemResult.timeOut : WordSemResult width)) = false := rfl
        simp only [hl, Bool.false_eq_true, if_false]
        refine ih.trans ?_
        simp only
        by_cases hcont : wordSemContLoop rb' = true
        · rw [if_pos hcont]
          by_cases hz : s1'.clock = 0
          · rw [if_pos hz]
            unfold flushState
            split <;> exact List.prefix_refl _
          · rw [if_neg hz]
            exact hmono _ (decClock s1') _ _ rfl
        · rw [if_neg hcont]
          split
          · split
            · exact List.prefix_refl _
            · rename_i s2 hce
              rw [cutState_ffi _ _ _ hce]
              exact List.prefix_refl _
          · exact List.prefix_refl _
      · rw [evaluate_add_clock_aux e c s' (by rw [hb]; exact hrb), hb]
        simp only
        by_cases hcont : wordSemContLoop rb = true
        · rw [if_pos hcont, if_pos hcont]
          by_cases hz : s1.clock = 0
          · rw [if_pos hz]
            have hf : (flushState true s1).ffi = s1.ffi := by
              unfold flushState
              split <;> rfl
            show (flushState true s1).ffi.ioEvents <+: _
            rw [hf]
            by_cases hz' : s1.clock + e = 0
            · rw [if_pos hz']
              unfold flushState
              split <;> exact List.prefix_refl _
            · rw [if_neg hz']
              exact hmono _ (decClock { s1 with clock := s1.clock + e }) _ _ rfl
          · rw [if_neg hz, if_neg (by omega)]
            simp only [wordSemSTOP]
            have hd : decClock { s1 with clock := s1.clock + e } =
                { decClock s1 with clock := (decClock s1).clock + e } := by
              simp only [decClock]
              rw [show s1.clock + e - 1 = s1.clock - 1 + e by omega]
            rw [hd]
            exact evaluate_add_clock_io_events_mono_aux hmono e (.loop names c exitNames) (decClock s1)
        · rw [if_neg hcont, if_neg hcont]
          rcases rb with _ | x
          · simp [wordSemContLoop] at hcont
          · cases x with
            | «break» n =>
              cases n with
              | zero =>
                simp only
                rw [cutState_withClock s1 (s1.clock + e)]
                rcases cutState (exitNames, .ln) s1 with _ | s2
                · exact List.prefix_refl _
                · exact List.prefix_refl _
              | succ n => exact List.prefix_refl _
            | _ => exact List.prefix_refl _
  | .call ret dest args handler, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      by_cases hz : s.clock = 0
      · rw [evaluate_call_clock_zero_ffi ret dest args handler s hz]
        exact hmono _ { s with clock := s.clock + e } _ _ rfl
      rw [ht, ht, getVars_withClock s (s.clock + e)]
      rcases hg : getVars args s with _ | xs
      · exact List.prefix_refl _
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
        exact List.prefix_refl _
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp only [hf]
        exact List.prefix_refl _
      simp only [hf]
      cases ret with
      | none =>
        cases handler with
        | some _ => exact List.prefix_refl _
        | none =>
          simp only
          rw [if_neg hz, if_neg (show ¬ (s.clock + e = 0) by omega)]
          have hd : callEnv args1 ss (decClock { s with clock := s.clock + e }) =
              { callEnv args1 ss (decClock s) with
                clock := (callEnv args1 ss (decClock s)).clock + e } := by
            simp only [callEnv, decClock]
            rw [show s.clock + e - 1 = s.clock - 1 + e by omega]
          rw [hd]
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          have hc := evaluate_clock prog _ rc sc hcv
          have ih := evaluate_add_clock_io_events_mono_aux hmono e prog (callEnv args1 ss (decClock s))
          rw [hcv] at ih
          rcases hcv' : evaluate prog { callEnv args1 ss (decClock s) with
              clock := (callEnv args1 ss (decClock s)).clock + e } with ⟨rc', sc'⟩
          rw [hcv'] at ih
          simp only
          split <;> split <;> exact ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
          exact List.prefix_refl _
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact List.prefix_refl _
        simp only
        rw [if_neg hz, if_neg (show ¬ (s.clock + e = 0) by omega)]
        have hd : callEnv args1 ss (pushEnv envs handler (decClock { s with clock := s.clock + e })) =
            { callEnv args1 ss (pushEnv envs handler (decClock s)) with
              clock := (callEnv args1 ss (pushEnv envs handler (decClock s))).clock + e } := by
          have hp := pushEnv_withClock (decClock s) (s.clock - 1 + e) envs handler
          have hdc' : decClock { s with clock := s.clock + e } =
              { decClock s with clock := s.clock - 1 + e } := by
            simp only [decClock]
            rw [show s.clock + e - 1 = s.clock - 1 + e by omega]
          rw [hdc', hp]
          simp only [callEnv, pushEnv_clock, decClock]
        rw [hd]
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        have hc := evaluate_clock prog _ rc s2 hcv
        by_cases hrc : rc = some .timeOut
        · subst hrc
          have ih := evaluate_add_clock_io_events_mono_aux hmono e prog
            (callEnv args1 ss (pushEnv envs handler (decClock s)))
          rw [hcv] at ih
          rcases hcv' : evaluate prog { callEnv args1 ss (pushEnv envs handler (decClock s)) with
              clock := (callEnv args1 ss (pushEnv envs handler (decClock s))).clock + e } with
            ⟨rc', s2'⟩
          rw [hcv'] at ih
          simp only
          refine ih.trans ?_
          rcases rc' with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
          · exact List.prefix_refl _
          · simp only
            split
            · exact List.prefix_refl _
            rcases hp : popEnv s2' with _ | s1
            · exact List.prefix_refl _
            simp only
            have hpf := popEnv_ffi _ _ hp
            split
            · rw [← hpf]
              exact hmono _ (setVars n ys s1) _ _ rfl
            · rw [hpf]
              exact List.prefix_refl _
          · cases handler with
            | none => exact List.prefix_refl _
            | some hv =>
              obtain ⟨n', hprog, l1', l2'⟩ := hv
              simp only
              split
              · exact List.prefix_refl _
              split
              · exact hmono _ (setVar n' y s2') _ _ rfl
              · exact List.prefix_refl _
          all_goals exact List.prefix_refl _
        rw [evaluate_add_clock_aux e prog _ (by rw [hcv]; exact hrc), hcv]
        simp only
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · exact List.prefix_refl _
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]
            exact List.prefix_refl _
          simp only [hx, if_false]
          rw [popEnv_withClock s2 (s2.clock + e)]
          rcases hp : popEnv s2 with _ | s1
          · exact List.prefix_refl _
          simp only [Option.map_some]
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
          · have hdom' : sptDomainEqUnion ({ s1 with clock := s2.clock + e } :
                WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
            simp only [hdom, hdom', if_true]
            rw [← hc2.1]
            have hsv : setVars n ys { s1 with clock := s1.clock + e } =
                { setVars n ys s1 with clock := (setVars n ys s1).clock + e } := rfl
            rw [hsv]
            exact evaluate_add_clock_io_events_mono_aux hmono e retHandler (setVars n ys s1)
          · have hdom' : ¬ sptDomainEqUnion ({ s1 with clock := s2.clock + e } :
                WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
            simp only [hdom, hdom', if_false]
            exact List.prefix_refl _
        · cases handler with
          | none => exact List.prefix_refl _
          | some hv =>
            obtain ⟨n', hprog, l1', l2'⟩ := hv
            simp only
            by_cases hx : x ≠ WordLocW.loc l1' l2'
            · rw [if_pos hx, if_pos hx]
              exact List.prefix_refl _
            rw [if_neg hx, if_neg hx]
            by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
            · have hdom' : sptDomainEqUnion ({ s2 with clock := s2.clock + e } :
                  WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
              rw [if_pos hdom, if_pos hdom']
              have hsv : setVar n' y { s2 with clock := s2.clock + e } =
                  { setVar n' y s2 with clock := (setVar n' y s2).clock + e } := rfl
              rw [hsv]
              exact evaluate_add_clock_io_events_mono_aux hmono e hprog (setVar n' y s2)
            · have hdom' : ¬ sptDomainEqUnion ({ s2 with clock := s2.clock + e } :
                  WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
              rw [if_neg hdom, if_neg hdom']
              exact List.prefix_refl _
        all_goals exact List.prefix_refl _
  | .skip, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .move a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .inst a, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .assign a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .get a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .set a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .store a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .alloc a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .storeConsts a b c d f, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .raise a, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | WordLangProgHOL.return a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | WordLangProgHOL.break a, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | WordLangProgHOL.continue a, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .opCurrHeap a b c, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .locValue a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .install a b c d f, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .codeBufferWrite a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .dataBufferWrite a b, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .ffi a b c d f g, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
  | .shareInst a b c, s => by
      rw [evaluate_withClock_const s (s.clock + e) _ rfl]
      exact List.prefix_refl _
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

/-- Exact HOL `wordProps$evaluate_add_clock_io_events_mono`
    (`wordPropsScript.sml:1639-1642`):

    ```
    ∀exps s extra.
      (SND(evaluate(exps,s))).ffi.io_events ≼
      (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
    ```

    HOL's `≼` is `<+:`.  The recursive core `evaluate_add_clock_io_events_mono_aux`
    is applied to the tagged `evaluate_io_events_mono`.  Like that theorem, it
    concerns FFI event traces only, not the numerical results of the
    floating-point instructions (whose `FPSqrt` rendering is untagged). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_add_clock_io_events_mono {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (exps : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (extra : Nat),
      (evaluate exps s).2.ffi.ioEvents <+:
        (evaluate exps { s with clock := s.clock + extra }).2.ffi.ioEvents :=
  fun exps s extra =>
    evaluate_add_clock_io_events_mono_aux evaluate_io_events_mono extra exps s

end AddClockIoEventsMono

end WordSemStateFiniteExact

end Flapjack
