module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-!
# wordProps `evaluate_stack_max_only_grows`

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4479-4487`.
HOL proves it by `recInduct evaluate_ind`: the run under the extra clock follows
the same path as the original run, so the reached `stack_max` only grows.  Here
the same induction is a recursion on HOL's termination measure (as for
`evaluate_stack_max_le`), with the motive `∀ ck`.  The non-recursive clauses use
`evaluate_withClock_const`; each recursive clause compares the two runs through
`evaluate_add_clock`, `evaluate_stack_max_le` and `option_le_trans`.

Inherited assumption: `evaluate`'s `Inst` clause calls the tagged `inst`, which
carries `(reals_as_rational_cuts)`; the theorem here records that inherited
`docs/SOUNDNESS.md` item 8 assumption in the theorem map.
-/

namespace Flapjack

namespace WordSemEvaluateStackMaxClockSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateStackMaxClockSupport

namespace WordSemStateFiniteExact

open Flapjack.Compiler.Backend.BackendProps

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the clock clamp of `evaluate` keeps the stack
    maximum, so it never affects the comparison of the two runs.  It has no
    separate HOL original (HOL unfolds `fix_clock` in place). -/
theorem fixClock_stackMax {β : Type} (old : WordSemStateFiniteExact width C F)
    (step : β × WordSemStateFiniteExact width C F) :
    (fixClock old step).2.stackMax = step.2.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the clock clamp commutes with adding a clock
    allowance.  It has no separate HOL original. -/
theorem fixClock_addClock {β : Type} (s : WordSemStateFiniteExact width C F)
    (step : β × WordSemStateFiniteExact width C F) (ck : Nat) :
    fixClock { s with clock := s.clock + ck }
        ⟨step.1, { step.2 with clock := step.2.clock + ck }⟩ =
      ⟨step.1, { (fixClock s step).2 with clock := (fixClock s step).2.clock + ck }⟩ := by
  simp only [fixClock]
  by_cases h : s.clock < step.2.clock
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `dec_clock` keeps the stack maximum. -/
theorem decClock_stackMax (state : WordSemStateFiniteExact width C F) :
    (decClock state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `flush_state` keeps the stack maximum. -/
theorem flushState_stackMax (b : Bool) (state : WordSemStateFiniteExact width C F) :
    (flushState b state).stackMax = state.stackMax := by
  cases b <;> rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `inc_clock` keeps the stack maximum. -/
theorem incClock_stackMax (n : Nat) (state : WordSemStateFiniteExact width C F) :
    (incClock n state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `set_var` keeps the stack maximum. -/
theorem setVar_stackMax (name : Nat) (value : WordLocW width)
    (state : WordSemStateFiniteExact width C F) :
    (setVar name value state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `set_vars` keeps the stack maximum. -/
theorem setVars_stackMax (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F) :
    (setVars names values state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the stack maximum of `call_env`, as used by
    the frame the call records. -/
theorem callEnv_stackMax (args : List (WordLocW width)) (size : Option Nat)
    (state : WordSemStateFiniteExact width C F) :
    (callEnv args size state).stackMax =
      wordSemOptionMax state.stackMax
        (wordSemOptionAdd (wordSemStackSize state.stack) size) := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the frame a returning call builds from the
    pushed environment does not depend on the clock, so the stack maximum of
    the body's initial state is the same under both clocks. -/
theorem callEnv_pushEnv_stackMax_decClock (args : List (WordLocW width)) (size : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (c : Nat) :
    (callEnv args size (pushEnv envs handler (decClock { s with clock := c }))).stackMax =
      (callEnv args size (pushEnv envs handler s)).stackMax := by
  cases handler with
  | none => rfl
  | some h =>
    obtain ⟨a, b, cc, d⟩ := h
    rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `pop_env` keeps the stack maximum (HOL reads
    it from `pop_env_const`). -/
theorem popEnv_stackMax (state next : WordSemStateFiniteExact width C F)
    (h : popEnv state = some next) : next.stackMax = state.stackMax :=
  (popEnvConst state next h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `cut_state` keeps the stack maximum. -/
theorem cutState_stackMax (names : WordLangCutsetsHOL)
    (state next : WordSemStateFiniteExact width C F)
    (h : cutState names state = some next) : next.stackMax = state.stackMax := by
  unfold cutState at h
  split at h
  · cases h
  · cases h
    rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): a statement that neither reads the clock nor
    recurses reaches the same stack maximum under any clock, exactly as HOL's
    `evaluate_clock_with_const` clause gives it. -/
theorem stackMax_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true) (ck : Nat) :
    optionLe (evaluate p s).2.stackMax
      (evaluate p { s with clock := s.clock + ck }).2.stackMax := by
  simp only [evaluate_withClock_const s (s.clock + ck) p hp]
  exact optionLe_refl _

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the loop's exit branch keeps the stack
    maximum of the state it starts from. -/
theorem loopExitTail_stackMax {width : Nat} [NeZero width] {C : Type} {F : Type}
    (exitNames : WordLangNumSetHOL) (u : WordSemStateFiniteExact width C F)
    (rb : Option (WordSemResult width)) :
    ((match rb with
        | some (.break 0) =>
            (match cutState (exitNames, .ln) u with
             | none => (some .error, u)
             | some s2 => (none, s2))
        | _x => (wordSemExitLoop rb, u)) :
        Option (WordSemResult width) × WordSemStateFiniteExact width C F).2.stackMax =
      u.stackMax := by
  split
  · split
    · rfl
    · rename_i s2 hce
      rw [cutState_stackMax _ _ _ hce]
  · rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the loop's tail keeps at least the stack
    maximum of the state it starts from. -/
theorem loopTail_stackMax {width : Nat} [NeZero width] {C : Type} {F : Type}
    (names : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width))
    (exitNames : WordLangNumSetHOL) (u : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) :
    optionLe u.stackMax
      ((if wordSemContLoop res = true then
          (if u.clock = 0 then (some .timeOut, flushState true u)
           else evaluate (wordSemSTOP (.loop names c exitNames)) (decClock u))
        else
          (match res with
            | some (.break 0) =>
                (match cutState (exitNames, .ln) u with
                 | none => (some .error, u)
                 | some s2 => (none, s2))
            | _x => (wordSemExitLoop res, u))) :
        Option (WordSemResult width) × WordSemStateFiniteExact width C F).2.stackMax := by
  by_cases hcont : wordSemContLoop res = true
  · rw [if_pos hcont]
    by_cases hz : u.clock = 0
    · rw [if_pos hz]
      exact optionLe_refl _
    · rw [if_neg hz]
      exact evaluate_stack_max_le (.loop names c exitNames) (decClock u) _ _ rfl
  · rw [if_neg hcont, loopExitTail_stackMax exitNames u res]
    exact optionLe_refl _

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): a sum of option sizes is bounded above by its
    maximum with anything. -/
theorem optionLe_optionMax_left (a b : Option Nat) :
    optionLe a (wordSemOptionMax a b) := by
  rcases a with _ | x
  · rcases b with _ | y
    all_goals simp [wordSemOptionMax, optionLe]
  rcases b with _ | y
  · simp [wordSemOptionMax, optionLe]
  simp only [wordSemOptionMax, optionLe]
  omega

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the returning-call continuation never lowers
    the stack maximum below the state the body run reached. -/
theorem callTailSome_optionLe {width : Nat} [NeZero width] {C : Type} {F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (retHandler : WordLangProgHOL (BitVec width)) (n : List Nat) (l1 l2 : Nat)
    (r : Option (WordSemResult width)) (st : WordSemStateFiniteExact width C F) :
    optionLe st.stackMax
      ((match (r, st) with
        | (some (.result x ys), s2) =>
            if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
            else
              match popEnv s2 with
              | none => (some .error, s2)
              | some s1 =>
                  if sptDomainEqUnion s1.locals envs.1 envs.2 then
                    evaluate retHandler (setVars n ys s1)
                  else (some .error, s1)
        | (some (.exception x y), s2) =>
            match handler with
            | none => (some (.exception x y), s2)
            | some (n', hprog, l1', l2') =>
                if x ≠ .loc l1' l2' then (some .error, s2)
                else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                  evaluate hprog (setVar n' y s2)
                else (some .error, s2)
        | (none, s2) => (some .error, s2)
        | (some (.break _), s2) => (some .error, s2)
        | (some (.continue _), s2) => (some .error, s2)
        | res => res) :
        Option (WordSemResult width) × WordSemStateFiniteExact width C F).2.stackMax := by
  rcases r with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · dsimp only
    exact optionLe_refl _
  · dsimp only
    by_cases hx : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
    · rw [if_pos hx]
      exact optionLe_refl _
    · rw [if_neg hx]
      rcases hp : popEnv st with _ | s1
      · exact optionLe_refl _
      · dsimp only
        by_cases hdom : sptDomainEqUnion s1.locals envs.1 envs.2
        · rw [if_pos hdom]
          have h1 := popEnv_stackMax st s1 hp
          have h2 : (setVars n ys s1).stackMax = s1.stackMax := setVars_stackMax n ys s1
          have h3 := evaluate_stack_max_le retHandler (setVars n ys s1) _ _ rfl
          rw [h2, h1] at h3
          exact h3
        · rw [if_neg hdom]
          have h1 := popEnv_stackMax st s1 hp
          rw [h1]
          exact optionLe_refl _
  · dsimp only
    cases handler with
    | none => exact optionLe_refl _
    | some hv =>
      obtain ⟨n', hprog, l1', l2'⟩ := hv
      dsimp only
      by_cases hx : x ≠ .loc l1' l2'
      · rw [if_pos hx]
        exact optionLe_refl _
      · rw [if_neg hx]
        by_cases hdom : sptDomainEqUnion st.locals envs.1 envs.2
        · rw [if_pos hdom]
          have h2 : (setVar n' y st).stackMax = st.stackMax := setVar_stackMax n' y st
          have h3 := evaluate_stack_max_le hprog (setVar n' y st) _ _ rfl
          rw [h2] at h3
          exact h3
        · rw [if_neg hdom]
          exact optionLe_refl _
  · change optionLe st.stackMax st.stackMax
    exact optionLe_refl _
  · change optionLe st.stackMax st.stackMax
    exact optionLe_refl _
  · change optionLe st.stackMax st.stackMax
    exact optionLe_refl _
  · change optionLe st.stackMax st.stackMax
    exact optionLe_refl _
  · change optionLe st.stackMax st.stackMax
    exact optionLe_refl _
  · change optionLe st.stackMax st.stackMax
    exact optionLe_refl _

end Helpers

section Evaluate

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): running the same program under a larger clock
    never lowers the reached stack maximum.  The clauses follow HOL's
    `evaluate_ind` cases. -/
theorem stackMax_incClock :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) (ck : Nat),
      optionLe (evaluate p s).2.stackMax
        (evaluate p { s with clock := s.clock + ck }).2.stackMax
  | .tick, s, ck => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      simp only [ht]
      split
      · split
        · exact optionLe_refl _
        · exact optionLe_refl _
      · split
        · exact optionLe_refl _
        · exact optionLe_refl _
  | .mustTerminate q, s, ck => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [ht]
      split
      · exact optionLe_refl _
      · have hU : ({ { s with clock := s.clock + ck } with
              clock := wordSemMustTerminateLimit width
              termdep := s.termdep - 1 } : WordSemStateFiniteExact width C F) =
            { s with
              clock := wordSemMustTerminateLimit width
              termdep := s.termdep - 1 } := rfl
        rw [hU]
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        simp only
        cases r with
        | none => exact optionLe_refl _
        | some x => cases x <;> exact optionLe_refl _
  | .seq c1 c2, s, ck => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [ht]
      rcases h1 : evaluate c1 s with ⟨r1, u1⟩
      rcases h2 : evaluate c1 { s with clock := s.clock + ck } with ⟨r1', u1'⟩
      have hc := evaluate_clock c1 s r1 u1 h1
      have ih := stackMax_incClock c1 s ck
      rw [h1, h2] at ih
      cases r1 with
      | none =>
          have hlong := evaluate_add_clock ck c1 s none u1 ⟨h1, by simp⟩
          rw [h2] at hlong
          simp only [Prod.mk.injEq] at hlong
          obtain ⟨hr1', hu1'⟩ := hlong
          subst hr1'
          subst hu1'
          exact stackMax_incClock c2 u1 ck
      | some x =>
          by_cases hto : x = .timeOut
          · subst hto
            cases r1' with
            | none =>
                exact optionLe_trans ih (evaluate_stack_max_le c2 u1' _ _ rfl)
            | some y => exact ih
          · have hlong := evaluate_add_clock ck c1 s (some x) u1 ⟨h1, by simpa using hto⟩
            rw [h2] at hlong
            simp only [Prod.mk.injEq] at hlong
            obtain ⟨hr1', hu1'⟩ := hlong
            subst hr1'
            subst hu1'
            exact ih
  | .ite cmp r1 ri c1 c2, s, ck => by
      have hreb := evaluate_def_rebound (width := width) (C := C) (F := F)
      have ht := hreb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [ht]
      have hv : getVar r1 { s with clock := s.clock + ck } = getVar r1 s := rfl
      have hi : getVarImm ri { s with clock := s.clock + ck } = getVarImm ri s := by
        cases ri <;> rfl
      rw [hv, hi]
      rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
        simp only [hx, hy]
      all_goals try exact optionLe_refl _
      rcases hw : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hw]
      · exact optionLe_refl _
      · exact stackMax_incClock c2 s ck
      · exact stackMax_incClock c1 s ck
  | .loop names c exitNames, s, ck => by
      have hreb := evaluate_def_rebound (width := width) (C := C) (F := F)
      have ht := hreb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [ht]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · have hcs' : cutState (names, .ln) { s with clock := s.clock + ck } = none := by
          rw [cutState_withClock, hcs]
          rfl
        rw [hcs']
        exact optionLe_refl _
      · have hc2 := cutState_clock_termdep _ _ _ hcs
        have hcs' : cutState (names, .ln) { s with clock := s.clock + ck } =
            some { s' with clock := s.clock + ck } := by
          rw [cutState_withClock, hcs]
          rfl
        rw [hcs', ← hc2.1]
        rcases hb : evaluate c s' with ⟨rb, u1⟩
        rcases hb' : evaluate c { s' with clock := s'.clock + ck } with ⟨rb', u1'⟩
        have hc := evaluate_clock c s' rb u1 hb
        have ih := stackMax_incClock c s' ck
        rw [hb, hb'] at ih
        simp only [hb, hb']
        by_cases hto : rb = some .timeOut
        · rw [hto] at ih ⊢
          exact optionLe_trans ih (loopTail_stackMax names c exitNames u1' rb')
        · have hlong := evaluate_add_clock ck c s' rb u1 ⟨hb, hto⟩
          rw [hb'] at hlong
          simp only [Prod.mk.injEq] at hlong
          obtain ⟨hrb', hu1'⟩ := hlong
          rw [hrb', hu1'] at ih ⊢
          by_cases hcont : wordSemContLoop rb = true
          · rw [if_pos hcont]
            rw [if_pos hcont]
            simp only []
            by_cases hz : u1.clock = 0
            · rw [if_pos hz]
              by_cases hz2 : u1.clock + ck = 0
              · rw [if_pos hz2]
                exact ih
              · rw [if_neg hz2]
                exact optionLe_trans ih
                  (evaluate_stack_max_le (.loop names c exitNames)
                    (decClock { u1 with clock := u1.clock + ck }) _ _ rfl)
            · rw [if_neg hz]
              have hz2 : u1.clock + ck ≠ 0 := by omega
              rw [if_neg hz2]
              have hd : decClock { u1 with clock := u1.clock + ck } =
                  { decClock u1 with clock := (decClock u1).clock + ck } := by
                simp only [decClock]
                rw [show u1.clock + ck - 1 = u1.clock - 1 + ck by omega]
              rw [hd]
              exact stackMax_incClock (.loop names c exitNames) (decClock u1) ck
          · rw [if_neg hcont]
            rw [if_neg hcont]
            rcases rb with _ | ⟨x, ys⟩ | ⟨x, y⟩ | n | n | _ | _ | _ | _
            · exact ih
            · exact ih
            · exact ih
            · split
              · split
                · split
                  · exact ih
                  · rename_i s2' hce'
                    rw [cutState_stackMax _ _ _ hce']
                    exact ih
                · rename_i s2 hce
                  rw [cutState_stackMax _ _ _ hce]
                  split
                  · exact ih
                  · rename_i s2' hce'
                    rw [cutState_stackMax _ _ _ hce']
                    exact ih
              · exact ih
            · exact ih
            · exact ih
            · exact ih
            · exact ih
            · exact ih
  | .call ret dest args handler, s, ck => by
      have hreb := evaluate_def_rebound (width := width) (C := C) (F := F)
      have ht := hreb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      simp only [ht]
      simp only [getVars_withClock]
      rcases hg : getVars args s with _ | xs
      · dsimp only
        exact optionLe_refl _
      simp only [hg]
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
        exact optionLe_refl _
      have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
      simp only [hbad', Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · dsimp only
        exact optionLe_refl _
      simp only [hf]
      cases ret with
      | none =>
        cases handler with
        | some _ => exact optionLe_refl _
        | none =>
          by_cases hz : s.clock = 0
          · rw [if_pos hz]
            by_cases hz2 : s.clock + ck = 0
            · rw [if_pos hz2, flushState_stackMax, flushState_stackMax]
              exact optionLe_refl _
            · rw [if_neg hz2, flushState_stackMax]
              rcases hcv : evaluate prog
                  (callEnv args1 ss (decClock { s with clock := s.clock + ck }))
                with ⟨rc, sc⟩
              simp only [hcv]
              have hst : (decClock { s with clock := s.clock + ck } :
                  WordSemStateFiniteExact width C F).stackMax = s.stackMax := rfl
              have h1 : optionLe s.stackMax
                  (callEnv args1 ss (decClock { s with clock := s.clock + ck })).stackMax := by
                have hm := optionLe_optionMax_left
                  (decClock { s with clock := s.clock + ck }).stackMax
                  (wordSemOptionAdd (wordSemStackSize
                    (decClock { s with clock := s.clock + ck }).stack) ss)
                rwa [hst] at hm
              have h2 := evaluate_stack_max_le prog
                (callEnv args1 ss (decClock { s with clock := s.clock + ck })) rc sc hcv
              by_cases hb : wordSemBadFunReturn rc = true
              · rw [if_pos hb]
                exact optionLe_trans h1 h2
              · rw [if_neg hb]
                exact optionLe_trans h1 h2
          · rw [if_neg hz]
            have hz2 : s.clock + ck ≠ 0 := by omega
            rw [if_neg hz2]
            have hd : callEnv args1 ss (decClock { s with clock := s.clock + ck }) =
                { callEnv args1 ss (decClock s) with
                  clock := (callEnv args1 ss (decClock s)).clock + ck } := by
              simp only [callEnv, decClock]
              rw [show s.clock + ck - 1 = s.clock - 1 + ck by omega]
            rw [hd]
            rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
            rcases hcv' : evaluate prog { callEnv args1 ss (decClock s) with
                clock := (callEnv args1 ss (decClock s)).clock + ck } with ⟨rc', sc'⟩
            simp only [hcv, hcv']
            have hrec := stackMax_incClock prog (callEnv args1 ss (decClock s)) ck
            rw [hcv, hcv'] at hrec
            by_cases hb : wordSemBadFunReturn rc = true
            · rw [if_pos hb]
              by_cases hb' : wordSemBadFunReturn rc' = true
              · rw [if_pos hb']
                exact hrec
              · rw [if_neg hb']
                exact hrec
            · rw [if_neg hb]
              by_cases hb' : wordSemBadFunReturn rc' = true
              · rw [if_pos hb']
                exact hrec
              · rw [if_neg hb']
                exact hrec
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
          exact optionLe_refl _
        have hdc' : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) := hdc
        simp only [hdc', if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact optionLe_refl _
        simp only [hce]
        by_cases hz : s.clock = 0
        · rw [if_pos hz]
          by_cases hz2 : s.clock + ck = 0
          · rw [if_pos hz2]
            dsimp only
            rw [flushState_stackMax, flushState_stackMax]
            rw [show s.clock + ck = s.clock by omega]
            exact optionLe_refl _
          · rw [if_neg hz2, flushState_stackMax]
            rcases hcv : evaluate prog
                (callEnv args1 ss
                  (pushEnv envs handler (decClock { s with clock := s.clock + ck })))
              with ⟨rc, sc⟩
            simp only [hcv]
            have h2 := evaluate_stack_max_le prog
              (callEnv args1 ss (pushEnv envs handler (decClock { s with clock := s.clock + ck })))
              rc sc hcv
            rw [callEnv_pushEnv_stackMax_decClock] at h2
            exact optionLe_trans h2
              (callTailSome_optionLe envs handler retHandler n l1 l2 rc sc)
        · rw [if_neg hz]
          have hz2 : s.clock + ck ≠ 0 := by omega
          rw [if_neg hz2]
          have hd : callEnv args1 ss
              (pushEnv envs handler (decClock { s with clock := s.clock + ck })) =
              { callEnv args1 ss (pushEnv envs handler (decClock s)) with
                clock := (callEnv args1 ss (pushEnv envs handler (decClock s))).clock + ck } := by
            have hp := pushEnv_withClock (decClock s) (s.clock - 1 + ck) envs handler
            have hdc' : decClock { s with clock := s.clock + ck } =
                { decClock s with clock := s.clock - 1 + ck } := by
              simp only [decClock]
              rw [show s.clock + ck - 1 = s.clock - 1 + ck by omega]
            rw [hdc', hp]
            simp only [callEnv, pushEnv_clock, decClock]
          rw [hd]
          rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
            with ⟨rc, sc⟩
          rcases hcv' : evaluate prog { callEnv args1 ss (pushEnv envs handler (decClock s)) with
              clock := (callEnv args1 ss (pushEnv envs handler (decClock s))).clock + ck }
            with ⟨rc', sc'⟩
          have hrec := stackMax_incClock prog
            (callEnv args1 ss (pushEnv envs handler (decClock s))) ck
          rw [hcv, hcv'] at hrec
          by_cases hto : rc = some .timeOut
          · rw [hto]
            exact optionLe_trans hrec
              (callTailSome_optionLe envs handler retHandler n l1 l2 rc' sc')
          · have hlong := evaluate_add_clock ck prog
              (callEnv args1 ss (pushEnv envs handler (decClock s))) rc sc ⟨hcv, hto⟩
            rw [hcv'] at hlong
            simp only [Prod.mk.injEq] at hlong
            obtain ⟨hrc', hsc'⟩ := hlong
            subst hrc'
            subst hsc'
            rcases rc' with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
            · dsimp only
              exact optionLe_refl _
            · dsimp only
              by_cases hx : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
              · simp only [if_pos hx]
                exact optionLe_refl _
              simp only [if_neg hx]
              rw [popEnv_withClock sc (sc.clock + ck)]
              rcases hp : popEnv sc with _ | s1
              · dsimp only
                exact optionLe_refl _
              · simp only [hp, Option.map_some]
                by_cases hdom : sptDomainEqUnion s1.locals envs.1 envs.2
                · simp only [if_pos hdom]
                  have hc := evaluate_clock prog
                    (callEnv args1 ss (pushEnv envs handler (decClock s))) _ sc hcv
                  have hc2 : s1.clock = sc.clock ∧ s1.termdep = sc.termdep :=
                    ⟨popEnv_clock sc s1 hp, popEnv_termdep sc s1 hp⟩
                  rw [show sc.clock = s1.clock from (popEnv_clock sc s1 hp).symm]
                  exact stackMax_incClock retHandler (setVars n ys s1) ck
                · simp only [if_neg hdom]
                  exact optionLe_refl _
            · dsimp only
              cases handler with
              | none => exact optionLe_refl _
              | some hv =>
                have hc := evaluate_clock prog
                  (callEnv args1 ss (pushEnv envs (some hv) (decClock s))) _ sc hcv
                obtain ⟨n', hprog, l1', l2'⟩ := hv
                by_cases hx : x ≠ .loc l1' l2'
                · simp only [if_pos hx]
                  exact optionLe_refl _
                simp only [if_neg hx]
                by_cases hdom : sptDomainEqUnion sc.locals envs.1 envs.2
                · simp only [if_pos hdom]
                  exact stackMax_incClock hprog (setVar n' y sc) ck
                · simp only [if_neg hdom]
                  exact optionLe_refl _
            · dsimp only
              exact optionLe_refl _
            · dsimp only
              exact optionLe_refl _
            · dsimp only
              exact optionLe_refl _
            · dsimp only
              exact optionLe_refl _
            · dsimp only
              exact optionLe_refl _
            · dsimp only
              exact optionLe_refl _
  | .skip, s, ck => stackMax_const s _ (by rfl) ck
  | .move a b, s, ck => stackMax_const s _ (by rfl) ck
  | .inst a, s, ck => stackMax_const s _ (by rfl) ck
  | .assign a b, s, ck => stackMax_const s _ (by rfl) ck
  | .get a b, s, ck => stackMax_const s _ (by rfl) ck
  | .set a b, s, ck => stackMax_const s _ (by rfl) ck
  | .store a b, s, ck => stackMax_const s _ (by rfl) ck
  | .alloc a b, s, ck => stackMax_const s _ (by rfl) ck
  | .storeConsts a b c d f, s, ck => stackMax_const s _ (by rfl) ck
  | .raise a, s, ck => stackMax_const s _ (by rfl) ck
  | WordLangProgHOL.return a b, s, ck => stackMax_const s _ (by rfl) ck
  | WordLangProgHOL.break a, s, ck => stackMax_const s _ (by rfl) ck
  | WordLangProgHOL.continue a, s, ck => stackMax_const s _ (by rfl) ck
  | .opCurrHeap a b c, s, ck => stackMax_const s _ (by rfl) ck
  | .locValue a b, s, ck => stackMax_const s _ (by rfl) ck
  | .install a b c d f, s, ck => stackMax_const s _ (by rfl) ck
  | .codeBufferWrite a b, s, ck => stackMax_const s _ (by rfl) ck
  | .dataBufferWrite a b, s, ck => stackMax_const s _ (by rfl) ck
  | .ffi a b c d f g, s, ck => stackMax_const s _ (by rfl) ck
  | .shareInst a b c, s, ck => stackMax_const s _ (by rfl) ck
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

end Evaluate

/-- Exact HOL `evaluate_stack_max_only_grows` (`wordPropsScript.sml:4479`):
    running the same program under a larger clock never lowers the reached
    stack maximum, stated over the two runs' results as HOL states it.

    Inherited assumption: the statement mentions the native `evaluate` whose
    `Inst` clause calls the tagged `inst`, which carries
    `(reals_as_rational_cuts)`; `docs/SOUNDNESS.md` item 8 applies to FP
    instructions, and no numerical FP claim is made here. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_stack_max_only_grows"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_stack_max_only_grows {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F) (ck : Nat)
    (r' : Option (WordSemResult width)) (t' : WordSemStateFiniteExact width C F) :
    (evaluate p s = (r, t) ∧ evaluate p (incClock ck s) = (r', t')) →
      optionLe t.stackMax t'.stackMax := by
  rintro ⟨h1, h2⟩
  have hinc : incClock ck s = { s with clock := s.clock + ck } := rfl
  have h := stackMax_incClock p s ck
  rw [← hinc] at h
  rw [h1, h2] at h
  exact h

end WordSemStateFiniteExact

end Flapjack
