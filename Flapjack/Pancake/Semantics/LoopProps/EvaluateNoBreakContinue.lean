module

public import Flapjack.Pancake.Semantics.LoopProps.EveryProg
public import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

@[expose] public section

/-!
# Exact port of `loopPropsScript.sml` `evaluate_no_Break_Continue`

HOL (`cakeml/pancake/semantics/loopPropsScript.sml:135-172`) shows that when
every program node of `prog` satisfies
`λr. (∀n. r ≠ Break n) ∧ (∀n. r ≠ Continue n)`, an evaluation of `prog` never
returns a `Break` or `Continue` result. The proof is a `recInduct
evaluate_ind`, whose Flapjack analogue is `clockSizeLexInduction` over the
`evaluate` clauses; the recursive calls decrease the clock or the program size
exactly as the evaluator's termination measure does.

The state carrier is the exact `LoopSemStateFiniteExact`; its sole `|->` field
`globals` and the positive word width are recorded by the two qualifiers. The
`locals`/`code` fields are exact `num_map` `Spt` tree maps, which carry no
finite-map qualifier.
-/

namespace Flapjack

open Flapjack.LoopSemStateFiniteExact

namespace LoopPropsNoBreakContinueFiniteSupport

/-- Local same-module witness for the canonical finite-support
    `LoopSemStateFiniteExact` carrier used by the
    `fmap_as_finite_support := [globals]` qualified port in this module
    (re-exports the checked witness of
    `Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopPropsNoBreakContinueFiniteSupport

/-- The result predicate of HOL `evaluate_no_Break_Continue`, as a local
    abbreviation used only inside this module's proofs. -/
private def noBC {width : Nat} [NeZero width]
    (res : Option (LoopResultExact width)) : Prop :=
  (∀ n, res ≠ some (.break n)) ∧ (∀ n, res ≠ some (.continue n))

private theorem noBC_none {width : Nat} [NeZero width] :
    noBC (none : Option (LoopResultExact width)) :=
  ⟨fun n he => (by cases he), fun n he => (by cases he)⟩

/-- The possible first components of `cut_res live (NONE, s)`: `NONE`,
    `SOME Error` or `SOME TimeOut`. Local proof support for `cutRes_noBC`. -/
private theorem cutRes_none_fst_cases {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (s : LoopSemStateFiniteExact width F) :
    (cutRes live (none, s)).1 = none ∨ (cutRes live (none, s)).1 = some .error ∨
      (cutRes live (none, s)).1 = some .timeOut := by
  unfold cutRes
  cases hc : cutState live s with
  | none => simp
  | some cut =>
      by_cases hz : cut.clock = 0
      · simp [if_pos hz]
      · simp [if_neg hz]

/-- `cut_res` never turns a non-`Break`/`Continue` result into one. Local proof
    support for `evaluate_no_Break_Continue`. -/
private theorem cutRes_noBC {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    {step : Option (LoopResultExact width) × LoopSemStateFiniteExact width F}
    (h : noBC step.1) : noBC (cutRes live step).1 := by
  obtain ⟨res, s⟩ := step
  cases res with
  | some value => exact h
  | none =>
      have hc := cutRes_none_fst_cases live s
      rcases hc with hc | hc | hc
      · rw [hc]
        exact noBC_none
      · rw [hc]
        simp [noBC]
      · rw [hc]
        simp [noBC]

/-- `exit_loop` keeps a result that is not a `Break`/`Continue` unchanged. Local
    proof support for `evaluate_no_Break_Continue`. -/
private theorem exitLoop_noBC {width : Nat} [NeZero width]
    {res : Option (LoopResultExact width)} (h : noBC res) :
    noBC (Flapjack.LoopSemStateFiniteExact.exitLoop res) := by
  obtain ⟨hb, hc⟩ := h
  cases res with
  | none => simp [Flapjack.LoopSemStateFiniteExact.exitLoop, noBC]
  | some value =>
      cases value with
      | «break» n => exact absurd rfl (hb n)
      | «continue» n => exact absurd rfl (hc n)
      | result vs => simp [Flapjack.LoopSemStateFiniteExact.exitLoop, noBC]
      | exception w => simp [Flapjack.LoopSemStateFiniteExact.exitLoop, noBC]
      | timeOut => simp [Flapjack.LoopSemStateFiniteExact.exitLoop, noBC]
      | finalFfi e => simp [Flapjack.LoopSemStateFiniteExact.exitLoop, noBC]
      | error => simp [Flapjack.LoopSemStateFiniteExact.exitLoop, noBC]

/-- `sh_mem_load` never returns a `Break`/`Continue` result. Local proof support
    for `evaluate_no_Break_Continue`. -/
private theorem shMemLoad_noBC {width : Nat} [NeZero width] {F : Type} (v : Nat)
    (addr : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F) :
    noBC (shMemLoad v addr nb s).1 := by
  simp only [noBC]
  refine ⟨?_, ?_⟩
  · intro n
    rw [shMemLoad]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals simp
  · intro n
    rw [shMemLoad]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals simp

/-- `sh_mem_store` never returns a `Break`/`Continue` result. Local proof
    support for `evaluate_no_Break_Continue`. -/
private theorem shMemStore_noBC {width : Nat} [NeZero width] {F : Type} (v : Nat)
    (addr : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F) :
    noBC (shMemStore v addr nb s).1 := by
  simp only [noBC]
  refine ⟨?_, ?_⟩
  · intro n
    rw [shMemStore]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals simp
  · intro n
    rw [shMemStore]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals simp

/-- `sh_mem_op` never returns a `Break`/`Continue` result. Local proof support
    for `evaluate_no_Break_Continue`. -/
private theorem shMemOp_noBC {width : Nat} [NeZero width] {F : Type} (op : WordMemOp)
    (v : Nat) (addr : BitVec width) (s : LoopSemStateFiniteExact width F) :
    noBC (shMemOp op v addr s).1 := by
  cases op with
  | load => exact shMemLoad_noBC v addr 0 s
  | store => exact shMemStore_noBC v addr 0 s
  | load8 => exact shMemLoad_noBC v addr 1 s
  | store8 => exact shMemStore_noBC v addr 1 s
  | load16 => exact shMemLoad_noBC v addr 2 s
  | store16 => exact shMemStore_noBC v addr 2 s
  | load32 => exact shMemLoad_noBC v addr 4 s
  | store32 => exact shMemStore_noBC v addr 4 s

set_option linter.unusedSimpArgs false in
/-- Exact port of HOL `loopProps$evaluate_no_Break_Continue`
    (`cakeml/pancake/semantics/loopPropsScript.sml:135-172`):
    `evaluate (prog, s) = (res, t) ∧
       every_prog (λr. (∀n. r ≠ Break n) ∧ (∀n. r ≠ Continue n)) prog ⇒
       (∀n. res ≠ SOME (Break n)) ∧ (∀n. res ≠ SOME (Continue n))`.
    The binders follow HOL's explicit quantifier order `prog`, `s`, `res`, `t`;
    `evaluate` is the tagged `LoopSemStateFiniteExact.evaluate` (curried in
    Lean), `every_prog` is the tagged `everyProgHOL`, and `s`/`t` are the exact
    `LoopSemStateFiniteExact` carrier whose `globals` `|->` field and positive
    word width are recorded by the two qualifiers. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_no_Break_Continue"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_no_Break_Continue {width : Nat} [NeZero width] {F : Type}
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (t : LoopSemStateFiniteExact width F) :
    (evaluate prog s = (res, t) ∧
      everyProgHOL (fun r => (∀ n, r ≠ .break n) ∧ (∀ n, r ≠ .continue n)) prog) →
    (∀ n, res ≠ some (.break n)) ∧ (∀ n, res ≠ some (.continue n)) := by
  intro h
  obtain ⟨heval, hevery⟩ := h
  have key : ∀ (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      ∀ (res : Option (LoopResultExact width)) (t : LoopSemStateFiniteExact width F),
      (evaluate prog s = (res, t) ∧
        everyProgHOL (fun r => (∀ n, r ≠ .break n) ∧ (∀ n, r ≠ .continue n)) prog) →
      (∀ n, res ≠ some (.break n)) ∧ (∀ n, res ≠ some (.continue n)) := by
    refine clockSizeLexInduction (α := HolLoopProg width) (·.clock) (motive := fun p s =>
      ∀ res t, (evaluate p s = (res, t) ∧
        everyProgHOL (fun r => (∀ n, r ≠ .break n) ∧ (∀ n, r ≠ .continue n)) p) →
      (∀ n, res ≠ some (.break n)) ∧ (∀ n, res ≠ some (.continue n))) ?_
    intro p s ih res t h
    obtain ⟨heval, hevery⟩ := h
    cases p with
    | seq first second =>
        rw [evaluate] at heval
        simp only [everyProgHOL] at hevery
        have lex1 : Prod.Lex (· < ·) (· < ·) (s.clock, sizeOf first)
            (s.clock, sizeOf (HolLoopProg.seq first second)) :=
          lexLt (Nat.le_refl _) (by simp +arith)
        split at heval
        · rename_i s1 heq1
          rw [fix_clock_evaluate] at heq1
          exact ih second s1 (lexLt (evaluate_clock _ _ _ _ heq1) (by simp +arith))
            res t ⟨heval, hevery.2.2⟩
        · rename_i r1 s1 heq1
          rw [fix_clock_evaluate] at heq1
          obtain ⟨rfl, rfl⟩ := heval
          exact ih first s lex1 res t ⟨heq1, hevery.2.1⟩
    | «ite» cmp cond right tB eB live =>
        rw [evaluate] at heval
        simp only [everyProgHOL] at hevery
        have lex1 : Prod.Lex (· < ·) (· < ·) (s.clock, sizeOf tB)
            (s.clock, sizeOf (HolLoopProg.ite cmp cond right tB eB live)) :=
          lexLt (Nat.le_refl _) (by simp +arith)
        have lex2 : Prod.Lex (· < ·) (· < ·) (s.clock, sizeOf eB)
            (s.clock, sizeOf (HolLoopProg.ite cmp cond right tB eB live)) :=
          lexLt (Nat.le_refl _) (by simp +arith)
        split at heval
        · split at heval
          · cases he1 : evaluate tB s with
            | mk r1' s1' =>
                rw [he1] at heval
                have hi := ih tB s lex1 r1' s1' ⟨he1, hevery.2.1⟩
                have hstep : noBC (evaluate tB s).1 := by
                  rw [he1]
                  exact hi
                have hcr := cutRes_noBC live hstep
                rw [he1] at hcr
                rw [heval] at hcr
                exact hcr
          · cases he2 : evaluate eB s with
            | mk r2 s2 =>
                rw [he2] at heval
                have hi := ih eB s lex2 r2 s2 ⟨he2, hevery.2.2⟩
                have hstep : noBC (evaluate eB s).1 := by
                  rw [he2]
                  exact hi
                have hcr := cutRes_noBC live hstep
                rw [he2] at hcr
                rw [heval] at hcr
                exact hcr
        · simp only [Prod.mk.injEq] at heval
          obtain ⟨rfl, rfl⟩ := heval
          simp [noBC]
    | mark body =>
        rw [evaluate] at heval
        simp only [everyProgHOL] at hevery
        exact ih body s (lexLt (Nat.le_refl _) (by simp +arith)) res t ⟨heval, hevery.2⟩
    | «break» label =>
        rw [evaluate] at heval
        simp only [Prod.mk.injEq] at heval
        obtain ⟨rfl, rfl⟩ := heval
        simp only [everyProgHOL] at hevery
        exact absurd rfl (hevery.1 label)
    | «continue» label =>
        rw [evaluate] at heval
        simp only [Prod.mk.injEq] at heval
        obtain ⟨rfl, rfl⟩ := heval
        simp only [everyProgHOL] at hevery
        exact absurd rfl (hevery.2 label)
    | loop liveIn body liveOut =>
        rw [evaluate] at heval
        have heveryOrig := hevery
        simp only [everyProgHOL] at hevery
        split at heval
        · rename_i s1 hcr
          have hclock1 := cutRes_none_clock hcr
          cases he : evaluate body s1 with
          | mk r1 s2 =>
              rw [he] at heval
              have hclock2 := evaluate_clock body s1 r1 s2 he
              have hclk : (fixClock s1 (r1, s2)).2.clock < s.clock := by
                simp only [fixClock]
                split
                · omega
                · omega
              have hlex : Prod.Lex (· < ·) (· < ·) (s1.clock, sizeOf body)
                  (s.clock, sizeOf (HolLoopProg.loop liveIn body liveOut)) :=
                lexLt (Nat.le_of_lt hclock1) (by simp +arith)
              have hi := ih body s1 hlex r1 s2 ⟨he, hevery.2⟩
              cases r1 with
              | none =>
                  simp only [fixClock] at heval
                  exact ih (.loop liveIn body liveOut) _ (lexLtClock hclk) res t
                    ⟨heval, heveryOrig⟩
              | some value =>
                  cases value with
                  | «continue» n =>
                      by_cases hn : n = 0
                      · subst hn
                        simp only [fixClock] at heval
                        exact ih (.loop liveIn body liveOut) _ (lexLtClock hclk) res t
                          ⟨heval, heveryOrig⟩
                      · exact (hi.2 n rfl).elim
                  | «break» n =>
                      by_cases hn : n = 0
                      · subst hn
                        simp only [fixClock] at heval
                        have hb := cutRes_noBC liveOut
                          (step := (none, { s2 with clock :=
                            if s1.clock < s2.clock then s1.clock else s2.clock }))
                          noBC_none
                        rw [heval] at hb
                        exact hb
                      · exact (hi.1 n rfl).elim
                  | _ =>
                      simp only [fixClock] at heval
                      obtain ⟨rfl, rfl⟩ := heval
                      exact exitLoop_noBC hi
        · have hb := cutRes_noBC liveIn (step := (none, s)) noBC_none
          rw [heval] at hb
          exact hb
    | shMem op v ad =>
        rw [evaluate] at heval
        cases hev : eval s ad with
        | none =>
            simp only [hev] at heval
            simp only [Prod.mk.injEq] at heval
            obtain ⟨rfl, rfl⟩ := heval
            simp [noBC]
        | some wl =>
            simp only [hev] at heval
            cases wl with
            | word addr =>
                simp only [] at heval
                by_cases hl : Compiler.Encoders.Asm.asmIsLoad op = true
                · simp only [if_pos hl] at heval
                  cases hsl : sptLookup v s.locals with
                  | none =>
                      simp only [hsl] at heval
                      simp only [Prod.mk.injEq] at heval
                      obtain ⟨rfl, rfl⟩ := heval
                      simp [noBC]
                  | some w =>
                      simp only [hsl] at heval
                      have h := shMemOp_noBC op v addr s
                      rw [heval] at h
                      exact h
                · simp only [if_neg hl] at heval
                  cases hsl : sptLookup v s.locals with
                  | none =>
                      simp only [hsl] at heval
                      simp only [Prod.mk.injEq] at heval
                      obtain ⟨rfl, rfl⟩ := heval
                      simp [noBC]
                  | some w =>
                      cases w with
                      | word _ =>
                          simp only [hsl] at heval
                          have h := shMemOp_noBC op v addr s
                          rw [heval] at h
                          exact h
                      | loc _ _ =>
                          simp only [hsl] at heval
                          simp only [Prod.mk.injEq] at heval
                          obtain ⟨rfl, rfl⟩ := heval
                          simp [noBC]
            | loc _ _ =>
                simp only [] at heval
                simp only [Prod.mk.injEq] at heval
                obtain ⟨rfl, rfl⟩ := heval
                simp [noBC]
    | call returns target arguments handler =>
        rw [evaluate] at heval
        cases hgv : Flapjack.LoopSemStateFiniteExact.getVars arguments s with
        | none =>
            rw [hgv] at heval
            simp only [] at heval
            obtain ⟨rfl, rfl⟩ := heval
            simp
        | some argvals =>
            rw [hgv] at heval
            cases hfc : Flapjack.LoopSemStateFiniteExact.findCode target argvals s.code with
            | none =>
                simp only [hfc] at heval
                obtain ⟨rfl, rfl⟩ := heval
                simp
            | some found =>
                simp only [hfc] at heval
                obtain ⟨env, prog'⟩ := found
                cases returns with
                | none =>
                    simp only [] at heval
                    by_cases hhs : handler.isSome
                    · simp only [if_pos hhs] at heval
                      obtain ⟨rfl, rfl⟩ := heval
                      exact ⟨fun n h => (by cases h), fun n h => (by cases h)⟩
                    · simp only [if_neg hhs] at heval
                      by_cases hz : s.clock = 0
                      · simp only [dif_pos hz] at heval
                        obtain ⟨rfl, rfl⟩ := heval
                        exact ⟨fun n h => (by cases h), fun n h => (by cases h)⟩
                      · simp only [dif_neg hz] at heval
                        split at heval
                        · obtain ⟨rfl, rfl⟩ := heval
                          simp
                        · obtain ⟨rfl, rfl⟩ := heval
                          simp
                        · obtain ⟨rfl, rfl⟩ := heval
                          simp
                        · rename_i hc hb heq
                          obtain ⟨rfl, rfl⟩ := heval
                          exact ⟨fun n h => hb n (Option.some.inj h),
                            fun n h => hc n (Option.some.inj h)⟩
                | some retPair =>
                    obtain ⟨ns, live⟩ := retPair
                    simp only [] at heval
                    by_cases hnd : ¬ ns.Nodup
                    · simp only [if_pos hnd] at heval
                      obtain ⟨rfl, rfl⟩ := heval
                      simp
                    · simp only [if_neg hnd] at heval
                      split at heval
                      · rename_i s1 hcr
                        cases he : evaluate prog' { s1 with locals := env } with
                        | mk r0 st0 =>
                            rw [fix_clock_evaluate] at heval
                            rw [he] at heval
                            have hclock3 := evaluate_clock prog' _ r0 st0 he
                            simp only [] at hclock3
                            cases r0 with
                            | none =>
                                simp only [] at heval
                                obtain ⟨rfl, rfl⟩ := heval
                                simp
                            | some v =>
                                cases v with
                                | «continue» n =>
                                    simp only [] at heval
                                    obtain ⟨rfl, rfl⟩ := heval
                                    simp
                                | «break» n =>
                                    simp only [] at heval
                                    obtain ⟨rfl, rfl⟩ := heval
                                    simp
                                | timeOut =>
                                    simp only [] at heval
                                    obtain ⟨rfl, rfl⟩ := heval
                                    simp
                                | finalFfi e =>
                                    simp only [] at heval
                                    obtain ⟨rfl, rfl⟩ := heval
                                    simp
                                | error =>
                                    simp only [] at heval
                                    obtain ⟨rfl, rfl⟩ := heval
                                    simp
                                | result retvs =>
                                    simp only [] at heval
                                    split at heval
                                    · obtain ⟨rfl, rfl⟩ := heval
                                      simp
                                    · cases handler with
                                      | none =>
                                          simp only [] at heval
                                          obtain ⟨rfl, rfl⟩ := heval
                                          simp
                                      | some spec =>
                                          obtain ⟨hn, hp1, hp2, hlive⟩ := spec
                                          simp only [] at heval
                                          generalize hst : ({ st0 with locals := s1.locals }) = st1
                                            at heval
                                          simp only [everyProgHOL] at hevery
                                          obtain ⟨-, hh1, hh2⟩ := hevery
                                          cases he2 : evaluate hp2 (setVars ns retvs st1) with
                                          | mk r2 st2 =>
                                              have hclock1 := cutRes_none_clock hcr
                                              have hclock2 := evaluate_clock hp2 _ r2 st2 he2
                                              have hsetv : st1.clock = st0.clock := by
                                                rw [← hst]
                                              have hsetv2 :
                                                (setVars ns retvs st1).clock
                                                  = st1.clock := rfl
                                              have hi := ih hp2 (setVars ns retvs st1)
                                                (lexLt (by omega) (by simp +arith)) r2 st2
                                                ⟨he2, hh2⟩
                                              have hstep :
                                                noBC (evaluate hp2 (setVars ns retvs st1)).1 := by
                                                rw [he2]
                                                exact hi
                                              have hcr := cutRes_noBC hlive hstep
                                              rw [he2] at hcr
                                              rw [he2] at heval
                                              rw [heval] at hcr
                                              exact hcr
                                | exception exn =>
                                    simp only [] at heval
                                    cases handler with
                                    | none =>
                                        simp only [] at heval
                                        obtain ⟨rfl, rfl⟩ := heval
                                        simp
                                    | some spec =>
                                        obtain ⟨hn, hp1, hp2, hlive⟩ := spec
                                        simp only [] at heval
                                        generalize hst : ({ st0 with locals := s1.locals }) = st1
                                          at heval
                                        simp only [everyProgHOL] at hevery
                                        obtain ⟨-, hh1, hh2⟩ := hevery
                                        cases he2 : evaluate hp1 (setVar hn exn st1) with
                                        | mk r2 st2 =>
                                            have hclock1 := cutRes_none_clock hcr
                                            have hclock2 := evaluate_clock hp1 _ r2 st2 he2
                                            have hsetv : st1.clock = st0.clock := by
                                              rw [← hst]
                                            have hsetv2 :
                                              (setVar hn exn st1).clock = st1.clock := rfl
                                            have hi := ih hp1 (setVar hn exn st1)
                                              (lexLt (by omega) (by simp +arith)) r2 st2 ⟨he2, hh1⟩
                                            have hstep :
                                              noBC (evaluate hp1 (setVar hn exn st1)).1 := by
                                              rw [he2]
                                              exact hi
                                            have hcr := cutRes_noBC hlive hstep
                                            rw [he2] at hcr
                                            rw [he2] at heval
                                            rw [heval] at hcr
                                            exact hcr
                      · have hb := cutRes_noBC live (step := (none, s)) noBC_none
                        rw [heval] at hb
                        exact hb
    | _ =>
        rw [evaluate] at heval
        try split at heval
        all_goals try split at heval
        all_goals try split at heval
        all_goals try split at heval
        all_goals try split at heval
        all_goals
          obtain ⟨rfl, rfl⟩ := by simpa only [Prod.mk.injEq] using heval
          simp [noBC]
  exact key prog s res t ⟨heval, hevery⟩

end Flapjack
