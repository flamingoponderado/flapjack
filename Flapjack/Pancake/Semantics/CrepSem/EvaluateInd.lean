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
beads `flapjack-2de.1` / `flapjack-2de.1.1`).  Two translation choices must be
reviewed before any `@[hol ... "evaluate_ind" 440]` tag:

* the expression guards use `crepExactEvalExpClassical`, the decider-free
  rendering of the reviewed exact expression evaluator `crepExactEvalExp` with
  the two address predicates instantiated classically, matching HOL `eval`;
* the `Call` clause does not call the reviewed exact `lookupCodeHOL`
  (`CrepSem/LookupCode.lean`, returning a raw `CrepLocalsExact` function) because
  the state's `locals` field is the finite-support `HolFiniteMapExact`; instead
  it spells out the same `lookup_code` computation (`s.code.lookup` plus the
  length/distinctness guards and `HolFiniteMapExact.empty.updateList`), which is
  why the `parameters.length`/`Nodup`/`newlocals` guards appear inline.

The `fix_clock` wrapper is rewritten away as in the HOL line-440 `rewrite`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack-only decider-free wrapper for the exact expression evaluator,
matching HOL `eval`. -/
noncomputable def crepExactEvalExpClassical {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expression : CrepExpHOL width) :
    Option (HolWordLab width) :=
  crepExactEvalExp state (fun a => Classical.propDecidable (state.memaddrs a)) expression

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

/-- Clock bound of the `While` loop-control case split, the clock analogue of
`crepWhileStep_domains`. -/
private theorem evalCrepSemHOLProg_whileClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (condition : CrepExpHOL width) (body : CrepProgHOL width)
    (loopStep : Option (CrepResultHOLExact width) × CrepSemHOLState width σ)
    (hstep : loopStep.2.clock ≤ state.clock)
    (hrec : (evalCrepSemHOLProg (crepStampExactDomains state loopStep.2)
        memDec shMemDec (.while condition body)).2.clock ≤ state.clock) :
    (match _hfixed : loopStep with
     | (none, loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.continue 0), loopState) =>
         evalCrepSemHOLProg (crepStampExactDomains state loopState) memDec shMemDec
           (.while condition body)
     | (some (.break 0), loopState) => (none, loopState)
     | (result, loopState) => (exitLoopCrepResult result, loopState)).2.clock ≤
        state.clock := by
  split <;> (first | exact hrec | exact hstep)

/-- Clock bound of the `Call` callee-result case split, the clock analogue of
`crepCallFixed_domains`. -/
private theorem evalCrepSemHOLProg_callClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fixed : Option (CrepResultHOLExact width) × CrepSemHOLState width σ)
    (hfix : fixed.2.clock ≤ state.clock)
    (hhandler : ∀ (handlerBody : CrepProgHOL width),
        (evalCrepSemHOLProg
          (crepStampExactDomains state { fixed.2 with locals := state.locals })
          memDec shMemDec handlerBody).2.clock ≤ state.clock) :
    (match _hfixed : fixed with
     | (none, bodyState) => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.break _), bodyState) =>
         (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.continue _), bodyState) =>
         (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.return retvs), bodyState) =>
         match returnInfo with
         | none => (some (CrepResultHOLExact.return retvs),
             CrepSemHOLState.emptyLocals bodyState)
         | some (rts, _) =>
             if retvs.length ≠ rts.length then (some CrepResultHOLExact.error, bodyState)
             else match rts.mapM state.locals.lookup with
               | some _ => (none, { bodyState with
                   locals := state.locals.updateListEq
                     (rts.zip retvs) })
               | none => (some CrepResultHOLExact.error, bodyState)
     | (some (CrepResultHOLExact.exception eid), bodyState) =>
         match returnInfo with
         | none =>
             (some (CrepResultHOLExact.exception eid),
               CrepSemHOLState.emptyLocals bodyState)
         | some (_, none) =>
             (some (CrepResultHOLExact.exception eid),
               CrepSemHOLState.emptyLocals bodyState)
         | some (_, some (eid', handlerBody)) =>
             if eid = eid' then
               evalCrepSemHOLProg
                 (crepStampExactDomains state { bodyState with locals := state.locals })
                 memDec shMemDec handlerBody
             else (some (CrepResultHOLExact.exception eid),
               CrepSemHOLState.emptyLocals bodyState)
     | (some result, bodyState) =>
         (some result, CrepSemHOLState.emptyLocals bodyState)).2.clock ≤
        state.clock := by
  split
  · exact hfix
  · exact hfix
  · exact hfix
  · split
    · simpa [CrepSemHOLState.emptyLocals] using hfix
    · split
      · exact hfix
      · split <;> exact hfix
  · split
    · simpa [CrepSemHOLState.emptyLocals] using hfix
    · simpa [CrepSemHOLState.emptyLocals] using hfix
    · split
      · exact hhandler _
      · simpa [CrepSemHOLState.emptyLocals] using hfix
  · simpa [CrepSemHOLState.emptyLocals] using hfix

/-- HOL `evaluate_clock` (`crepSemScript.sml:421-431`) over the exact
evaluator core: the result clock never exceeds the input clock. -/
theorem evalCrepSemHOLProg_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (program : CrepProgHOL width) :
    (evalCrepSemHOLProg state memDec shMemDec program).2.clock ≤ state.clock := by
  have hmain : ∀ (c : Nat) (state : CrepSemHOLState width σ), state.clock ≤ c →
      ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
        (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
        (program : CrepProgHOL width),
        (evalCrepSemHOLProg state memDec shMemDec program).2.clock ≤ state.clock := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ihClock =>
      intro state hclk memDec shMemDec program
      have inner : ∀ (n : Nat) (program : CrepProgHOL width), sizeOf program ≤ n →
          ∀ (state : CrepSemHOLState width σ), state.clock ≤ c →
          ∀ (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
            (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a)),
            (evalCrepSemHOLProg state memDec shMemDec program).2.clock ≤ state.clock := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihSize =>
          intro program hsize state hclk memDec shMemDec
          cases program with
          | skip => simp [evalCrepSemHOLProg_skip]
          | dec name value body =>
              have hsub : sizeOf body < n := by
                have h1 : sizeOf body < sizeOf (CrepProgHOL.dec name value body) := by
                  decreasing_trivial
                omega
              have ihBody := ihSize (sizeOf body) hsub body (by omega)
              rw [evalCrepSemHOLProg_dec]
              split
              · simp
              · rename_i v _
                dsimp only
                have hb := ihBody (CrepSemHOLState.setVar name v state)
                  (by simp only [CrepSemHOLState.setVar]; exact hclk) memDec shMemDec
                simpa [CrepSemHOLState.setVar] using hb
          | assign name src =>
              rw [evalCrepSemHOLProg_assign]
              split <;> (try split) <;> simp [CrepSemHOLState.setVar]
          | primitive names operator args =>
              rw [evalCrepSemHOLProg_primitive]
              split <;> (try split) <;> (try split) <;> simp
          | store dst src =>
              rw [evalCrepSemHOLProg_store]
              split <;> (try split) <;> (try split) <;> simp
          | store32 dst src =>
              rw [evalCrepSemHOLProg_store32]
              split <;> (try split) <;> (try split) <;> simp
          | storeByte dst src =>
              rw [evalCrepSemHOLProg_storeByte]
              split <;> (try split) <;> (try split) <;> simp
          | storeGlob dst src =>
              rw [evalCrepSemHOLProg_storeGlob]
              split <;> (try split) <;> simp [CrepSemHOLState.setGlobals]
          | seq first second =>
              have hsubS : sizeOf second < n := by
                have h1 : sizeOf second < sizeOf (CrepProgHOL.seq first second) := by
                  decreasing_trivial
                omega
              have ihSecond := ihSize (sizeOf second) hsubS second (by omega)
              simp only [evalCrepSemHOLProg_seq]
              split
              · rename_i stepState hstep
                have hclkStep : stepState.clock ≤ state.clock :=
                  fixClockCrepSemHOL_IMP_LESS_EQ state
                    (evalCrepSemHOLProg state memDec shMemDec first) none stepState
                    (by simpa using hstep)
                have hb := ihSecond (crepStampExactDomains state stepState)
                  (Nat.le_trans hclkStep hclk) memDec shMemDec
                exact Nat.le_trans hb hclkStep
              · rename_i res stepState hstep
                rw [hstep]
                exact fixClockCrepSemHOL_IMP_LESS_EQ state
                  (evalCrepSemHOLProg state memDec shMemDec first) (some res) stepState hstep
          | ite condition thenBranch elseBranch =>
              have hsubT : sizeOf thenBranch < n := by
                have h1 : sizeOf thenBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have hsubE : sizeOf elseBranch < n := by
                have h1 : sizeOf elseBranch <
                    sizeOf (CrepProgHOL.ite condition thenBranch elseBranch) := by
                  decreasing_trivial
                omega
              have ihThen := ihSize (sizeOf thenBranch) hsubT thenBranch (by omega)
              have ihElse := ihSize (sizeOf elseBranch) hsubE elseBranch (by omega)
              rw [evalCrepSemHOLProg_ite]
              split
              · rename_i w _
                split
                · exact ihThen state hclk memDec shMemDec
                · exact ihElse state hclk memDec shMemDec
              · simp
          | «while» condition body =>
              rw [evalCrepSemHOLProg_while]
              split
              · rename_i w _
                split
                · split
                  · simp [CrepSemHOLState.emptyLocals]
                  · dsimp only
                    refine evalCrepSemHOLProg_whileClock state memDec shMemDec condition body
                      (fixClockCrepSemHOL (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body))
                      ?_ ?_
                    · have hb := fixClockCrepSemHOL_IMP_LESS_EQ (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body)
                        _ _ rfl
                      exact Nat.le_trans hb (Nat.sub_le _ _)
                    · have hb := fixClockCrepSemHOL_IMP_LESS_EQ (decClockCrepSemHOL state)
                        (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec shMemDec body)
                        _ _ rfl
                      have hlt : (crepStampExactDomains state
                            (fixClockCrepSemHOL (decClockCrepSemHOL state)
                              (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec
                                shMemDec body)).2).clock < state.clock := by
                        have hd : (decClockCrepSemHOL state).clock < state.clock := by
                          simp only [decClockCrepSemHOL]; omega
                        exact Nat.lt_of_le_of_lt hb hd
                      have hm : (crepStampExactDomains state
                            (fixClockCrepSemHOL (decClockCrepSemHOL state)
                              (evalCrepSemHOLProg (decClockCrepSemHOL state) memDec
                                shMemDec body)).2).clock < c :=
                        Nat.lt_of_lt_of_le hlt hclk
                      have hrec := ihClock _ hm _
                        (Nat.le_of_eq rfl) memDec shMemDec (.while condition body)
                      exact Nat.le_trans hrec (Nat.le_of_lt hlt)
                · simp
              · simp
          | «break» label => simp [evalCrepSemHOLProg_break]
          | «continue» label => simp [evalCrepSemHOLProg_continue]
          | call =>
              rename_i rin fn ar
              rw [evalCrepSemHOLProg_call]
              split
              · simp
              · rename_i values _
                split
                · simp
                · rename_i parameters body _
                  split
                  · dsimp only
                    let callee : CrepSemHOLState width σ :=
                      { state with locals :=
                          HolFiniteMapExact.empty.updateList (parameters.zip values) }
                    let decCallee : CrepSemHOLState width σ := decClockCrepSemHOL callee
                    let bodyResult : Option (CrepResultHOLExact width) ×
                        CrepSemHOLState width σ :=
                      evalCrepSemHOLProg decCallee memDec shMemDec body
                    let fixed : Option (CrepResultHOLExact width) ×
                        CrepSemHOLState width σ :=
                      fixClockCrepSemHOL decCallee bodyResult
                    have hfix : fixed.2.clock ≤ state.clock := by
                      have hb := fixClockCrepSemHOL_IMP_LESS_EQ decCallee bodyResult _ _ rfl
                      have hd : decCallee.clock ≤ state.clock := by
                        simp only [decCallee, callee, decClockCrepSemHOL]
                        exact Nat.sub_le _ _
                      exact Nat.le_trans hb hd
                    have hhandler : state.clock ≠ 0 → ∀ handlerBody,
                        (evalCrepSemHOLProg
                          (crepStampExactDomains state
                            { fixed.2 with locals := state.locals })
                          memDec shMemDec handlerBody).2.clock ≤ state.clock := by
                      intro hclock handlerBody
                      have hlt : (crepStampExactDomains state
                            { fixed.2 with locals := state.locals }).clock < state.clock := by
                        have hb := fixClockCrepSemHOL_IMP_LESS_EQ decCallee bodyResult _ _ rfl
                        have hd : decCallee.clock < state.clock := by
                          simp only [decCallee, callee, decClockCrepSemHOL]
                          omega
                        exact Nat.lt_of_le_of_lt hb hd
                      have hm : (crepStampExactDomains state
                            { fixed.2 with locals := state.locals }).clock < c :=
                        Nat.lt_of_lt_of_le hlt hclk
                      have hrec := ihClock _ hm _
                        (Nat.le_of_eq rfl) memDec shMemDec handlerBody
                      exact Nat.le_trans hrec (Nat.le_of_lt hlt)
                    split
                    · rename_i rts snd
                      split
                      · dsimp only
                        split
                        · simp [CrepSemHOLState.emptyLocals]
                        · rename_i hclock
                          exact evalCrepSemHOLProg_callClock state memDec shMemDec
                            (some (rts, snd)) fixed hfix (hhandler hclock)
                      · simp
                    · dsimp only
                      split
                      · simp [CrepSemHOLState.emptyLocals]
                      · rename_i hclock
                        exact evalCrepSemHOLProg_callClock state memDec shMemDec
                          none fixed hfix (hhandler hclock)
                  · simp
          | extCall function configuration configurationLength array arrayLength =>
              rw [evalCrepSemHOLProg_extCall]
              split <;> (try split) <;> (try split) <;> (try split) <;>
                (try split) <;> (try split) <;> simp
          | «raise» exception =>
              simp [evalCrepSemHOLProg_raise, CrepSemHOLState.emptyLocals]
          | «return» values =>
              rw [evalCrepSemHOLProg_return]
              split <;> simp [CrepSemHOLState.emptyLocals]
          | shMem operator name address =>
              rw [evalCrepSemHOLProg_shMem]
              split
              · rename_i addressValue _
                split
                · split
                  · have hclk : (crepShMemLoadHOL operator name addressValue state
                        shMemDec).2.clock = state.clock := by
                      unfold crepShMemLoadHOL
                      exact @crepShMemLoadClock width ‹NeZero width› σ name addressValue
                        (crepShMemByteWidth operator) state shMemDec
                        (crepShMemLoadExactHOL name addressValue
                          (crepShMemByteWidth operator) state).1
                        (crepShMemLoadExactHOL name addressValue
                          (crepShMemByteWidth operator) state).2
                        (Prod.ext rfl rfl)
                    exact Nat.le_of_eq hclk
                  · simp
                · split
                  · have hclk : (crepShMemStoreHOL operator name addressValue state
                        shMemDec).2.clock = state.clock := by
                      unfold crepShMemStoreHOL
                      exact @crepShMemStoreClock width ‹NeZero width› σ name addressValue
                        (crepShMemByteWidth operator) state shMemDec
                        (crepShMemStoreExactHOL name addressValue
                          (crepShMemByteWidth operator) state).1
                        (crepShMemStoreExactHOL name addressValue
                          (crepShMemByteWidth operator) state).2
                        (Prod.ext rfl rfl)
                    exact Nat.le_of_eq hclk
                  · simp
              · simp
          | tick =>
              rw [evalCrepSemHOLProg_tick]
              split <;> simp [decClockCrepSemHOL, CrepSemHOLState.emptyLocals]
      exact inner (sizeOf program) program (by omega) state hclk memDec shMemDec
  exact hmain state.clock state (by omega) memDec shMemDec program

/-- HOL `evaluate_clock` over the exact evaluator. -/
theorem evalCrepSemHOLProgExact_clock_le {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (program : CrepProgHOL width) :
    (evalCrepSemHOLProgExact state program).2.clock ≤ state.clock := by
  rw [evalCrepSemHOLProgExact_eq_core state program
      (fun a => Classical.propDecidable (state.memaddrs a))
      (fun a => Classical.propDecidable (state.shMemaddrs a))]
  exact evalCrepSemHOLProg_clock_le state _ _ program

/-- The exact clause-for-clause Lean statement of HOL `crepSem$evaluate_ind`
(`cakeml/pancake/semantics/crepSemScript.sml:440`,
`REWRITE_RULE [fix_clock_evaluate] evaluate_ind`), reconstructed over the exact
carriers `CrepProgHOL`, `CrepSemHOLState`, and `CrepResultHOLExact`.  The
`Call` clauses use the `lookup_code` branch structure unfolded as the evaluator
executes it (`s.code.lookup` plus the length/distinctness guards and the
`FUPDATE_LIST FEMPTY` local map), so the recursive local map has the exact
`HolFiniteMapExact` carrier of the state.  `fix_clock` has been rewritten away
(`evaluate_clock` is `evalCrepSemHOLProgExact_clock_le`). -/
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
        (∀ args parameters body newlocals eval_prog v4 st v7 eid v v1 v2 v3 eid' p,
          argexps.mapM (crepExactEvalExpClassical s) = some args →
          s.code.lookup fname = some (parameters, body) →
          parameters.length = args.length →
          parameters.Nodup →
          newlocals = HolFiniteMapExact.empty.updateList (parameters.zip args) →
          (¬ (match caltyp with
              | none => False
              | some (rts, _) => ¬ rts.Nodup)) →
          s.clock ≠ 0 →
          eval_prog = evalCrepSemHOLProgExact
            { decClockCrepSemHOL s with locals := newlocals } body →
          eval_prog = (v4, st) →
          v4 = some v7 → v7 = .exception eid →
          caltyp = some v → v = (v1, v2) → v2 = some v3 → v3 = (eid', p) →
          eid = eid' →
          P (p, { st with locals := s.locals })) →
        (∀ args parameters body newlocals,
          argexps.mapM (crepExactEvalExpClassical s) = some args →
          s.code.lookup fname = some (parameters, body) →
          parameters.length = args.length →
          parameters.Nodup →
          newlocals = HolFiniteMapExact.empty.updateList (parameters.zip args) →
          (¬ (match caltyp with
              | none => False
              | some (rts, _) => ¬ rts.Nodup)) →
          s.clock ≠ 0 →
          P (body, { decClockCrepSemHOL s with locals := newlocals })) →
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
      · intro args parameters body newlocals eval_prog v4 st v7 eid v v1 v2 v3 eid' p
          _ _ _ _ _ _ hclock heval1 heval2 _ _ _ _ _ _ _
        have hclk : st.clock < state.clock := by
          have h := evalCrepSemHOLProgExact_clock_le
            { decClockCrepSemHOL state with locals := newlocals } body
          rw [heval1.symm] at h
          rw [heval2] at h
          have hd : ({ decClockCrepSemHOL state with locals := newlocals }).clock <
              state.clock := by
            simp only [decClockCrepSemHOL]; omega
          have hst : st.clock ≤ ({ decClockCrepSemHOL state with locals := newlocals }).clock := by
            simpa using h
          omega
        exact ih p { st with locals := state.locals } (hlexClock hclk)
      · intro args parameters body newlocals _ _ _ _ _ _ hclock
        exact ih body { decClockCrepSemHOL state with locals := newlocals }
          (hlexClock (by simp only [decClockCrepSemHOL]; omega))

end Flapjack
