import Flapjack.Pancake.Semantics.PanSem.TotalEvalCallBridge

/-!
# Reachable rangedness of the production total panSem evaluator

The production/exact `Call` and `DecCall` agreements
(`TotalEvalCallBridge.lean`) take the callee post-state rangedness and the
result-payload rangedness (`PanSemHOLResultRanged`) as an explicit premise
`hcallee`, and the looked-up code entry rangedness as `hcode`.  This module
proves both are reachable invariants of `panSemTotalEvaluate`:

* `panSemTotalEvaluate_code` — the evaluator never writes `code` (frame lemma,
  following `panSemTotalEvaluate_exceptionShapes`);
* `panSemTotalEvaluate_ranged` — for a `ProgByteRanged` program, a
  `PanSemStateRelExecRanged` state and a `PanPrimitiveHandlerByteRanged`
  primitive handler, where every code entry is `PanLangEntryByteRanged`, the
  result state is again ranged and the result payload is
  `PanSemHOLResultRanged`;
* `panSemTotalEvaluateCake_ranged` — the same for the canonical entrypoint, whose
  handler premise is `panPrimopHOL_byteRanged`;
* `panSemTotalEvaluate_call_agree_of_ranged` / `_decCall_agree_of_ranged` — the
  `Call`/`DecCall` agreements with `hcode`/`hcallee` discharged (instantiate
  `primitive := panPrimopHOL`, `hprim := panPrimopHOL_byteRanged` for the
  canonical entrypoint).

The remaining top-level obligation is `PanSemCodeRanged` of the compiled
initial state.

Everything here is untagged Flapjack-specific bridge infrastructure
(`flapjack-pxn.18.4.3.77.2.15.4`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

section CodeFrame

variable {σ : Type}

/-- The clock-leaf clauses leave `code` unchanged. -/
theorem panSemEvaluateClockLeaf_code
    (leaf : PanSemClockLeaf) (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemEvaluateClockLeaf leaf state).2.code = state.code := by
  cases leaf <;> simp only [panSemEvaluateClockLeaf] <;> repeat' (first | rfl | split)

/-- The `Assign` clause leaves `code` unchanged. -/
theorem panSemTotalAssignClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (value : Exp (RiscV.Word 64)) :
    (panSemTotalAssignClause state kind name value).2.code = state.code := by
  simp only [panSemTotalAssignClause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `Raise` clause leaves `code` unchanged (it only reads them). -/
theorem panSemTotalRaiseClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exceptionId : ExceptionId) (expression : Exp (RiscV.Word 64)) :
    (panSemTotalRaiseClause state exceptionId expression).2.code = state.code := by
  simp only [panSemTotalRaiseClause, panSemTotalExprStep, panEmptyLocals]
  repeat' (first | rfl | split)

/-- The `Return` clause leaves `code` unchanged. -/
theorem panSemTotalReturnClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) :
    (panSemTotalReturnClause state expression).2.code = state.code := by
  simp only [panSemTotalReturnClause, panSemTotalExprStep, panEmptyLocals]
  repeat' (first | rfl | split)

/-- The `Primitive` clause leaves `code` unchanged. -/
theorem panSemTotalPrimitiveClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp) (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    (panSemTotalPrimitiveClause state name operator arguments primitive).2.code = state.code := by
  simp only [panSemTotalPrimitiveClause, panSemTotalExprListStep]
  repeat' (first | rfl | split)

/-- The `Store` clause leaves `code` unchanged. -/
theorem panSemTotalStoreClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause state address value).2.code = state.code := by
  simp only [panSemTotalStoreClause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `Store32` clause leaves `code` unchanged. -/
theorem panSemTotalStore32Clause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStore32Clause state address value).2.code = state.code := by
  simp only [panSemTotalStore32Clause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `StoreByte` clause leaves `code` unchanged. -/
theorem panSemTotalStoreByteClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreByteClause state address value).2.code = state.code := by
  simp only [panSemTotalStoreByteClause, panSemTotalExprStep]
  repeat' (first | rfl | split)

/-- The `ExtCall` clause leaves `code` unchanged. -/
theorem panSemTotalExtCallClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : FunName) (configuration configurationLength array arrayLength : Exp (RiscV.Word 64)) :
    (panSemTotalExtCallClause state function configuration configurationLength array arrayLength).2.code = state.code := by
  simp only [panSemTotalExtCallClause, panSemTotalExprStep, panSemTotalExtCallStep,
    panSemTotalMachineReadBytes, panSemTotalMachineWriteBytes, panEmptyLocals]
  repeat' (first | rfl | split)

/-- The `ShMemLoad` clause leaves `code` unchanged. -/
theorem panSemTotalShMemLoadClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp (RiscV.Word 64)) :
    (panSemTotalShMemLoadClause state size kind name address).2.code = state.code := by
  simp only [panSemTotalShMemLoadClause, panSemTotalExprStep, panSemTotalShMemState,
    panSemTotalShMemStateBack, panSemTotalShMemLoadResult]
  repeat' (first | rfl | split)

/-- The `ShMemStore` clause leaves `code` unchanged. -/
theorem panSemTotalShMemStoreClause_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (size : OpSize) (address value : Exp (RiscV.Word 64)) :
    (panSemTotalShMemStoreClause state size address value).2.code = state.code := by
  simp only [panSemTotalShMemStoreClause, panSemTotalExprStep, panSemTotalShMemState,
    panSemTotalShMemStateBack, panSemTotalShMemStoreResult]
  repeat' (first | rfl | split)

theorem panSemTotalDecBind_code [BEq String]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (value : PanValue (RiscV.Word 64)) :
    (panSemTotalDecBind state name value).code = state.code := by
  simp [panSemTotalDecBind]

theorem panSemFixClock_code (entryClock : Nat)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemFixClock entryClock state).code = state.code := rfl

/-- `panEmptyLocals` only clears locals, so it leaves `code` unchanged. -/
theorem panEmptyLocals_code
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panEmptyLocals state).code = state.code := rfl

/-- **Frame lemma.** The production total evaluator never writes
    `code`: its result state stores exactly the entry state's
    code map.  Proved by well-founded induction over `panSemEvalMeasure`,
    using the per-clause frame lemmas above for the non-recursive clauses and
    the induction hypothesis for the recursive `Dec`/`Seq`/`If`/`While`/`Call`/
    `DecCall` clauses. -/
theorem panSemTotalEvaluate_code {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    ∀ (prog : Prog (RiscV.Word 64)) (state : PanSemState (RiscV.Word 64) (FfiState σ)),
      (panSemTotalEvaluate primitive prog state).2.code = state.code := by
  intro prog state
  have hwf : WellFounded (@panSemEvalMeasureRel (RiscV.Word 64) (FfiState σ)) :=
    panSemEvalMeasureRel_wf
  let motive : PanSemState (RiscV.Word 64) (FfiState σ) × Prog (RiscV.Word 64) → Prop :=
    fun p => (panSemTotalEvaluate primitive p.2 p.1).2.code = p.1.code
  have hmain : ∀ p, motive p := by
    intro p
    refine WellFounded.induction hwf p ?_
    intro p ih
    obtain ⟨state, prog⟩ := p
    change (panSemTotalEvaluate primitive prog state).2.code = state.code
    cases prog with
    | skip => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_code .skip state
    | «break» => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_code .break state
    | «continue» => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_code .continue state
    | tick => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_code .tick state
    | assign kind name value => rw [panSemTotalEvaluate]; exact panSemTotalAssignClause_code state kind name value
    | primitive name operator arguments => rw [panSemTotalEvaluate]; exact panSemTotalPrimitiveClause_code state name operator arguments primitive
    | store address value => rw [panSemTotalEvaluate]; exact panSemTotalStoreClause_code state address value
    | store32 address value => rw [panSemTotalEvaluate]; exact panSemTotalStore32Clause_code state address value
    | storeByte address value => rw [panSemTotalEvaluate]; exact panSemTotalStoreByteClause_code state address value
    | raise exceptionId expression => rw [panSemTotalEvaluate]; exact panSemTotalRaiseClause_code state exceptionId expression
    | «return» expression => rw [panSemTotalEvaluate]; exact panSemTotalReturnClause_code state expression
    | annot tag text => rw [panSemTotalEvaluate]
    | dec name shape value body =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases heval : evalPanSemStateExp state value with
        | none => rfl
        | some evaluated =>
            simp only []
            cases hmatch : panShapeMatches shape (panSemShapeOf evaluated) with
            | false => rfl
            | true =>
                simp only [if_true]
                try dsimp only
                rw [ih (panSemTotalDecBind state name evaluated, body)
                  (panSemEvalMeasureRel_decBody state name shape value body)]
                rw [panSemTotalDecBind_code]
    | seq first second =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hres : (panSemTotalEvaluate primitive first state).1 with
        | none =>
            have ih1 := ih (state, first)
              (panSemEvalMeasureRel_seq_branch state state first second first (Nat.le_refl _) (Or.inl rfl))
            have hclk : (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2).clock ≤ state.clock :=
              panSemFixClock_clock_le _ _
            have ih2 := ih (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2, second)
              (panSemEvalMeasureRel_seq_branch _ state first second second hclk (Or.inr rfl))
            rw [ih2, panSemFixClock_code, ih1]
        | some result =>
            have ih1 := ih (state, first)
              (panSemEvalMeasureRel_seq_branch state state first second first (Nat.le_refl _) (Or.inl rfl))
            rw [panSemFixClock_code, ih1]
    | ite condition thenBranch elseBranch =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hcond : evalPanSemStateExp state condition with
        | none => rfl
        | some v =>
            cases v with
            | word w =>
                try dsimp only
                split
                · exact ih (state, elseBranch)
                    (panSemEvalMeasureRel_ite_branch state condition thenBranch elseBranch elseBranch (Or.inr rfl))
                · exact ih (state, thenBranch)
                    (panSemEvalMeasureRel_ite_branch state condition thenBranch elseBranch thenBranch (Or.inl rfl))
            | rStruct fs => rfl
            | nStruct nm flds => rfl
    | «while» condition body =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hcond : evalPanSemStateExp state condition with
        | none => rfl
        | some v =>
            cases v with
            | word w =>
                try dsimp only
                split
                · rfl
                · split
                  · exact panEmptyLocals_code state
                  · rename_i hw hclk
                    try dsimp only
                    have hdecClock : state.clock - 1 < state.clock := by omega
                    have ihBody := ih ({ state with clock := state.clock - 1 }, body)
                      (panSemEvalMeasureRel_of_clock_lt hdecClock)
                    have hfixLt : (panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2).clock < state.clock := by
                      have := panSemFixClock_clock_le (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2
                      omega
                    have ihLoop := ih ((panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2),
                        .while condition body)
                      (panSemEvalMeasureRel_of_clock_lt hfixLt)
                    cases hbody : (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).1 with
                    | none => rw [ihLoop, panSemFixClock_code, ihBody]
                    | some r =>
                        cases r with
                        | «continue» => rw [ihLoop, panSemFixClock_code, ihBody]
                        | «break» => rw [panSemFixClock_code, ihBody]
                        | error => rw [panSemFixClock_code, ihBody]
                        | timeOut => rw [panSemFixClock_code, ihBody]
                        | returned val => rw [panSemFixClock_code, ihBody]
                        | exception eid val => rw [panSemFixClock_code, ihBody]
                        | finalFfi ev => rw [panSemFixClock_code, ihBody]
            | rStruct fs => rfl
            | nStruct nm flds => rfl
    | call info function arguments =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hexps : evalPanSemStateExps state arguments with
        | none => rfl
        | some values =>
            simp only []
            cases hlookup : panSemTotalCodeLookup state function values with
            | none => rfl
            | some triple =>
                obtain ⟨callee, newLocals, returnShape⟩ := triple
                simp only []
                split
                · exact panEmptyLocals_code state
                · rename_i hclk
                  have hdecClock : state.clock - 1 < state.clock := by omega
                  have ihBody := ih ({ state with clock := state.clock - 1, locals := newLocals }, callee)
                    (panSemEvalMeasureRel_of_clock_lt hdecClock)
                  have hbodyExc : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).2.code =
                      state.code := by
                    rw [ihBody]
                  have hfixedExc : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).code =
                      state.code := by
                    rw [panSemFixClock_code, hbodyExc]
                  have hfixedClock : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).clock <
                      state.clock := by
                    have hle := panSemFixClock_clock_le (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2
                    omega
                  cases hcall : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).1 with
                  | none => try dsimp only; exact hfixedExc
                  | some r =>
                      cases r with
                      | error => try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
                      | timeOut => try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
                      | finalFfi ev => try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
                      | «break» => try dsimp only; exact hfixedExc
                      | «continue» => try dsimp only; exact hfixedExc
                      | returned value =>
                          try dsimp only
                          split
                          · try dsimp only
                            split
                            · rw [panEmptyLocals_code]; exact hfixedExc
                            · try dsimp only; exact hfixedExc
                            · try dsimp only
                              split
                              · split
                                · try dsimp only; exact hfixedExc
                                · try dsimp only; exact hfixedExc
                              · try dsimp only; exact hfixedExc
                          · try dsimp only; exact hfixedExc
                      | exception exceptionId value =>
                          try dsimp only
                          split
                          · rw [panEmptyLocals_code]; exact hfixedExc
                          · try dsimp only; exact hfixedExc
                          · try dsimp only
                            rename_i handlerId handlerVar handlerProg
                            split
                            · split
                              · split
                                · try dsimp only
                                  have ihHandler := ih
                                    ({ panSemFixClock (state.clock - 1)
                                        (panSemTotalEvaluate primitive callee
                                          ({ state with clock := state.clock - 1, locals := newLocals })).2 with
                                      locals := updatePanValueMap state.locals handlerVar value }, handlerProg)
                                    (panSemEvalMeasureRel_of_clock_lt (by
                                      have hle := panSemFixClock_clock_le (state.clock - 1)
                                        (panSemTotalEvaluate primitive callee
                                          ({ state with clock := state.clock - 1, locals := newLocals })).2
                                      omega))
                                  rw [ihHandler, hfixedExc]
                                · try dsimp only; exact hfixedExc
                              · try dsimp only; exact hfixedExc
                            · rw [panEmptyLocals_code]; exact hfixedExc
    | decCall name shape function arguments continuation =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hexps : evalPanSemStateExps state arguments with
        | none => rfl
        | some values =>
            simp only []
            cases hlookup : panSemTotalCodeLookup state function values with
            | none => rfl
            | some triple =>
                obtain ⟨callee, newLocals, returnShape⟩ := triple
                simp only []
                split
                · exact panEmptyLocals_code state
                · rename_i hclk
                  have hdecClock : state.clock - 1 < state.clock := by omega
                  have ihBody := ih ({ state with clock := state.clock - 1, locals := newLocals }, callee)
                    (panSemEvalMeasureRel_of_clock_lt hdecClock)
                  have hbodyExc : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).2.code =
                      state.code := by
                    rw [ihBody]
                  have hfixedExc : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).code =
                      state.code := by
                    rw [panSemFixClock_code, hbodyExc]
                  have hfixedClock : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).clock <
                      state.clock := by
                    have hle := panSemFixClock_clock_le (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2
                    omega
                  cases hcall : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).1 with
                  | none => try dsimp only; exact hfixedExc
                  | some r =>
                      cases r with
                      | error => try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
                      | timeOut => try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
                      | finalFfi ev => try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
                      | «break» => try dsimp only; exact hfixedExc
                      | «continue» => try dsimp only; exact hfixedExc
                      | returned value =>
                          try dsimp only
                          split
                          · try dsimp only
                            have ihCont := ih
                              ({ panSemFixClock (state.clock - 1)
                                  (panSemTotalEvaluate primitive callee
                                    ({ state with clock := state.clock - 1, locals := newLocals })).2 with
                                locals := updatePanValueMap state.locals name value }, continuation)
                              (panSemEvalMeasureRel_of_clock_lt (by
                                have hle := panSemFixClock_clock_le (state.clock - 1)
                                  (panSemTotalEvaluate primitive callee
                                    ({ state with clock := state.clock - 1, locals := newLocals })).2
                                omega))
                            have hcontExc : (panSemTotalEvaluate primitive continuation
                                ({ panSemFixClock (state.clock - 1)
                                    (panSemTotalEvaluate primitive callee
                                      ({ state with clock := state.clock - 1, locals := newLocals })).2 with
                                  locals := updatePanValueMap state.locals name value })).2.code =
                                state.code := by
                              rw [ihCont]
                              exact hfixedExc
                            try dsimp only
                            rw [hcontExc]
                          · try dsimp only; exact hfixedExc
                      | exception eid val =>
                          try dsimp only; rw [panEmptyLocals_code]; exact hfixedExc
    | extCall function configuration configurationLength array arrayLength =>
        rw [panSemTotalEvaluate]
        exact panSemTotalExtCallClause_code state function configuration configurationLength array arrayLength
    | shMemLoad size kind name address =>
        rw [panSemTotalEvaluate]
        exact panSemTotalShMemLoadClause_code state size kind name address
    | shMemStore size address value =>
        rw [panSemTotalEvaluate]
        exact panSemTotalShMemStoreClause_code state size address value
  exact hmain (state, prog)


end CodeFrame


section Ranged

variable {σ : Type}

/-- Every production code entry is byte-ranged. -/
def PanSemCodeRanged (state : PanSemState (RiscV.Word 64) (FfiState σ)) : Prop :=
  ∀ name entry, panSemCodeLookup state.code name = some entry → PanLangEntryByteRanged entry

/-- A production evaluator output whose state is ranged and whose result payload
    is byte-ranged. -/
abbrev PanSemRangedOutput
    (output : Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ)) : Prop :=
  PanSemStateRelExecRanged output.2 ∧ PanSemHOLResultRanged output.1

theorem PanSemRangedOutput.error {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) : PanSemRangedOutput (some .error, state) :=
  ⟨h, trivial⟩

theorem PanSemRangedOutput.exprStep {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (expression : Exp (RiscV.Word 64))
    (onValue : PanValue (RiscV.Word 64) →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ))
    (honValue : ∀ value, evalPanSemStateExp state expression = some value →
      PanSemRangedOutput (onValue value)) :
    PanSemRangedOutput (panSemTotalExprStep state expression onValue) := by
  unfold panSemTotalExprStep
  cases hv : evalPanSemStateExp state expression with
  | none => exact PanSemRangedOutput.error h
  | some value => exact honValue value hv

theorem panSemEvaluateClockLeaf_rangedOutput (leaf : PanSemClockLeaf)
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state) :
    PanSemRangedOutput (panSemEvaluateClockLeaf leaf state) := by
  cases leaf <;> simp only [panSemEvaluateClockLeaf]
  · exact ⟨h, trivial⟩
  · exact ⟨h, trivial⟩
  · exact ⟨h, trivial⟩
  · split
    · exact ⟨h.panEmptyLocals, trivial⟩
    · exact ⟨h.setClock _, trivial⟩

theorem panSemTotalAssignClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (kind : VarKind) (name : VarName) (expression : Exp (RiscV.Word 64))
    (he : ExpByteRanged expression) :
    PanSemRangedOutput (panSemTotalAssignClause state kind name expression) := by
  unfold panSemTotalAssignClause
  refine PanSemRangedOutput.exprStep h _ _ (fun value hv => ?_)
  have hvR := evalPanSemStateExp_byteRanged state h expression he value hv
  split
  · cases kind
    · exact ⟨h.updateLocals name value hvR, trivial⟩
    · exact ⟨h.updateGlobals name value hvR, trivial⟩
  · exact PanSemRangedOutput.error h

theorem panSemTotalPrimitiveClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (name : VarName) (operator : PrimOp) (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprim : PanPrimitiveHandlerByteRanged primitive) :
    PanSemRangedOutput (panSemTotalPrimitiveClause state name operator arguments primitive) := by
  refine ⟨h.primitiveClause name operator arguments primitive hprim, ?_⟩
  unfold panSemTotalPrimitiveClause panSemTotalExprListStep
  split
  · dsimp only
    repeat' (first | trivial | split)
  · trivial

theorem panSemTotalStoreClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (address value : Exp (RiscV.Word 64)) :
    PanSemRangedOutput (panSemTotalStoreClause state address value) := by
  unfold panSemTotalStoreClause
  refine PanSemRangedOutput.exprStep h _ _ (fun a _ => ?_)
  split
  · refine PanSemRangedOutput.exprStep h _ _ (fun v _ => ?_)
    split
    · exact ⟨h.of_fields rfl rfl rfl, trivial⟩
    · exact PanSemRangedOutput.error h
  · exact PanSemRangedOutput.error h

theorem panSemTotalStore32Clause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (address value : Exp (RiscV.Word 64)) :
    PanSemRangedOutput (panSemTotalStore32Clause state address value) := by
  unfold panSemTotalStore32Clause
  refine PanSemRangedOutput.exprStep h _ _ (fun a _ => ?_)
  split
  · refine PanSemRangedOutput.exprStep h _ _ (fun v _ => ?_)
    repeat' (first | exact ⟨h.of_fields rfl rfl rfl, trivial⟩ | exact PanSemRangedOutput.error h | split)
  · exact PanSemRangedOutput.error h

theorem panSemTotalStoreByteClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (address value : Exp (RiscV.Word 64)) :
    PanSemRangedOutput (panSemTotalStoreByteClause state address value) := by
  unfold panSemTotalStoreByteClause
  refine PanSemRangedOutput.exprStep h _ _ (fun a _ => ?_)
  split
  · refine PanSemRangedOutput.exprStep h _ _ (fun v _ => ?_)
    repeat' (first | exact ⟨h.of_fields rfl rfl rfl, trivial⟩ | exact PanSemRangedOutput.error h | split)
  · exact PanSemRangedOutput.error h

theorem panSemTotalRaiseClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (exceptionId : ExceptionId) (hid : NameRanged exceptionId)
    (expression : Exp (RiscV.Word 64)) (he : ExpByteRanged expression) :
    PanSemRangedOutput (panSemTotalRaiseClause state exceptionId expression) := by
  unfold panSemTotalRaiseClause
  refine PanSemRangedOutput.exprStep h _ _ (fun value hv => ?_)
  have hvR := evalPanSemStateExp_byteRanged state h expression he value hv
  split
  · split
    · exact ⟨h.panEmptyLocals, hid, hvR⟩
    · exact PanSemRangedOutput.error h
  · exact PanSemRangedOutput.error h

theorem panSemTotalReturnClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (expression : Exp (RiscV.Word 64)) (he : ExpByteRanged expression) :
    PanSemRangedOutput (panSemTotalReturnClause state expression) := by
  unfold panSemTotalReturnClause
  refine PanSemRangedOutput.exprStep h _ _ (fun value hv => ?_)
  have hvR := evalPanSemStateExp_byteRanged state h expression he value hv
  split
  · exact ⟨h.panEmptyLocals, hvR⟩
  · exact PanSemRangedOutput.error h

theorem panSemTotalExtCallClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp (RiscV.Word 64)) :
    PanSemRangedOutput (panSemTotalExtCallClause state function configuration
      configurationLength array arrayLength) := by
  refine ⟨h.extCallClause function configuration configurationLength array arrayLength, ?_⟩
  simp only [panSemTotalExtCallClause, panSemTotalExprStep, panSemTotalExtCallStep,
    panSemTotalMachineReadBytes, panSemTotalMachineWriteBytes, panEmptyLocals]
  repeat' (first | trivial | split)

theorem panSemTotalShMemLoadClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp (RiscV.Word 64)) :
    PanSemRangedOutput (panSemTotalShMemLoadClause state size kind name address) := by
  unfold panSemTotalShMemLoadClause
  refine PanSemRangedOutput.exprStep h _ _ (fun a _ => ?_)
  split
  · split
    · simp only [panShMemLoad]
      repeat' split
      all_goals (try simp only [panSemTotalShMemLoadResult, panSemTotalShMemStateBack,
        panSemTotalShMemState])
      all_goals first
        | exact PanSemRangedOutput.error h
        | exact ⟨PanSemStateRelExecRanged.of_fields (h.updateLocals name (.word _) (by simp [PanValueByteRanged]))
            rfl rfl rfl, trivial⟩
        | exact ⟨PanSemStateRelExecRanged.of_fields (h.updateGlobals name (.word _) (by simp [PanValueByteRanged]))
            rfl rfl rfl, trivial⟩
        | exact ⟨PanSemStateRelExecRanged.of_fields h.panEmptyLocals rfl rfl rfl, trivial⟩
    · exact PanSemRangedOutput.error h
  · exact PanSemRangedOutput.error h

theorem panSemTotalShMemStoreClause_rangedOutput
    {state : PanSemState (RiscV.Word 64) (FfiState σ)} (h : PanSemStateRelExecRanged state)
    (size : OpSize) (address value : Exp (RiscV.Word 64)) :
    PanSemRangedOutput (panSemTotalShMemStoreClause state size address value) := by
  unfold panSemTotalShMemStoreClause
  refine PanSemRangedOutput.exprStep h _ _ (fun a _ => ?_)
  split
  · refine PanSemRangedOutput.exprStep h _ _ (fun v _ => ?_)
    split
    · simp only [panShMemStore]
      repeat' split
      all_goals (try simp only [panSemTotalShMemStoreResult, panSemTotalShMemStateBack,
        panSemTotalShMemState])
      all_goals first
        | exact PanSemRangedOutput.error h
        | exact ⟨h.of_fields rfl rfl rfl, trivial⟩
    · exact PanSemRangedOutput.error h
  · exact PanSemRangedOutput.error h


theorem PanSemCodeRanged.of_code {state other : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemCodeRanged state) (hcode : other.code = state.code) : PanSemCodeRanged other := by
  intro name entry hentry
  rw [hcode] at hentry
  exact h name entry hentry

/-- Restoring one local with `res_var` from a byte-ranged saved binding
    preserves `PanSemStateRelExecRanged`. -/
theorem PanSemStateRelExecRanged.resVarLocals {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemStateRelExecRanged state) (name : VarName)
    (old : Option (PanValue (RiscV.Word 64)))
    (hold : ∀ value, old = some value → PanValueByteRanged value) :
    PanSemStateRelExecRanged { state with locals := resVar state.locals (name, old) } := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro key value hkey
  cases old with
  | none =>
      simp only [resVar, FDOMSUB] at hkey
      split at hkey
      · cases hkey
      · exact h.1 key value hkey
  | some saved =>
      simp only [resVar, FUPDATE] at hkey
      split at hkey
      · injection hkey with hk
        subst hk
        exact hold _ rfl
      · exact h.1 key value hkey

/-- Production-only consequences of a successful `panSemTotalCodeLookup` on
    byte-ranged code and arguments. -/
theorem panSemTotalCodeLookup_ranged (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hc : PanSemCodeRanged state) (function : FunName) (values : List (PanValue (RiscV.Word 64)))
    (hvalues : ∀ value ∈ values, PanValueByteRanged value)
    (callee : Prog (RiscV.Word 64)) (newLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (returnShape : Shape)
    (hlookup : panSemTotalCodeLookup state function values = some (callee, newLocals, returnShape)) :
    ProgByteRanged callee ∧ ShapeByteRanged returnShape ∧
      ∀ name value, newLocals name = some value → PanValueByteRanged value := by
  unfold panSemTotalCodeLookup at hlookup
  split at hlookup
  · cases hlookup
  · rename_i b r l hcall
    simp only [Option.some.injEq, Prod.mk.injEq] at hlookup
    obtain ⟨rfl, rfl, rfl⟩ := hlookup
    unfold lookupPanSemCodeCall at hcall
    cases hlk : panSemCodeLookup state.code function with
    | none => simp [hlk] at hcall
    | some entry =>
        obtain ⟨parameters, body, shape⟩ := entry
        obtain ⟨_, hbody, hshape⟩ := hc function _ hlk
        simp [hlk, bindPanValueParameters] at hcall
        obtain ⟨_, hbind⟩ := hcall
        split at hbind
        · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hbind
          obtain ⟨rfl, rfl, rfl⟩ := hbind
          exact ⟨hbody, hshape, bindFold_values _ (fun _ => none) PanValueByteRanged
            (fun e he => hvalues e.2 (List.of_mem_zip he).2) (fun _ _ h => by cases h)⟩
        · simp at hbind

/-- **Reachable rangedness of the production total evaluator.**  For a
    `ProgByteRanged` program run from a `PanSemStateRelExecRanged` state with
    byte-ranged code entries under a byte-ranged primitive handler, the result
    state is `PanSemStateRelExecRanged` and the result payload is
    `PanSemHOLResultRanged`.  Proved by well-founded induction over
    `panSemEvalMeasure`, following `panSemTotalEvaluate_exceptionShapes`; code
    rangedness carries over by the frame lemma `panSemTotalEvaluate_code`. -/
theorem panSemTotalEvaluate_ranged (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprim : PanPrimitiveHandlerByteRanged primitive) :
    ∀ (prog : Prog (RiscV.Word 64)) (state : PanSemState (RiscV.Word 64) (FfiState σ)),
      ProgByteRanged prog → PanSemStateRelExecRanged state → PanSemCodeRanged state →
      PanSemRangedOutput (panSemTotalEvaluate primitive prog state) := by
  intro prog state
  have hwf : WellFounded (@panSemEvalMeasureRel (RiscV.Word 64) (FfiState σ)) :=
    panSemEvalMeasureRel_wf
  let motive : PanSemState (RiscV.Word 64) (FfiState σ) × Prog (RiscV.Word 64) → Prop :=
    fun p => ProgByteRanged p.2 → PanSemStateRelExecRanged p.1 → PanSemCodeRanged p.1 →
      PanSemRangedOutput (panSemTotalEvaluate primitive p.2 p.1)
  have hmain : ∀ p, motive p := by
    intro p
    refine WellFounded.induction hwf p ?_
    intro p ih
    obtain ⟨state, prog⟩ := p
    intro hp h hc
    change PanSemRangedOutput (panSemTotalEvaluate primitive prog state)
    cases prog with
    | skip => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_rangedOutput .skip h
    | «break» => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_rangedOutput .break h
    | «continue» => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_rangedOutput .continue h
    | tick => rw [panSemTotalEvaluate]; exact panSemEvaluateClockLeaf_rangedOutput .tick h
    | assign kind name value =>
        rw [panSemTotalEvaluate]; exact panSemTotalAssignClause_rangedOutput h kind name value hp.2
    | primitive name operator arguments =>
        rw [panSemTotalEvaluate]
        exact panSemTotalPrimitiveClause_rangedOutput h name operator arguments primitive hprim
    | store address value => rw [panSemTotalEvaluate]; exact panSemTotalStoreClause_rangedOutput h address value
    | store32 address value => rw [panSemTotalEvaluate]; exact panSemTotalStore32Clause_rangedOutput h address value
    | storeByte address value =>
        rw [panSemTotalEvaluate]; exact panSemTotalStoreByteClause_rangedOutput h address value
    | raise exceptionId expression =>
        rw [panSemTotalEvaluate]
        exact panSemTotalRaiseClause_rangedOutput h exceptionId hp.1 expression hp.2
    | «return» expression =>
        rw [panSemTotalEvaluate]; exact panSemTotalReturnClause_rangedOutput h expression hp
    | annot tag text => rw [panSemTotalEvaluate]; exact ⟨h, trivial⟩
    | dec name shape value body =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases heval : evalPanSemStateExp state value with
        | none => exact PanSemRangedOutput.error h
        | some evaluated =>
            simp only []
            have hvR := evalPanSemStateExp_byteRanged state h value hp.2.2.1 evaluated heval
            split
            · have hb := ih (panSemTotalDecBind state name evaluated, body)
                (panSemEvalMeasureRel_decBody state name shape value body) hp.2.2.2
                (h.updateLocals name evaluated hvR) (hc.of_code rfl)
              exact ⟨hb.1.resVarLocals name (state.locals name)
                (fun v hv => h.1 name v hv), hb.2⟩
            · exact PanSemRangedOutput.error h
    | seq first second =>
        rw [panSemTotalEvaluate]
        try dsimp only
        have ih1 := ih (state, first)
          (panSemEvalMeasureRel_seq_branch state state first second first (Nat.le_refl _)
            (Or.inl rfl)) hp.1 h hc
        cases hres : (panSemTotalEvaluate primitive first state).1 with
        | none =>
            have hclk : (panSemFixClock state.clock
                (panSemTotalEvaluate primitive first state).2).clock ≤ state.clock :=
              panSemFixClock_clock_le _ _
            exact ih (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2, second)
              (panSemEvalMeasureRel_seq_branch _ state first second second hclk (Or.inr rfl)) hp.2
              (ih1.1.setClock _)
              (hc.of_code (by rw [panSemFixClock_code, panSemTotalEvaluate_code]))
        | some result =>
            refine ⟨ih1.1.setClock _, ?_⟩
            have := ih1.2
            rw [hres] at this
            exact this
    | ite condition thenBranch elseBranch =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hcond : evalPanSemStateExp state condition with
        | none => exact PanSemRangedOutput.error h
        | some v =>
            cases v with
            | word w =>
                try dsimp only
                split
                · exact ih (state, elseBranch)
                    (panSemEvalMeasureRel_ite_branch state condition thenBranch elseBranch elseBranch
                      (Or.inr rfl)) hp.2.2 h hc
                · exact ih (state, thenBranch)
                    (panSemEvalMeasureRel_ite_branch state condition thenBranch elseBranch thenBranch
                      (Or.inl rfl)) hp.2.1 h hc
            | rStruct fs => exact PanSemRangedOutput.error h
            | nStruct nm flds => exact PanSemRangedOutput.error h
    | «while» condition body =>
        rw [panSemTotalEvaluate]
        try dsimp only
        cases hcond : evalPanSemStateExp state condition with
        | none => exact PanSemRangedOutput.error h
        | some v =>
            cases v with
            | word w =>
                try dsimp only
                split
                · exact ⟨h, trivial⟩
                · split
                  · exact ⟨h.panEmptyLocals, trivial⟩
                  · rename_i hw hclk
                    try dsimp only
                    have hdecClock : state.clock - 1 < state.clock := by omega
                    have ihBody := ih ({ state with clock := state.clock - 1 }, body)
                      (panSemEvalMeasureRel_of_clock_lt hdecClock) hp.2 (h.setClock _)
                      (hc.of_code rfl)
                    have hfixLt : (panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body
                          { state with clock := state.clock - 1 }).2).clock < state.clock := by
                      have := panSemFixClock_clock_le (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2
                      omega
                    have hfixCode : PanSemCodeRanged (panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body
                          { state with clock := state.clock - 1 }).2) :=
                      hc.of_code (by rw [panSemFixClock_code, panSemTotalEvaluate_code])
                    have ihLoop := ih ((panSemFixClock (state.clock - 1)
                        (panSemTotalEvaluate primitive body { state with clock := state.clock - 1 }).2),
                        .while condition body)
                      (panSemEvalMeasureRel_of_clock_lt hfixLt) hp (ihBody.1.setClock _) hfixCode
                    have hres := ihBody.2
                    cases hbody : (panSemTotalEvaluate primitive body
                        { state with clock := state.clock - 1 }).1 with
                    | none => exact ihLoop
                    | some r =>
                        rw [hbody] at hres
                        cases r with
                        | «continue» => exact ihLoop
                        | «break» => exact ⟨ihBody.1.setClock _, trivial⟩
                        | error => exact ⟨ihBody.1.setClock _, trivial⟩
                        | timeOut => exact ⟨ihBody.1.setClock _, trivial⟩
                        | returned val => exact ⟨ihBody.1.setClock _, hres⟩
                        | exception eid val => exact ⟨ihBody.1.setClock _, hres⟩
                        | finalFfi ev => exact ⟨ihBody.1.setClock _, trivial⟩
            | rStruct fs => exact PanSemRangedOutput.error h
            | nStruct nm flds => exact PanSemRangedOutput.error h
    | call info function arguments =>
        rw [panSemTotalEvaluate]
        try dsimp only
        change ProgByteRanged (Prog.call info function arguments) at hp
        unfold ProgByteRanged at hp
        obtain ⟨_, hargs, hinfo⟩ := hp
        cases hexps : evalPanSemStateExps state arguments with
        | none => exact PanSemRangedOutput.error h
        | some values =>
            simp only []
            have hvals := evalPanSemStateExps_byteRanged state h arguments hargs values hexps
            cases hlookup : panSemTotalCodeLookup state function values with
            | none => exact PanSemRangedOutput.error h
            | some triple =>
                obtain ⟨callee, newLocals, returnShape⟩ := triple
                obtain ⟨hcalleeR, _, hlocR⟩ := panSemTotalCodeLookup_ranged state hc function
                  values hvals callee newLocals returnShape hlookup
                simp only []
                split
                · exact ⟨h.panEmptyLocals, trivial⟩
                · rename_i hclk
                  have hdecClock : state.clock - 1 < state.clock := by omega
                  have ihBody := ih ({ state with clock := state.clock - 1, locals := newLocals }, callee)
                    (panSemEvalMeasureRel_of_clock_lt hdecClock) hcalleeR ⟨hlocR, h.2.1, h.2.2⟩
                    (hc.of_code rfl)
                  have hfixR : PanSemStateRelExecRanged (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2) :=
                    ihBody.1.setClock _
                  have hfixedClock : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).clock <
                      state.clock := by
                    have hle := panSemFixClock_clock_le (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2
                    omega
                  have hfixCode : PanSemCodeRanged (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2) :=
                    hc.of_code (by rw [panSemFixClock_code, panSemTotalEvaluate_code])
                  have hres := ihBody.2
                  cases hcall : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).1 with
                  | none => exact ⟨hfixR, trivial⟩
                  | some r =>
                      rw [hcall] at hres
                      cases r with
                      | error => exact ⟨hfixR.panEmptyLocals, trivial⟩
                      | timeOut => exact ⟨hfixR.panEmptyLocals, trivial⟩
                      | finalFfi ev => exact ⟨hfixR.panEmptyLocals, trivial⟩
                      | «break» => exact ⟨hfixR, trivial⟩
                      | «continue» => exact ⟨hfixR, trivial⟩
                      | returned value =>
                          try dsimp only
                          split
                          · split
                            · exact ⟨hfixR.panEmptyLocals, hres⟩
                            · exact ⟨hfixR.restoreLocals h, trivial⟩
                            · split
                              · split
                                · exact ⟨(hfixR.restoreLocals h).updateLocals _ value hres, trivial⟩
                                · exact ⟨(hfixR.restoreLocals h).updateGlobals _ value hres, trivial⟩
                              · exact ⟨hfixR, trivial⟩
                          · exact ⟨hfixR, trivial⟩
                      | exception exceptionId value =>
                          try dsimp only
                          split
                          · exact ⟨hfixR.panEmptyLocals, hres⟩
                          · exact ⟨hfixR.panEmptyLocals, hres⟩
                          · rename_i kindOpt handlerId handlerVar handlerProg
                            obtain ⟨_, _, _, hhandlerR⟩ := hinfo
                            split
                            · split
                              · split
                                · exact ih
                                    ({ panSemFixClock (state.clock - 1)
                                          (panSemTotalEvaluate primitive callee
                                            { state with clock := state.clock - 1, locals := newLocals }).2 with
                                        locals := updatePanValueMap state.locals handlerVar value }, handlerProg)
                                    (panSemEvalMeasureRel_of_clock_lt hfixedClock) hhandlerR
                                    ((hfixR.restoreLocals h).updateLocals _ value hres.2)
                                    (hfixCode.of_code rfl)
                                · exact ⟨hfixR, trivial⟩
                              · exact ⟨hfixR, trivial⟩
                            · exact ⟨hfixR.panEmptyLocals, hres⟩
    | decCall name shape function arguments continuation =>
        rw [panSemTotalEvaluate]
        try dsimp only
        change ProgByteRanged (Prog.decCall name shape function arguments continuation) at hp
        unfold ProgByteRanged at hp
        obtain ⟨_, _, _, hargs, hcontR⟩ := hp
        cases hexps : evalPanSemStateExps state arguments with
        | none => exact PanSemRangedOutput.error h
        | some values =>
            simp only []
            have hvals := evalPanSemStateExps_byteRanged state h arguments hargs values hexps
            cases hlookup : panSemTotalCodeLookup state function values with
            | none => exact PanSemRangedOutput.error h
            | some triple =>
                obtain ⟨callee, newLocals, returnShape⟩ := triple
                obtain ⟨hcalleeR, _, hlocR⟩ := panSemTotalCodeLookup_ranged state hc function
                  values hvals callee newLocals returnShape hlookup
                simp only []
                split
                · exact ⟨h.panEmptyLocals, trivial⟩
                · rename_i hclk
                  have hdecClock : state.clock - 1 < state.clock := by omega
                  have ihBody := ih ({ state with clock := state.clock - 1, locals := newLocals }, callee)
                    (panSemEvalMeasureRel_of_clock_lt hdecClock) hcalleeR ⟨hlocR, h.2.1, h.2.2⟩
                    (hc.of_code rfl)
                  have hfixR : PanSemStateRelExecRanged (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2) :=
                    ihBody.1.setClock _
                  have hfixedClock : (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2).clock <
                      state.clock := by
                    have hle := panSemFixClock_clock_le (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2
                    omega
                  have hfixCode : PanSemCodeRanged (panSemFixClock (state.clock - 1)
                      (panSemTotalEvaluate primitive callee
                        ({ state with clock := state.clock - 1, locals := newLocals })).2) :=
                    hc.of_code (by rw [panSemFixClock_code, panSemTotalEvaluate_code])
                  have hres := ihBody.2
                  cases hcall : (panSemTotalEvaluate primitive callee
                      ({ state with clock := state.clock - 1, locals := newLocals })).1 with
                  | none => exact ⟨hfixR, trivial⟩
                  | some r =>
                      rw [hcall] at hres
                      cases r with
                      | error => exact ⟨hfixR.panEmptyLocals, trivial⟩
                      | timeOut => exact ⟨hfixR.panEmptyLocals, trivial⟩
                      | finalFfi ev => exact ⟨hfixR.panEmptyLocals, trivial⟩
                      | «break» => exact ⟨hfixR, trivial⟩
                      | «continue» => exact ⟨hfixR, trivial⟩
                      | exception eid val => exact ⟨hfixR.panEmptyLocals, hres⟩
                      | returned value =>
                          try dsimp only
                          split
                          · have ihCont := ih
                              ({ panSemFixClock (state.clock - 1)
                                    (panSemTotalEvaluate primitive callee
                                      { state with clock := state.clock - 1, locals := newLocals }).2 with
                                  locals := updatePanValueMap state.locals name value }, continuation)
                              (panSemEvalMeasureRel_of_clock_lt hfixedClock) hcontR
                              ((hfixR.restoreLocals h).updateLocals _ value hres)
                              (hfixCode.of_code rfl)
                            exact ⟨ihCont.1.resVarLocals name (state.locals name)
                              (fun v hv => h.1 name v hv), ihCont.2⟩
                          · exact ⟨hfixR, trivial⟩
    | extCall function configuration configurationLength array arrayLength =>
        rw [panSemTotalEvaluate]
        exact panSemTotalExtCallClause_rangedOutput h function configuration configurationLength
          array arrayLength
    | shMemLoad size kind name address =>
        rw [panSemTotalEvaluate]; exact panSemTotalShMemLoadClause_rangedOutput h size kind name address
    | shMemStore size address value =>
        rw [panSemTotalEvaluate]; exact panSemTotalShMemStoreClause_rangedOutput h size address value
  exact hmain (state, prog)

/-- Reachable rangedness for the canonical entrypoint `panSemTotalEvaluateCake`:
    the primitive-handler premise is discharged by `panPrimopHOL_byteRanged`. -/
theorem panSemTotalEvaluateCake_ranged
    (prog : Prog (RiscV.Word 64)) (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hprog : ProgByteRanged prog) (hstate : PanSemStateRelExecRanged state)
    (hcode : PanSemCodeRanged state) :
    PanSemRangedOutput (panSemTotalEvaluateCake prog state) :=
  panSemTotalEvaluate_ranged panPrimopHOL panPrimopHOL_byteRanged prog state hprog hstate hcode

/-- The rangedness invariant is closed under runs of the canonical entrypoint,
    including code-entry rangedness (`panSemTotalEvaluate_code`). -/
theorem panSemTotalEvaluateCake_codeRanged
    (prog : Prog (RiscV.Word 64)) (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hcode : PanSemCodeRanged state) :
    PanSemCodeRanged (panSemTotalEvaluateCake prog state).2 :=
  hcode.of_code (panSemTotalEvaluate_code panPrimopHOL prog state)


/-! ### Initial-state code rangedness

The code map of a production state is an association list looked up by
`lookupInfo`; `panSemCodeLookup_mem_binding` backs every successful lookup by a
stored entry.  A code map whose stored entries are all byte-ranged therefore
satisfies `PanSemCodeRanged`.  The declaration-derived code map
(`functionEntries`, HOL `panLang$functions`) has byte-ranged entries when every
declaration is `DeclByteRanged`, and the `pan_structs` code conversion (the
`panStructConvertCode` map of `PanStructs/CompileCorrect.lean`) preserves them.
This mirrors DS9's `exceptionEntries` lemmas for `PanSemExceptionShapesRanged`
(`flapjack-pxn.18.4.3.77.2.15.5`). -/

/-- A state whose stored code entries are all byte-ranged is `PanSemCodeRanged`. -/
theorem panSemCodeRanged_of_entries (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hentries : ∀ entry ∈ state.code, PanLangEntryByteRanged entry.2) :
    PanSemCodeRanged state := by
  intro name entry hlookup
  exact hentries (name, entry) (panSemCodeLookup_mem_binding state.code name entry hlookup)

/-- The declaration-derived code entries of `DeclByteRanged` declarations are
    byte-ranged: a `function` declaration contributes its `FunDeclByteRanged`
    parameters, body and return shape. -/
theorem functionEntries_byteRanged (declarations : List (Decl (RiscV.Word 64)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ entry ∈ functionEntries declarations, PanLangEntryByteRanged entry.2 := by
  induction declarations with
  | nil => intro entry hentry; simp [functionEntries] at hentry
  | cons declaration declarations ih =>
      have htail := ih (fun d hd => hranged d (by simp [hd]))
      cases declaration with
      | function fd =>
          intro entry hentry
          simp only [functionEntries, List.mem_cons] at hentry
          rcases hentry with rfl | hentry
          · obtain ⟨_, hparams, hbody, hret⟩ := (hranged (.function fd) (by simp) :
              FunDeclByteRanged fd)
            exact ⟨hparams, hbody, hret⟩
          · exact htail entry hentry
      | decl _ _ _ => simpa only [functionEntries] using htail
      | exnDecl _ _ => simpa only [functionEntries] using htail
      | name _ _ => simpa only [functionEntries] using htail

/-- The compiled initial code map `functionEntries declarations` satisfies
    `PanSemCodeRanged` whenever every declaration is `DeclByteRanged`. -/
theorem panSemCodeRanged_of_functionEntries (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (declarations : List (Decl (RiscV.Word 64)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    PanSemCodeRanged { state with code := functionEntries declarations } :=
  panSemCodeRanged_of_entries _ (functionEntries_byteRanged declarations hranged)

/-- The `pan_structs` code conversion (`panStructConvertCode`, rendered inline)
    preserves `PanSemCodeRanged` for a byte-ranged structure context, via
    `structCompileShape_byteRanged` and `structCompileProg_byteRanged`. -/
theorem PanSemCodeRanged.map_structCompile [BEq String]
    {state : PanSemState (RiscV.Word 64) (FfiState σ)}
    (hentries : ∀ entry ∈ state.code, PanLangEntryByteRanged entry.2)
    (context : StructPassContext) (hc : CtxBR context.structs) :
    PanSemCodeRanged { state with code := state.code.map fun (name, (parameters, body, returnShape)) =>
      (name,
        (parameters.map fun (parameter, shape) =>
            (parameter, structCompileShape context.structs shape),
          structCompileProg { context with locals := parameters } body,
          structCompileShape context.structs returnShape)) } := by
  apply panSemCodeRanged_of_entries
  intro converted hconverted
  obtain ⟨⟨name, parameters, body, returnShape⟩, horiginal, rfl⟩ := List.mem_map.mp hconverted
  obtain ⟨hparams, hbody, hret⟩ := hentries _ horiginal
  refine ⟨?_, structCompileProg_byteRanged { context with locals := parameters } hc body hbody,
    structCompileShape_byteRanged context.structs returnShape hc hret⟩
  intro parameter hparameter
  obtain ⟨⟨parameterName, shape⟩, hmem, rfl⟩ := List.mem_map.mp hparameter
  obtain ⟨hname, hshape⟩ := hparams _ hmem
  exact ⟨hname, structCompileShape_byteRanged context.structs shape hc hshape⟩

end Ranged

section Agreement

variable {σ : Type}

/-- `Call` agreement with the callee rangedness premises discharged: `hcode`
    from `PanSemCodeRanged production` and `hcallee` from
    `panSemTotalEvaluate_ranged` under a byte-ranged primitive handler. -/
theorem panSemTotalEvaluate_call_agree_of_ranged
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hprim : PanPrimitiveHandlerByteRanged primitive)
    (hcodeRanged : PanSemCodeRanged production)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64))
    (hexceptionShapes : ∀ identifier shape,
      production.exceptionShapes identifier = some shape → ShapeByteRanged shape)
    (ihCallee : ∀ (program : ProgHOL 64)
        (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        production'.clock < production.clock →
        PanSemTotalAgreeAt primitive (progOfHOL program) program production' exact')
    (ihHandler : ∀ kind eid var handler,
        info = some (kind, some (eid, var, handler)) →
        ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
          (exact' : PanSemStateFiniteExact 64 σ),
          PanSemStateRelExec production' exact'.toExact →
          PanSemStateRelExecRanged production' →
          PanSemTotalAgreeAt primitive (progOfHOL handler) handler production' exact') :
    PanSemTotalAgreeAt primitive (progOfHOL (.call info function arguments))
      (.call info function arguments) production exact :=
  panSemTotalEvaluate_call_agree (primitive := primitive) (production := production) (exact := exact) (hrel := hrel) (hranged := hranged) (info := info) (function := function) (arguments := arguments) (hexceptionShapes := hexceptionShapes) (ihCallee := ihCallee) (ihHandler := ihHandler)
    (hcode := fun entry hentry => hcodeRanged _ entry hentry)
    (hcallee := fun values hvalues callee newLocals returnShape hlookup => by
      obtain ⟨hcalleeR, _, hlocR⟩ := panSemTotalCodeLookup_ranged production hcodeRanged _
        values hvalues callee newLocals returnShape hlookup
      exact panSemTotalEvaluate_ranged primitive hprim callee _ hcalleeR
        ⟨hlocR, hranged.2.1, hranged.2.2⟩ (hcodeRanged.of_code rfl))

/-- `DecCall` agreement with the callee rangedness premises discharged: `hcode`
    from `PanSemCodeRanged production` and `hcallee` from
    `panSemTotalEvaluate_ranged` under a byte-ranged primitive handler. -/
theorem panSemTotalEvaluate_decCall_agree_of_ranged
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hprim : PanPrimitiveHandlerByteRanged primitive)
    (hcodeRanged : PanSemCodeRanged production)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64)
    (ihCallee : ∀ (program : ProgHOL 64)
        (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        production'.clock < production.clock →
        PanSemTotalAgreeAt primitive (progOfHOL program) program production' exact')
    (ihContinuation : ∀ (production' : PanSemState (RiscV.Word 64) (FfiState σ))
        (exact' : PanSemStateFiniteExact 64 σ),
        PanSemStateRelExec production' exact'.toExact →
        PanSemStateRelExecRanged production' →
        PanSemTotalAgreeAt primitive (progOfHOL continuation) continuation production' exact') :
    PanSemTotalAgreeAt primitive
      (progOfHOL (.decCall resultName shape function arguments continuation))
      (.decCall resultName shape function arguments continuation) production exact :=
  panSemTotalEvaluate_decCall_agree (primitive := primitive) (production := production) (exact := exact) (hrel := hrel) (hranged := hranged) (resultName := resultName) (shape := shape) (function := function) (arguments := arguments) (continuation := continuation) (ihCallee := ihCallee) (ihContinuation := ihContinuation)
    (hcode := fun entry hentry => hcodeRanged _ entry hentry)
    (hcallee := fun values hvalues callee newLocals returnShape hlookup => by
      obtain ⟨hcalleeR, _, hlocR⟩ := panSemTotalCodeLookup_ranged production hcodeRanged _
        values hvalues callee newLocals returnShape hlookup
      exact panSemTotalEvaluate_ranged primitive hprim callee _ hcalleeR
        ⟨hlocR, hranged.2.1, hranged.2.2⟩ (hcodeRanged.of_code rfl))

end Agreement

end Flapjack
