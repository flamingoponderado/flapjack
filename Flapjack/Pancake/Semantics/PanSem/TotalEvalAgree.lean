import Flapjack.Pancake.Semantics.PanSem.TotalEvalExtCallBridge

/-!
# Total production/exact agreement of the panSem evaluators

Assembles the per-constructor agreements of `TotalEvalBridge.lean`,
`TotalEvalExpBridge.lean`, `TotalEvalCallBridge.lean` and
`TotalEvalExtCallBridge.lean` into one theorem relating the production total
evaluator `panSemTotalEvaluate` on `progOfHOL p` to the tagged exact
`evaluateHOLFiniteState` on `p`, for every exact program `p`
(`flapjack-pxn.18.4.3.77.2.14.19`, `.77.2.14`).  The rangedness
premises are the reachable invariants of `TotalEvalRanged.lean`.  The theorem
is a Flapjack bridge, not the tagged HOL `pc_compile_correct` or `evaluate_ind`.
Untagged Flapjack-specific bridge infrastructure.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

/-- Every decoded exact program is byte-ranged. -/
theorem progOfHOL_byteRanged_bridge : (p : ProgHOL 64) → ProgByteRanged (progOfHOL p)
  | .skip => by rw [progOfHOL]; trivial
  | .dec name shape value body => by
      rw [progOfHOL]
      exact ⟨nameRanged_toStringOfBytes_bridge name, shapeOfHOL_byteRanged_bridge shape,
        expOfHOL_byteRanged_bridge value, progOfHOL_byteRanged_bridge body⟩
  | .assign kind name value => by
      rw [progOfHOL]
      exact ⟨nameRanged_toStringOfBytes_bridge name, expOfHOL_byteRanged_bridge value⟩
  | .primitive name operator args => by
      rw [progOfHOL]
      refine ⟨nameRanged_toStringOfBytes_bridge name, fun e he => ?_⟩
      obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
      exact expOfHOL_byteRanged_bridge e'
  | .store address value => by
      rw [progOfHOL]; exact ⟨expOfHOL_byteRanged_bridge address, expOfHOL_byteRanged_bridge value⟩
  | .store32 address value => by
      rw [progOfHOL]; exact ⟨expOfHOL_byteRanged_bridge address, expOfHOL_byteRanged_bridge value⟩
  | .storeByte address value => by
      rw [progOfHOL]; exact ⟨expOfHOL_byteRanged_bridge address, expOfHOL_byteRanged_bridge value⟩
  | .seq first second => by
      rw [progOfHOL]; exact ⟨progOfHOL_byteRanged_bridge first, progOfHOL_byteRanged_bridge second⟩
  | .ite condition thenBranch elseBranch => by
      rw [progOfHOL]
      exact ⟨expOfHOL_byteRanged_bridge condition, progOfHOL_byteRanged_bridge thenBranch,
        progOfHOL_byteRanged_bridge elseBranch⟩
  | .while condition body => by
      rw [progOfHOL]
      exact ⟨expOfHOL_byteRanged_bridge condition, progOfHOL_byteRanged_bridge body⟩
  | .break => by rw [progOfHOL]; trivial
  | .continue => by rw [progOfHOL]; trivial
  | .call none name args => by
      rw [progOfHOL]
      refine ⟨nameRanged_toStringOfBytes_bridge name, fun e he => ?_, trivial⟩
      obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
      exact expOfHOL_byteRanged_bridge e'
  | .call (some (kind, none)) name args => by
      rw [progOfHOL]
      refine ⟨nameRanged_toStringOfBytes_bridge name, fun e he => ?_, ?_, trivial⟩
      · obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
        exact expOfHOL_byteRanged_bridge e'
      · rcases kind with _ | ⟨k, n⟩
        · trivial
        · exact nameRanged_toStringOfBytes_bridge n
  | .call (some (kind, some (eid, var, handler))) name args => by
      rw [progOfHOL]
      refine ⟨nameRanged_toStringOfBytes_bridge name, fun e he => ?_, ?_,
        nameRanged_toStringOfBytes_bridge eid, nameRanged_toStringOfBytes_bridge var,
        progOfHOL_byteRanged_bridge handler⟩
      · obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
        exact expOfHOL_byteRanged_bridge e'
      · rcases kind with _ | ⟨k, n⟩
        · trivial
        · exact nameRanged_toStringOfBytes_bridge n
  | .decCall name shape function args body => by
      rw [progOfHOL]
      refine ⟨nameRanged_toStringOfBytes_bridge name, shapeOfHOL_byteRanged_bridge shape,
        nameRanged_toStringOfBytes_bridge function, fun e he => ?_, progOfHOL_byteRanged_bridge body⟩
      obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
      exact expOfHOL_byteRanged_bridge e'
  | .extCall function configuration configurationLength array arrayLength => by
      rw [progOfHOL]
      exact ⟨nameRanged_toStringOfBytes_bridge function, expOfHOL_byteRanged_bridge configuration,
        expOfHOL_byteRanged_bridge configurationLength, expOfHOL_byteRanged_bridge array,
        expOfHOL_byteRanged_bridge arrayLength⟩
  | .raise exception value => by
      rw [progOfHOL]
      exact ⟨nameRanged_toStringOfBytes_bridge exception, expOfHOL_byteRanged_bridge value⟩
  | .return value => by rw [progOfHOL]; exact expOfHOL_byteRanged_bridge value
  | .shMemLoad size kind name address => by
      rw [progOfHOL]
      exact ⟨nameRanged_toStringOfBytes_bridge name, expOfHOL_byteRanged_bridge address⟩
  | .shMemStore size address value => by
      rw [progOfHOL]; exact ⟨expOfHOL_byteRanged_bridge address, expOfHOL_byteRanged_bridge value⟩
  | .tick => by rw [progOfHOL]; trivial
  | .annot tag text => by
      rw [progOfHOL]
      exact ⟨nameRanged_toStringOfBytes_bridge tag, nameRanged_toStringOfBytes_bridge text⟩

/-- Exception-shape rangedness depends only on the `exceptionShapes` field. -/
theorem PanSemExceptionShapesRanged.of_eq {σ : Type}
    {state other : PanSemState (RiscV.Word 64) (FfiState σ)}
    (h : PanSemExceptionShapesRanged state) (heq : other.exceptionShapes = state.exceptionShapes) :
    PanSemExceptionShapesRanged other := by
  intro eid shape hlookup
  rw [heq] at hlookup
  exact h eid shape hlookup

/-- Lexicographic step for a non-increasing first and decreasing second component. -/
theorem prodLex_of_le_of_lt {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.lt_or_eq_of_le ha with h | h
  · exact .left _ _ h
  · subst h; exact .right _ hb

/-- **Total production/exact agreement of the panSem evaluators.**  For every
    exact program `p`, running the production total evaluator on `progOfHOL p`
    from a state related to the exact state, with the reachable rangedness
    invariants (`PanSemStateRelExecRanged`, `PanSemCodeRanged`,
    `PanSemExceptionShapesRanged`) and a byte-ranged primitive handler agreeing
    with `panPrimopHOLExact`, gives a `PanSemHOLResultOptionRel`-related result
    and a `PanSemStateRelExec`-related post-state compared with
    `evaluateHOLFiniteState exact p`.  No target run, result or post-state is
    assumed.  Proved by well-founded recursion on `(production.clock, sizeOf p)`,
    assembling the per-constructor agreements; the Seq/While post-state and
    Call/DecCall callee rangedness premises are discharged by
    `panSemTotalEvaluate_ranged`.

    Every constructor is proved, including `ShMemStore`
    (`panSemTotalEvaluate_shMemStore_agree`, `flapjack-pxn.18.4.3.77.2.14.17`).
    Untagged: the statement relates the production
    evaluator to the tagged exact one and is not a HOL declaration. -/
theorem panSemTotalEvaluate_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprimBridge : ∀ (operator : PrimOp) (values : List (PanValue (RiscV.Word 64))),
      Option.map panValueToHOL (primitive operator values)
        = panPrimopHOLExact operator (values.map panValueToHOL))
    (hprimRanged : PanPrimitiveHandlerByteRanged primitive)
    (p : ProgHOL 64) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production) :
    PanSemTotalAgreeAt primitive (progOfHOL p) p production exact := by
  classical
  match p with
  | .skip => rw [progOfHOL]; exact panSemTotalEvaluate_skip_agree primitive production exact hrel
  | .break => rw [progOfHOL]; exact panSemTotalEvaluate_break_agree primitive production exact hrel
  | .continue => rw [progOfHOL]; exact panSemTotalEvaluate_continue_agree primitive production exact hrel
  | .tick => rw [progOfHOL]; exact panSemTotalEvaluate_tick_agree primitive production exact hrel
  | .annot tag text =>
      rw [progOfHOL]; exact panSemTotalEvaluate_annot_agree primitive production exact hrel tag text
  | .assign kind name value =>
      have h := panSemTotalEvaluate_assign_agree primitive production exact hrel hranged kind
        (toStringOfBytes name) (nameRanged_toStringOfBytes_bridge name) (expOfHOL value)
        (expOfHOL_byteRanged_bridge value)
      rw [ofString_toStringOfBytes, expToHOL_expOfHOL] at h
      rw [progOfHOL]; exact h
  | .primitive name operator args =>
      have h := panSemTotalEvaluate_primitive_agree primitive production exact hrel hranged
        (toStringOfBytes name) (nameRanged_toStringOfBytes_bridge name) operator
        (args.map expOfHOL) (fun e he => by
          obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
          exact expOfHOL_byteRanged_bridge e') (hprimBridge operator) hprimRanged
      simp only [ofString_toStringOfBytes, List.map_map, Function.comp_def, expToHOL_expOfHOL,
        List.map_id'] at h
      rw [progOfHOL]; exact h
  | .store address value =>
      have h := panSemTotalEvaluate_store_agree primitive production exact hrel hranged
        (expOfHOL address) (expOfHOL value) (expOfHOL_byteRanged_bridge address)
        (expOfHOL_byteRanged_bridge value)
      rw [expToHOL_expOfHOL, expToHOL_expOfHOL] at h
      rw [progOfHOL]; exact h
  | .store32 address value =>
      rw [progOfHOL]
      exact panSemTotalEvaluate_store32_agree primitive production exact hrel hranged address value
  | .storeByte address value =>
      rw [progOfHOL]
      exact panSemTotalEvaluate_storeByte_agree primitive production exact hrel hranged address value
  | .raise exception value =>
      rw [progOfHOL]
      exact panSemTotalEvaluate_raise_agree primitive production exact hrel hranged hexn exception value
  | .return value =>
      rw [progOfHOL]
      exact panSemTotalEvaluate_return_agree primitive production exact hrel hranged value
  | .extCall function configuration configurationLength array arrayLength =>
      exact panSemTotalEvaluate_extCall_agree primitive production exact hrel hranged function
        configuration configurationLength array arrayLength
  | .shMemLoad size kind name address =>
      rw [progOfHOL]
      exact panSemTotalEvaluate_shMemLoad_agree primitive production exact hrel hranged size kind
        name address
  | .shMemStore size address value =>
      rw [progOfHOL]
      exact panSemTotalEvaluate_shMemStore_agree primitive production exact hrel hranged size
        address value
  | .ite condition thenBranch elseBranch =>
      exact panSemTotalEvaluate_ite_agree primitive production exact hrel hranged condition
        thenBranch elseBranch
        (panSemTotalEvaluate_agree primitive hprimBridge hprimRanged thenBranch
          production exact hrel hranged hcode hexn)
        (panSemTotalEvaluate_agree primitive hprimBridge hprimRanged elseBranch
          production exact hrel hranged hcode hexn)
  | .seq first second =>
      exact panSemTotalEvaluate_seq_agree primitive production exact hrel first second
        (panSemTotalEvaluate_agree primitive hprimBridge hprimRanged first
          production exact hrel hranged hcode hexn)
        (panSemTotalEvaluate_ranged primitive hprimRanged (progOfHOL first) production
          (progOfHOL_byteRanged_bridge first) hranged hcode).1
        (fun production' exact' hrel' hranged' hframe =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged second
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
  | .dec name shape value body =>
      exact panSemTotalEvaluate_dec_agree primitive production exact hrel hranged name shape
        value body
        (fun production' exact' hrel' hranged' hframe =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged body
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
  | .while condition body =>
      exact panSemTotalEvaluate_while_agree primitive production exact hrel hranged condition body
        (fun production' exact' hrel' hranged' hframe =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged body
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
        (panSemTotalEvaluate_ranged primitive hprimRanged (progOfHOL body)
          { production with clock := production.clock - 1 }
          (progOfHOL_byteRanged_bridge body) (hranged.setClock (production.clock - 1))
          (hcode.of_code rfl)).1
        (fun production' exact' hrel' hranged' hframe hlt =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged
            (.while condition body) production' exact' hrel' hranged' (hcode.of_code hframe.1)
            (hexn.of_eq hframe.2.1))
  | .call info function arguments =>
      exact panSemTotalEvaluate_call_agree_of_ranged (primitive := primitive)
        (production := production) (exact := exact) (hrel := hrel) (hranged := hranged)
        (hprim := hprimRanged) (hcodeRanged := hcode) (info := info) (function := function)
        (arguments := arguments) (hexceptionShapes := hexn)
        (ihCallee := fun program production' exact' hrel' hranged' hframe hlt =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged program
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
        (ihHandler := fun kind eid var handler hinfo production' exact' hrel' hranged' hframe =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged handler
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
  | .decCall resultName shape function arguments continuation =>
      exact panSemTotalEvaluate_decCall_agree_of_ranged (primitive := primitive)
        (production := production) (exact := exact) (hrel := hrel) (hranged := hranged)
        (hprim := hprimRanged) (hcodeRanged := hcode) (resultName := resultName) (shape := shape)
        (function := function) (arguments := arguments) (continuation := continuation)
        (ihCallee := fun program production' exact' hrel' hranged' hframe hlt =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged program
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
        (ihContinuation := fun production' exact' hrel' hranged' hframe =>
          panSemTotalEvaluate_agree primitive hprimBridge hprimRanged continuation
            production' exact' hrel' hranged' (hcode.of_code hframe.1) (hexn.of_eq hframe.2.1))
termination_by (production.clock, sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact .left _ _ (by assumption)
    | exact .right _ (by omega)
    | exact prodLex_of_le_of_lt hframe.2.2 (by omega)
    | (subst hinfo
       exact prodLex_of_le_of_lt hframe.2.2 (by simp; omega))

/-- The total agreement for the canonical entrypoint `panSemTotalEvaluateCake`:
    the handler premises are discharged by `panPrimopHOL_bridge` and
    `panPrimopHOL_byteRanged`. -/
theorem panSemTotalEvaluateCake_agree {σ : Type}
    (p : ProgHOL 64) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production) :
    PanSemTotalAgreeAt panPrimopHOL (progOfHOL p) p production exact :=
  panSemTotalEvaluate_agree panPrimopHOL panPrimopHOL_bridge panPrimopHOL_byteRanged
    p production exact hrel hranged hcode hexn

/-- Replacing the clock on both sides by the same value preserves
    `PanSemStateRelExec` (HOL `s with clock := k`). -/
theorem PanSemStateRelExec.setClock {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateFiniteExact 64 σ}
    (h : PanSemStateRelExec production exact.toExact) (clock : Nat) :
    PanSemStateRelExec { production with clock := clock }
      ({ exact with clock := clock } : PanSemStateFiniteExact 64 σ).toExact := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, _, hbe, hffi, hb, ht⟩ := h
  exact ⟨hl, hg, hs, hc, he, hm, hmd, hsm, rfl, hbe, hffi, hb, ht⟩

/-- **Semantics-entry form.**  HOL `semantics_def`
    (`cakeml/pancake/semantics/panSemScript.sml:785-809`) runs the entry program
    `Call NONE start []` (`panEntryProgram`) at every clock `k` from
    `s with clock := k`.  For a related base state pair satisfying the reachable
    invariants, the production run agrees with the exact run at every clock. -/
theorem panSemTotalEvaluate_agree_entry {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprimBridge : ∀ (operator : PrimOp) (values : List (PanValue (RiscV.Word 64))),
      Option.map panValueToHOL (primitive operator values)
        = panPrimopHOLExact operator (values.map panValueToHOL))
    (hprimRanged : PanPrimitiveHandlerByteRanged primitive)
    (start : MlS) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production) (clock : Nat) :
    PanSemTotalAgreeAt primitive (.call none (toStringOfBytes start) [])
      (.call none start [] : ProgHOL 64)
      { production with clock := clock } { exact with clock := clock } := by
  have h := panSemTotalEvaluate_agree primitive hprimBridge hprimRanged
    (.call none start [] : ProgHOL 64) { production with clock := clock }
    { exact with clock := clock } (hrel.setClock clock) (hranged.setClock clock)
    (hcode.of_code rfl) (hexn.of_eq rfl)
  rw [progOfHOL_call_callInfo] at h
  exact h

/-- The semantics-entry form for the canonical entrypoint `panSemTotalEvaluateCake`. -/
theorem panSemTotalEvaluateCake_agree_entry {σ : Type}
    (start : MlS) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production) (clock : Nat) :
    PanSemTotalAgreeAt panPrimopHOL (.call none (toStringOfBytes start) [])
      (.call none start [] : ProgHOL 64)
      { production with clock := clock } { exact with clock := clock } :=
  panSemTotalEvaluate_agree_entry panPrimopHOL panPrimopHOL_bridge panPrimopHOL_byteRanged start
    production exact hrel hranged hcode hexn clock

/-- **Observation-level entry agreement.**  At every clock `k`, the production
    and exact runs of the `semantics_def` entry program have related results and
    related FFI event traces (`FfiEventListRel` on `ffi.io_events`), which are
    the observations HOL `semantics_def` inspects. -/
theorem panSemTotalEvaluate_entry_observations {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprimBridge : ∀ (operator : PrimOp) (values : List (PanValue (RiscV.Word 64))),
      Option.map panValueToHOL (primitive operator values)
        = panPrimopHOLExact operator (values.map panValueToHOL))
    (hprimRanged : PanPrimitiveHandlerByteRanged primitive)
    (start : MlS) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production) (clock : Nat) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.call none (toStringOfBytes start) [])
          { production with clock := clock }).1
        (evaluateHOLFiniteState { exact with clock := clock } (.call none start [])).1 ∧
      FfiEventListRel
        (panSemTotalEvaluate primitive (.call none (toStringOfBytes start) [])
          { production with clock := clock }).2.ffi.ioEvents
        (evaluateHOLFiniteState { exact with clock := clock } (.call none start [])).2.ffi.ioEvents := by
  obtain ⟨hres, hstate⟩ := panSemTotalEvaluate_agree_entry primitive hprimBridge hprimRanged start
    production exact hrel hranged hcode hexn clock
  exact ⟨hres, hstate.2.2.2.2.2.2.2.2.2.2.1.2.1⟩

end Flapjack
