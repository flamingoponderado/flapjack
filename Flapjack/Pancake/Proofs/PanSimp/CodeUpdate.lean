import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! Code-map updates do not affect the evaluation of the non-calling Pan
statements: `evaluate (p, s with code := c) = (res, post with code := c)`
whenever `evaluate (p, s) = (res, post)`. Flapjack infrastructure for the
pan_simp `compile_correct` simulation (no separate HOL original; the
original proof re-derives these per case with `state_rel_def`). The proofs
follow the pan_globals `evaluate_fperm` leaf cases with the permuted code map
replaced by an arbitrary one. -/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

/-- `Skip` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Skip {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.skip : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.skip : ProgHOL width) =
      (res, { post with code := c }) := by
  rw [evaluateHOLFiniteState_skip] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (none : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  · exact evaluateHOLFiniteState_skip { state with code := c }
  all_goals simp

/-- `Break` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Break {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.break : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.break : ProgHOL width) =
      (res, { post with code := c }) := by
  rw [evaluateHOLFiniteState_break] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (some .break : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  · exact evaluateHOLFiniteState_break { state with code := c }
  all_goals simp

/-- `Continue` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Continue {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.continue : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.continue : ProgHOL width) =
      (res, { post with code := c }) := by
  rw [evaluateHOLFiniteState_continue] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (some .continue : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  · exact evaluateHOLFiniteState_continue { state with code := c }
  all_goals simp


/-- `Annot` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Annot {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ) (tag text : MlS)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.annot tag text : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.annot tag text : ProgHOL width) =
      (res, { post with code := c }) := by
  rw [evaluateHOLFiniteState_annot] at heval
  have hpost : state = post := congrArg Prod.snd heval
  have hres : (none : Option (PanSemResultExact width)) = res := congrArg Prod.fst heval
  cases hpost
  cases hres
  · exact evaluateHOLFiniteState_annot { state with code := c } tag text
  all_goals simp

/-- `Tick` evaluation (timeout and decrement branches) commutes with a code-map update. -/
theorem evaluateCodeUpd_Tick {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.tick : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.tick : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  · rw [evaluateHOLFiniteState_tick] at heval ⊢
    by_cases hc : state.clock = 0
    · simp only [if_pos hc, emptyLocalsHOLFinite] at heval ⊢
      simpa only [Prod.fst, Prod.snd] using congrArg
        (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
          (run.1, { run.2 with code := c })) heval
    · simp only [if_neg hc, decClockHOLFinite] at heval ⊢
      simpa only [Prod.fst, Prod.snd] using congrArg
        (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
          (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `Assign` evaluation, including expression failure and validity branches,
commutes with a code-map update. -/
theorem evaluateCodeUpd_Assign {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (kind : VarKind) (name : MlS) (expression : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.assign kind name expression : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.assign kind name expression : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have he : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  have hvalid (value : ValueHOL width) :
      isValidValueHOLFinite { state with code := c } kind name value =
        isValidValueHOLFinite state kind name value := by
    cases kind <;> rfl
  have hset (value : ValueHOL width) :
      setKvarHOLFinite kind name value { state with code := c } =
        { setKvarHOLFinite kind name value state with
          code := c } := by
    cases kind <;> rfl
  · rw [evaluateHOLFiniteState_assign] at heval ⊢
    rw [he]
    cases hv : @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) expression with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some value =>
        simp only [hv] at heval ⊢
        rw [hvalid]
        by_cases hs : isValidValueHOLFinite state kind name value = true
        · simp only [hs, if_true] at heval ⊢
          rw [hset]
          simpa only [Prod.fst, Prod.snd] using congrArg
            (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
              (run.1, { run.2 with code := c })) heval
        · simp only [if_neg hs] at heval ⊢
          simpa only [Prod.fst, Prod.snd] using congrArg
            (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
              (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `Primitive` evaluation, including list and operator failure, commutes with
a code-map update. -/
theorem evaluateCodeUpd_Primitive {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL width))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.primitive name operator arguments : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.primitive name operator arguments : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  have he : @evalListHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments := by
    clear heval
    induction arguments with
    | nil => rfl
    | cons expression rest ih =>
        simp only [evalListHOLExact, ih]
        rw [point]
  have hvalid (value : ValueHOL width) :
      isValidValueHOLFinite { state with code := c } .local name value =
        isValidValueHOLFinite state .local name value := rfl
  have hset (value : ValueHOL width) :
      setVarHOLFinite name value { state with code := c } =
        { setVarHOLFinite name value state with
          code := c } := rfl
  · rw [evaluateHOLFiniteState_primitive] at heval ⊢
    rw [he]
    cases hv : @evalListHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some values =>
        simp only [hv] at heval ⊢
        cases hp : panPrimopHOLExact operator values with
        | none =>
            simp only [hp] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
        | some value =>
            simp only [hp] at heval ⊢
            rw [hvalid]
            by_cases hs : isValidValueHOLFinite state .local name value = true
            · simp only [hs, if_true] at heval ⊢
              rw [hset]
              simpa only [Prod.fst, Prod.snd] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := c })) heval
            · simp only [if_neg hs] at heval ⊢
              simpa only [Prod.fst, Prod.snd] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `Store` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Store {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (destination source : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.store destination source : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.store destination source : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  · rw [evaluateHOLFiniteState_store] at heval ⊢
    rw [point destination]
    cases hd : @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) destination with
    | none =>
        simp only [hd] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some destinationValue =>
        cases destinationValue with
        | val payload =>
            cases payload with
            | word address =>
                simp only [hd] at heval ⊢
                rw [point source]
                cases hs : @evalHOLExact width σ _ state.toExact
                    (fun address => Classical.propDecidable (state.memaddrs address)) source with
                | none =>
                    simp only [hs] at heval ⊢
                    simpa only [Prod.fst, Prod.snd] using congrArg
                      (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                        (run.1, { run.2 with code := c })) heval
                | some value =>
                    simp only [hs] at heval ⊢
                    cases hm : @panMemStoresHOL width _ address (flattenHOL value) state.memaddrs
                        (fun address => Classical.propDecidable (state.memaddrs address)) state.memory with
                    | none =>
                        simp only [hm] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := c })) heval
                    | some memory =>
                        simp only [hm] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := c })) heval
        | rStruct _ | nStruct _ _ =>
            simp only [hd] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `Store32` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Store32 {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (destination source : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.store32 destination source : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.store32 destination source : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  · rw [evaluateHOLFiniteState_store32] at heval ⊢
    rw [point destination]
    cases hd : @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) destination with
    | none =>
        simp only [hd] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some destinationValue =>
        cases destinationValue with
        | val payload =>
            cases payload with
            | word address =>
                simp only [hd] at heval ⊢
                rw [point source]
                cases hs : @evalHOLExact width σ _ state.toExact
                    (fun address => Classical.propDecidable (state.memaddrs address)) source with
                | none =>
                    simp only [hs] at heval ⊢
                    simpa only [Prod.fst, Prod.snd] using congrArg
                      (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                        (run.1, { run.2 with code := c })) heval
                | some sourceValue =>
                    cases sourceValue with
                    | val sourcePayload =>
                        cases sourcePayload with
                        | word value =>
                            simp only [hs] at heval ⊢
                            cases hm : @panMemStore32HOL width _ state.memory state.memaddrs
                                (fun address => Classical.propDecidable (state.memaddrs address))
                                state.be address (BitVec.ofNat 32 value.toNat) with
                            | none =>
                                simp only [hm] at heval ⊢
                                simpa only [Prod.fst, Prod.snd] using congrArg
                                  (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                                    (run.1, { run.2 with code := c })) heval
                            | some memory =>
                                simp only [hm] at heval ⊢
                                simpa only [Prod.fst, Prod.snd] using congrArg
                                  (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                                    (run.1, { run.2 with code := c })) heval
                    | rStruct _ | nStruct _ _ =>
                        simp only [hs] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := c })) heval
        | rStruct _ | nStruct _ _ =>
            simp only [hd] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `StoreByte` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_StoreByte {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (destination source : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.storeByte destination source : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.storeByte destination source : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  · rw [evaluateHOLFiniteState_storeByte] at heval ⊢
    rw [point destination]
    cases hd : @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) destination with
    | none =>
        simp only [hd] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some destinationValue =>
        cases destinationValue with
        | val payload =>
            cases payload with
            | word address =>
                simp only [hd] at heval ⊢
                rw [point source]
                cases hs : @evalHOLExact width σ _ state.toExact
                    (fun address => Classical.propDecidable (state.memaddrs address)) source with
                | none =>
                    simp only [hs] at heval ⊢
                    simpa only [Prod.fst, Prod.snd] using congrArg
                      (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                        (run.1, { run.2 with code := c })) heval
                | some sourceValue =>
                    cases sourceValue with
                    | val sourcePayload =>
                        cases sourcePayload with
                        | word value =>
                            simp only [hs] at heval ⊢
                            cases hm : @panMemStoreByteWord8HOL width _ state.memory state.memaddrs
                                (fun address => Classical.propDecidable (state.memaddrs address))
                                state.be address (BitVec.ofNat 8 value.toNat) with
                            | none =>
                                simp only [hm] at heval ⊢
                                simpa only [Prod.fst, Prod.snd] using congrArg
                                  (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                                    (run.1, { run.2 with code := c })) heval
                            | some memory =>
                                simp only [hm] at heval ⊢
                                simpa only [Prod.fst, Prod.snd] using congrArg
                                  (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                                    (run.1, { run.2 with code := c })) heval
                    | rStruct _ | nStruct _ _ =>
                        simp only [hs] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := c })) heval
        | rStruct _ | nStruct _ _ =>
            simp only [hd] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
  all_goals simp



/-- The shared-memory read commutes with an arbitrary updated code
update: it inspects only the shared-memory domain and the FFI, and every branch
preserves the input `code` field. -/
theorem shMemLoadHOLFiniteExact_codeUpd {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) :
    let loaded := @shMemLoadHOLFiniteExact width σ _ state
        (fun current => Classical.propDecidable (state.shMemaddrs current))
        kind name address nb
    @shMemLoadHOLFiniteExact width σ _ { state with code := c }
        (fun current => Classical.propDecidable (state.shMemaddrs current))
        kind name address nb =
      (loaded.1, { loaded.2 with code := c }) := by
  classical
  cases state with
  | mk locals globals structs code0 eshapes memory memaddrs shMemaddrs clock be ffi baseAddr topAddr =>
    dsimp only
    unfold shMemLoadHOLFiniteExact emptyLocalsHOLFinite setKvarFfiHOLFinite
      setKvarHOLFinite setVarHOLFinite setGlobalHOLFinite
    cases hffi : callFFIHOL ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL address false) with
    | final event =>
      by_cases hnb : nb = 0
      · simp only [hnb, if_true]
        by_cases haddr : shMemaddrs address
        · simp only [haddr, if_true]
        · simp only [haddr, if_false]
      · simp only [hnb, if_false]
        by_cases haddr : shMemaddrs (panByteAlignHOL address)
        · simp only [haddr, if_true]
        · simp only [haddr, if_false]
    | ret newFfi newBytes =>
      by_cases hnb : nb = 0
      · simp only [hnb, if_true]
        by_cases haddr : shMemaddrs address
        · simp only [haddr, if_true]
          cases kind <;> rfl
        · simp only [haddr, if_false]
      · simp only [hnb, if_false]
        by_cases haddr : shMemaddrs (panByteAlignHOL address)
        · simp only [haddr, if_true]
          cases kind <;> rfl
        · simp only [haddr, if_false]

set_option backward.isDefEq.respectTransparency false in
/-- `ShMemLoad` evaluation, including the shared-memory FFI outcomes, commutes
with a code-map update. -/
theorem evaluateCodeUpd_ShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state
      (.shMemLoad operator kind name address : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.shMemLoad operator kind name address : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLFinite width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ)
      (fun current => Classical.propDecidable (state.memaddrs current)) expression =
      @evalHOLFinite width σ _ state
      (fun current => Classical.propDecidable (state.memaddrs current)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun current => Classical.propDecidable (state.memaddrs current))
      (c)) expression
  have hlookup :
      lookupKvarHOLFinite kind name
        ({ state with code := c } : PanSemStateFiniteExact width σ) =
      lookupKvarHOLFinite kind name state := by
    cases kind <;> rfl
  · rw [evaluateHOLFiniteState_shMemLoad_source] at heval ⊢
    rw [point, hlookup]
    cases hv : @evalHOLFinite width σ _ state
        (fun current => Classical.propDecidable (state.memaddrs current)) address with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some value =>
        cases value with
        | val payload =>
            cases payload with
            | word addr =>
                simp only [hv] at heval ⊢
                cases hk : lookupKvarHOLFinite kind name state with
                | none =>
                    simp only [hk] at heval ⊢
                    simpa only [Prod.fst, Prod.snd] using congrArg
                      (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                        (run.1, { run.2 with code := c })) heval
                | some kvalue =>
                    cases kvalue with
                    | val kpayload =>
                        cases kpayload with
                        | word _ =>
                            simp only [hk] at heval ⊢
                            rw [shMemLoadHOLFiniteExact_codeUpd c state kind name addr
                              (nbOpHOL operator)]
                            simpa only [Prod.fst, Prod.snd] using congrArg
                              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                                (run.1, { run.2 with code := c })) heval
                    | rStruct fields =>
                        simp only [hk] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := c })) heval
                    | nStruct kname fields =>
                        simp only [hk] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := c })) heval
        | rStruct fields =>
            simp only [hv] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
        | nStruct valueName fields =>
            simp only [hv] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `ShMemStore` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_ShMemStore {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (address value : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.shMemStore operator address value : ProgHOL width) =
      (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.shMemStore operator address value : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  rw [evaluateHOLFiniteState_shMemStore_total]
  rw [evaluateHOLFiniteState_shMemStore_total] at heval
  rw [point address, point value]
  cases ha : @evalHOLExact width σ _ state.toExact
      (fun key => Classical.propDecidable (state.memaddrs key)) address with
  | none =>
      simp only [ha] at heval ⊢
      cases heval
      rfl
  | some av =>
      cases av with
      | rStruct _ | nStruct _ _ =>
          simp only [ha] at heval ⊢
          cases heval
          rfl
      | val aw =>
          cases aw with
          | word addr =>
              cases hv : @evalHOLExact width σ _ state.toExact
                  (fun key => Classical.propDecidable (state.memaddrs key)) value with
              | none =>
                  simp only [ha, hv] at heval ⊢
                  cases heval
                  rfl
              | some vv =>
                  cases vv with
                  | rStruct _ | nStruct _ _ =>
                      simp only [ha, hv] at heval ⊢
                      cases heval
                      rfl
                  | val vw =>
                      cases vw with
                      | word bytes =>
                          simp only [ha, hv] at heval ⊢
                          unfold shMemStoreHOLExact at heval ⊢
                          by_cases hn : nbOpHOL operator = 0
                          · simp only [hn, if_true] at heval ⊢
                            by_cases hd : state.shMemaddrs addr
                            · simp only [hd, if_true] at heval ⊢
                              obtain ⟨outcome, hf⟩ : ∃ outcome, callFFIHOL state.ffi
                                  (.sharedMem .mappedWrite) [BitVec.ofNat 8 0]
                                  (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) =
                                    outcome := ⟨_, rfl⟩
                              cases outcome <;> simp only [hf] at heval ⊢ <;>
                                cases heval <;> cases state <;> rfl
                            · simp only [hd, if_false] at heval ⊢
                              cases heval
                              cases state
                              rfl
                          · simp only [hn, if_false] at heval ⊢
                            by_cases hd : state.shMemaddrs (panByteAlignHOL addr)
                            · simp only [hd, if_true] at heval ⊢
                              obtain ⟨outcome, hf⟩ : ∃ outcome, callFFIHOL state.ffi
                                  (.sharedMem .mappedWrite) [BitVec.ofNat 8 (nbOpHOL operator)]
                                  ((panWordToBytesHOL bytes false).take (nbOpHOL operator) ++
                                    panWordToBytesHOL addr false) = outcome := ⟨_, rfl⟩
                              cases outcome <;> simp only [hf] at heval ⊢ <;>
                                cases heval <;> cases state <;> rfl
                            · simp only [hd, if_false] at heval ⊢
                              cases heval
                              cases state
                              rfl

  all_goals simp


/-- `Return` evaluation commutes with a code-map update. -/
theorem evaluateCodeUpd_Return {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (expression : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.return expression : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.return expression : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have he : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  · rw [evaluateHOLFiniteState_return] at heval ⊢
    rw [he]
    cases hv : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some value =>
        by_cases hs : sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact value) ≤ 32
        · simp only [hv, if_pos hs] at heval ⊢
          simpa only [Prod.fst, Prod.snd, emptyLocalsHOLFinite] using congrArg
            (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
              (run.1, { run.2 with code := c })) heval
        · simp only [hv, if_neg hs] at heval ⊢
          simpa only [Prod.fst, Prod.snd] using congrArg
            (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
              (run.1, { run.2 with code := c })) heval
  all_goals simp

/-- `Raise` evaluation, including its exception-shape guard, commutes with a
code-map update. -/
theorem evaluateCodeUpd_Raise {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (exceptionId : MlS)
    (expression : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.raise exceptionId expression : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := c }
      (.raise exceptionId expression : ProgHOL width) =
      (res, { post with code := c }) := by
  classical
  have he : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  · rw [evaluateHOLFiniteState_raise] at heval ⊢
    rw [he]
    cases hshape : state.eshapes.lookup exceptionId with
    | none =>
        simp only [hshape] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := c })) heval
    | some shape =>
        cases hv : @evalHOLExact width σ _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
        | none =>
            simp only [hshape, hv] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := c })) heval
        | some value =>
            by_cases hc : shapeOfHOLExact value = shape ∧
              sizeOfShapeWithContextHOL state.structs (shapeOfHOLExact value) ≤ 32
            · simp only [hshape, hv, if_pos hc] at heval ⊢
              simpa only [Prod.fst, Prod.snd, emptyLocalsHOLFinite] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := c })) heval
            · simp only [hshape, hv, if_neg hc] at heval ⊢
              simpa only [Prod.fst, Prod.snd] using congrArg
                (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                  (run.1, { run.2 with code := c })) heval
  all_goals simp


/-- `ExtCall` evaluation, including the FFI outcomes, commutes with a code-map
update. -/
theorem evaluateCodeUpd_ExtCall {width : Nat} {σ : Type} [NeZero width]
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (state : PanSemStateFiniteExact width σ)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state
      (.extCall function configuration configurationLength array arrayLength) = (res,post)) :
    evaluateHOLFiniteState {state with code := c}
      (.extCall function configuration configurationLength array arrayLength) =
      (res,{post with code := c}) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := c } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (c)) expression
  have mapped := congrArg
    (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
      (run.1,{run.2 with code := c})) heval
  rw [evaluateHOLFiniteState_extCall_source]
  rw [evaluateHOLFiniteState_extCall_source] at mapped
  simp only [evalHOLFinite] at mapped ⊢
  rw [point configuration,point configurationLength,point array,point arrayLength]
  repeat' split <;> simp_all only []
  all_goals simpa only [emptyLocalsHOLFinite,ofExact] using mapped


end Flapjack
