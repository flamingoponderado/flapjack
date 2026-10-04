import Flapjack.Compiler.Backend.Semantics.WordSem.Props.InstConst
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.FfiHOL

/-!
# WordSem FFI event-prefix support

This is proof-side infrastructure for the exact HOL
`wordPropsScript.sml:evaluate_io_events_mono` port.  It records the local
shared-memory and external-call facts needed by the evaluator induction; the
tagged theorem itself will live under this WordSem counterpart module. -/

namespace Flapjack

namespace WordSemStateFiniteExact

private theorem shMemStore_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStore (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain address
  · simp only [shMemStore, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [0]
        (panWordToBytesHOL value false ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [0]
          (panWordToBytesHOL value false ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStore, hdom]

private theorem shMemStoreByte_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStoreByte (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [shMemStoreByte, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [1]
        ([getByteHOL8 0 value false] ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [1]
          ([getByteHOL8 0 value false] ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStoreByte, hdom]

private theorem shMemStore16_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStore16 (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [shMemStore16, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [2]
        ((panWordToBytesHOL value false).take 2 ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [2]
          ((panWordToBytesHOL value false).take 2 ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStore16, hdom]

private theorem shMemStore32_ioEvents_prefix {width : Nat} [NeZero width]
    {rw : Nat} [NeZero rw] {C F : Type} (address value : BitVec width)
    (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shMemStore32 (rw := rw) address value state).2.ffi.ioEvents := by
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [shMemStore32, if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedWrite) [4]
        ((panWordToBytesHOL value false).take 4 ++ panWordToBytesHOL address false) with
    | final _ => simp [flushState]
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedWrite) [4]
          ((panWordToBytesHOL value false).take 4 ++ panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [shMemStore32, hdom]

private theorem shMemLoad_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoad address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoad
  by_cases hdom : state.shMdomain address
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [0]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [0] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemLoadByte_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoadByte address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoadByte
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [1]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [1] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemLoad16_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoad16 address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoad16
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [2]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [2] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemLoad32_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+:
      (match shMemLoad32 address state with
       | none => state.ffi.ioEvents
       | some (.final _) => state.ffi.ioEvents
       | some (.ret nextFfi _) => nextFfi.ioEvents) := by
  unfold shMemLoad32
  by_cases hdom : state.shMdomain (riscvByteAlignHOL address)
  · simp only [if_pos hdom]
    cases hcall : callFFIHOL state.ffi (.sharedMem .mappedRead) [4]
        (panWordToBytesHOL address false) with
    | final _ => exact List.prefix_refl _
    | ret nextFfi bytes =>
        simpa using callFFIHOL_return_ioEvents_prefix state.ffi
          (.sharedMem .mappedRead) [4] (panWordToBytesHOL address false)
          nextFfi bytes hcall
  · simp [hdom]

private theorem shMemSetVar_ioEvents_prefix {width rw : Nat} [NeZero width]
    [NeZero rw] {C F : Type} (result : Option (HolFfiResult F)) (v : Nat)
    (state : WordSemStateFiniteExact width C F)
    (hret : ∀ nextFfi bytes, result = some (.ret nextFfi bytes) →
      state.ffi.ioEvents <+: nextFfi.ioEvents) :
    state.ffi.ioEvents <+: (shMemSetVar (rw := rw) result v state).2.ffi.ioEvents := by
  cases result with
  | none => exact List.prefix_refl _
  | some result =>
      cases result with
      | final outcome => exact List.prefix_refl _
      | ret nextFfi bytes =>
          simpa [shMemSetVar, setVar] using hret nextFfi bytes rfl

private theorem shareInst_ioEvents_prefix {width rw : Nat} [NeZero width]
    [NeZero rw] {C F : Type} (operator : WordMemOp) (v : Nat)
    (address : BitVec width) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (shareInst (rw := rw) operator v address state).2.ffi.ioEvents := by
  cases operator with
  | load =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoad_ioEvents_prefix address state
      rw [show shMemLoad address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | load8 =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoadByte_ioEvents_prefix address state
      rw [show shMemLoadByte address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | load16 =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoad16_ioEvents_prefix address state
      rw [show shMemLoad16 address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | load32 =>
      simp only [shareInst]
      apply shMemSetVar_ioEvents_prefix (rw := rw) (v := v)
      intro nextFfi bytes hret
      have hload := shMemLoad32_ioEvents_prefix address state
      rw [show shMemLoad32 address state = some (.ret nextFfi bytes) from hret] at hload
      exact hload
  | store =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStore_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp
  | store8 =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStoreByte_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp
  | store16 =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStore16_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp
  | store32 =>
      simp only [shareInst]
      cases hvar : getVar v state with
      | none => simp
      | some value =>
          cases value with
          | word w => simpa [hvar] using shMemStore32_ioEvents_prefix (rw := rw) address w state
          | loc _ _ => simp

private theorem cutState_ioEvents_eq {width : Nat} [NeZero width]
    {C F : Type} {names : WordLangCutsetsHOL}
    {state next : WordSemStateFiniteExact width C F}
    (h : cutState names state = some next) : next.ffi.ioEvents = state.ffi.ioEvents := by
  unfold cutState at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    cases h
    rfl

private theorem memStore_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (address : BitVec width) (value : WordLocW width)
    (state : WordSemStateFiniteExact width C F) :
    (memStore address value state).map (fun next => next.ffi.ioEvents) =
      (memStore address value state).map (fun _ => state.ffi.ioEvents) := by
  unfold memStore
  split <;> rfl

/-- Flapjack-specific projection lemma: successful exact instructions preserve
    the FFI field. This supplies the Inst leaf of the event-prefix induction;
    it is not a separate HOL declaration port. -/
private theorem inst_ffi_of_some {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (state next : WordSemStateFiniteExact width C F)
    (h : inst i state = some next) : next.ffi = state.ffi := by
  exact (instConst i state next h).2

private theorem jumpExc_ioEvents_eq_of_some {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (h : jumpExc state = some (next, l1, l2)) :
    next.ffi.ioEvents = state.ffi.ioEvents := by
  unfold jumpExc at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

private theorem gc_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F)
    (h : gc state = some next) : next.ffi.ioEvents = state.ffi.ioEvents := by
  simp only [gc] at h
  cases hfun : state.gcFun
      (wordSemEncStack state.stack, state.memory, state.mdomain, state.store) with
  | none => simp [hfun] at h
  | some result =>
      obtain ⟨wl, memory, store⟩ := result
      cases hdec : wordSemDecStack wl state.stack with
      | none => simp [hfun, hdec] at h
      | some stack =>
          simp only [hfun, hdec, Option.some.injEq] at h
          cases h
          rfl

private theorem popEnv_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F)
    (h : popEnv state = some next) : next.ffi.ioEvents = state.ffi.ioEvents := by
  cases hstack : state.stack with
  | nil => simp [popEnv, hstack] at h
  | cons frame frames =>
      cases frame with
      | stackFrame localsSize locals0 locals handler =>
          cases handler with
          | none =>
              simp [popEnv, hstack] at h
              cases h
              rfl
          | some handler =>
              simp [popEnv, hstack] at h
              cases h
              rfl

private theorem alloc_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (w : BitVec width) (names : WordLangCutsetsHOL)
    (state : WordSemStateFiniteExact width C F) :
    (alloc w names state).2.ffi.ioEvents = state.ffi.ioEvents := by
  unfold alloc
  split
  · simp [flushState]
  · rename_i envs hcut
    cases hgc : gc (pushEnv envs none (setStore .allocSize (.word w) state)) with
    | none => simp [flushState]
    | some g =>
      have hg := gc_ioEvents_eq _ _ hgc
      have hgin : (pushEnv envs none (setStore .allocSize (.word w) state)).ffi.ioEvents =
          state.ffi.ioEvents := rfl
      rw [hgin] at hg
      cases hp : popEnv g with
      | none => simp [hp, hg, flushState]
      | some p =>
        have hpop := popEnv_ioEvents_eq _ _ hp
        rw [hg] at hpop
        cases hstore : getStore .allocSize p with
        | none => simp [hp, hstore, hpop]
        | some space =>
          cases hspace : hasSpace space p with
          | none => simp [hp, hstore, hspace, hpop]
          | some fits => cases fits <;> simp [hp, hstore, hspace, hpop, flushState]

private theorem ffiStatement_ioEvents_prefix {width : Nat} [NeZero width]
    {C F : Type} (ffiIndex : Flapjack.Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (evaluate (.ffi ffiIndex ptr1 len1 ptr2 len2 names) state).2.ffi.ioEvents := by
  unfold evaluate
  repeat' split
  all_goals (try exact List.prefix_refl _)
  all_goals
    first
    | exact callFFIHOL_result_ioEvents_prefix _ _ _ _ _ (by assumption)
    | (rename_i hcall; exact callFFIHOL_result_ioEvents_prefix _ _ _ _ _ hcall)

/-- Flapjack-specific projection form of the Inst induction leaf. -/
private theorem instStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (evaluate (.inst i) state).2.ffi.ioEvents := by
  rw [evaluate]
  cases hi : inst i state with
  | none => exact List.prefix_refl _
  | some next =>
      have hffi := inst_ffi_of_some i state next hi
      simpa only [hffi] using List.prefix_refl state.ffi.ioEvents

/-- Flapjack-specific projection form of the Seq induction clause. Its two
    premises are exactly the recursive event-prefix induction hypotheses. -/
private theorem seqStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (hfirst : state.ffi.ioEvents <+: (evaluate c1 state).2.ffi.ioEvents)
    (hsecond : ∀ res next, evaluate c1 state = (res, next) → res = none →
      next.ffi.ioEvents <+: (evaluate c2 next).2.ffi.ioEvents) :
    state.ffi.ioEvents <+: (evaluate (.seq c1 c2) state).2.ffi.ioEvents := by
  rw [evaluate, fix_clock_evaluate]
  cases hstep : evaluate c1 state with
  | mk result next =>
      rw [hstep] at hfirst
      cases result with
      | none => exact hfirst.trans (hsecond none next hstep rfl)
      | some result => exact hfirst

/-- Flapjack-specific projection form of the Loop induction clause. The body
    and recursive-loop premises retain the exact evaluator's cut and clock
    side conditions; cut-state representation changes do not alter FFI events. -/
private theorem loopStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F)
    (hbody : ∀ v, cutState (names, .ln) state = some v →
      v.ffi.ioEvents <+: (evaluate body v).2.ffi.ioEvents)
    (hrecur : ∀ v res next, cutState (names, .ln) state = some v →
      evaluate body v = (res, next) → wordSemContLoop res = true → next.clock ≠ 0 →
      (decClock next).ffi.ioEvents <+:
        (evaluate (wordSemSTOP (.loop names body exitNames)) (decClock next)).2.ffi.ioEvents) :
    state.ffi.ioEvents <+: (evaluate (.loop names body exitNames) state).2.ffi.ioEvents := by
  rw [evaluate]
  cases hcut : cutState (names, .ln) state with
  | none => exact List.prefix_refl _
  | some v =>
      dsimp only
      rw [fix_clock_evaluate]
      have hfirst := hbody v hcut
      have hsame := cutState_ioEvents_eq hcut
      rw [hsame] at hfirst
      cases hstep : evaluate body v with
      | mk result next =>
          dsimp only
          rw [hstep] at hfirst
          by_cases hcont : wordSemContLoop result = true
          · simp only [if_pos hcont]
            by_cases hz : next.clock = 0
            · simpa only [hz, ↓reduceDIte, flushState] using hfirst
            · simp only [hz, ↓reduceDIte]
              exact hfirst.trans (hrecur v result next hcut hstep hcont hz)
          · simp only [if_neg hcont]
            repeat' split
            all_goals first
              | exact hfirst
              | (have hsame := cutState_ioEvents_eq ‹cutState _ next = some _›
                 rw [hsame]; exact hfirst)

/-- Flapjack-specific FFI projection of the exact frame push. -/
private theorem pushEnv_ffi {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (state : WordSemStateFiniteExact width C F) :
    (pushEnv envs handler state).ffi = state.ffi := by
  cases handler with
  | none => rfl
  | some value => obtain ⟨n, prog, l1, l2⟩ := value; rfl

/-- Flapjack-specific returning-Call prefix composition. The callee and
    continuation premises are the normalized recursive induction hypotheses,
    with the exact code lookup, return-location, environment and clock guards. -/
private theorem returningCallStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (n : List Nat) (names : WordLangCutsetsHOL) (retHandler : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (state : WordSemStateFiniteExact width C F) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hg : getVars args state = some xs) (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hf : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs)
      state.code state.stackSize = some (args1, prog, ss))
    (hnames : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup))
    (henvs : wordSemCutEnvs names state.locals = some envs) (hz : state.clock ≠ 0)
    (hcallee : (callEnv args1 ss (pushEnv envs handler (decClock state))).ffi.ioEvents <+:
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock state)))).2.ffi.ioEvents)
    (hreturn : ∀ x ys t popped,
      evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock state))) =
        (some (.result x ys), t) →
      ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) → popEnv t = some popped →
      sptDomainEqUnion popped.locals envs.1 envs.2 →
      popped.ffi.ioEvents <+: (evaluate retHandler (setVars n ys popped)).2.ffi.ioEvents)
    (hexception : ∀ x y t n' hprog l1' l2',
      evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock state))) =
        (some (.exception x y), t) →
      handler = some (n', hprog, l1', l2') → x = .loc l1' l2' →
      sptDomainEqUnion t.locals envs.1 envs.2 →
      t.ffi.ioEvents <+: (evaluate hprog (setVar n' y t)).2.ffi.ioEvents) :
    state.ffi.ioEvents <+:
      (evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler) state).2.ffi.ioEvents := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hnames, henvs, hz]
  have hstart : (callEnv args1 ss (pushEnv envs handler (decClock state))).ffi.ioEvents =
      state.ffi.ioEvents := by
    change (pushEnv envs handler (decClock state)).ffi.ioEvents = state.ffi.ioEvents
    rw [pushEnv_ffi]
    rfl
  rw [hstart] at hcallee
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock state))) with ⟨rc, t⟩
  rw [hcv] at hcallee
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · exact hcallee
  · simp only
    split
    · exact hcallee
    · rename_i hvalid
      cases hp : popEnv t with
      | none => exact hcallee
      | some popped =>
          dsimp only
          have hevents := popEnv_ioEvents_eq t popped hp
          split
          · rename_i hdom
            have hnext := hreturn x ys t popped hcv hvalid hp hdom
            rw [hevents] at hnext
            exact hcallee.trans hnext
          · simpa only [hevents] using hcallee
  · cases hh : handler with
    | none => exact hcallee
    | some hv =>
        obtain ⟨n', hprog, l1', l2'⟩ := hv
        dsimp only
        split
        · exact hcallee
        · rename_i hloc
          split
          · rename_i hdom
            exact hcallee.trans (hexception x y t n' hprog l1' l2' hcv hh
              (Classical.byContradiction hloc) hdom)
          · exact hcallee
  all_goals exact hcallee

/-- Flapjack-specific tail-Call induction clause. Both successful return and
    bad-return rejection retain the callee's FFI events. -/
private theorem tailCallStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat) (state : WordSemStateFiniteExact width C F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (hg : getVars args state = some xs) (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) state.code state.stackSize =
      some (args1, prog, ss)) (hz : state.clock ≠ 0)
    (hcallee : (callEnv args1 ss (decClock state)).ffi.ioEvents <+:
      (evaluate prog (callEnv args1 ss (decClock state))).2.ffi.ioEvents) :
    state.ffi.ioEvents <+: (evaluate (.call none dest args none) state).2.ffi.ioEvents := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hz]
  rcases hcv : evaluate prog (callEnv args1 ss (decClock state)) with ⟨result, next⟩
  rw [hcv] at hcallee
  split <;> exact hcallee

/-- Flapjack-specific Store leaf: both rejection and successful memory updates
    preserve the FFI event sequence. -/
private theorem storeStatement_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (exp : WordLangExpHOL (BitVec width)) (v : Nat)
    (state : WordSemStateFiniteExact width C F) :
    (evaluate (.store exp v) state).2.ffi.ioEvents = state.ffi.ioEvents := by
  rw [evaluate]
  repeat' split
  all_goals first
    | rfl
    | (rename_i hmem
       unfold memStore at hmem
       split at hmem <;> cases hmem <;> rfl)

/-- Flapjack-specific Raise leaf, including the successful exception jump. -/
private theorem raiseStatement_ioEvents_eq {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (state : WordSemStateFiniteExact width C F) :
    (evaluate (.raise n) state).2.ffi.ioEvents = state.ffi.ioEvents := by
  rw [evaluate]
  repeat' split
  all_goals first
    | rfl
    | exact jumpExc_ioEvents_eq_of_some _ _ _ _ ‹jumpExc _ = some _›

/-- Flapjack-specific MustTerminate induction clause: timeout restores the
    input state, and all other results retain the body's FFI events. -/
private theorem mustTerminateStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (hbody : state.termdep ≠ 0 →
      state.ffi.ioEvents <+: (evaluate body
        { state with clock := wordSemMustTerminateLimit width, termdep := state.termdep - 1 }).2.ffi.ioEvents) :
    state.ffi.ioEvents <+: (evaluate (.mustTerminate body) state).2.ffi.ioEvents := by
  rw [evaluate]
  split
  · exact List.prefix_refl _
  · rename_i hdep
    have hprefix := hbody hdep
    cases hstep : evaluate body
        { state with clock := wordSemMustTerminateLimit width, termdep := state.termdep - 1 } with
    | mk result next =>
        rw [hstep] at hprefix
        dsimp only
        repeat' split
        all_goals first | exact List.prefix_refl _ | exact hprefix

/-- Flapjack-specific If induction clause with exactly the successful operand
    lookup and comparison guards of the evaluator. -/
private theorem ifStatement_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width))
    (c1 c2 : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (htrue : ∀ x y, getVar r1 state = some x → getVarImm ri state = some y →
      wordSemWordCmp cmp x y = some true →
      state.ffi.ioEvents <+: (evaluate c1 state).2.ffi.ioEvents)
    (hfalse : ∀ x y, getVar r1 state = some x → getVarImm ri state = some y →
      wordSemWordCmp cmp x y = some false →
      state.ffi.ioEvents <+: (evaluate c2 state).2.ffi.ioEvents) :
    state.ffi.ioEvents <+: (evaluate (.ite cmp r1 ri c1 c2) state).2.ffi.ioEvents := by
  rw [evaluate]
  repeat' split
  all_goals first
    | exact List.prefix_refl _
    | exact htrue _ _ ‹getVar _ _ = some _› ‹getVarImm _ _ = some _› ‹wordSemWordCmp _ _ _ = some true›
    | exact hfalse _ _ ‹getVar _ _ = some _› ‹getVarImm _ _ = some _› ‹wordSemWordCmp _ _ _ = some false›

/-- Flapjack-specific projection form used to assemble the exact HOL evaluator
    theorem below; this helper is not a separate HOL declaration. -/
theorem evaluate_ioEvents_prefix {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F) :
    state.ffi.ioEvents <+: (evaluate p state).2.ffi.ioEvents := by
  apply evaluate_ind (fun p state => state.ffi.ioEvents <+: (evaluate p state).2.ffi.ioEvents) ?_ p state
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; rw [evaluate]; exact List.prefix_refl _
  · intro n names s
    rw [evaluate]
    repeat' split
    all_goals first
      | exact List.prefix_refl _
      | (rw [alloc_ioEvents_eq]; exact List.prefix_refl _)
  · intro t1 t2 addr offset words s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro pri moves s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · exact instStatement_ioEvents_prefix
  · intro v exp s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro v name s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro v exp s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro b dst src s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro exp v s
    rw [storeStatement_ioEvents_eq]; exact List.prefix_refl _
  · intro s
    rw [evaluate]
    split <;> exact List.prefix_refl _
  · exact mustTerminateStatement_ioEvents_prefix
  · intro c1 c2 s ih
    exact seqStatement_ioEvents_prefix c1 c2 s ih.2
      (fun res next heval hnone => ih.1 res next ⟨heval.symm, hnone⟩)
  · intro n ms s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro n s
    rw [raiseStatement_ioEvents_eq]; exact List.prefix_refl _
  · intro k s; rw [evaluate]; exact List.prefix_refl _
  · intro k s; rw [evaluate]; exact List.prefix_refl _
  · intro cmp r1 ri c1 c2 s ih
    apply ifStatement_ioEvents_prefix
    · intro x y hx hy hc
      exact ih.1 (some x) (some y) x y true ⟨by rw [hx, hy], rfl, rfl, hc, rfl⟩
    · intro x y hx hy hc
      exact ih.2 (some x) (some y) x y false ⟨by rw [hx, hy], rfl, rfl, hc, Bool.noConfusion⟩
  · intro names body exitNames s ih
    exact loopStatement_ioEvents_prefix names exitNames body s ih.2
      (fun v res next hcut heval hcont hz => ih.1 v res next ⟨hcut, heval.symm, hcont, hz⟩)
  · intro r l1 s
    rw [evaluate]
    split <;> exact List.prefix_refl _
  · intro ptr len dptr dlen names s
    rw [evaluate]
    repeat' split
    all_goals dsimp only
    all_goals repeat' split
    all_goals exact List.prefix_refl _
  · intro r1 r2 s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · intro r1 r2 s
    rw [evaluate]
    repeat' split
    all_goals exact List.prefix_refl _
  · exact ffiStatement_ioEvents_prefix
  · intro op v exp s
    rw [evaluate]
    repeat' split
    all_goals first
      | exact List.prefix_refl _
      | exact shareInst_ioEvents_prefix _ _ _ _
  · intro ret dest args handler s ih
    rcases ih with ⟨hreturn, hexception, hcallee, htail⟩
    have hcall := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    cases hg : getVars args s with
    | none => rw [hcall]; simp only [hg]; exact List.prefix_refl _
    | some xs =>
      by_cases hbad : wordSemBadDestArgs dest args = true
      · rw [hcall]; simp only [hg, hbad, ↓reduceIte]; exact List.prefix_refl _
      · cases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        | none =>
          rw [hcall]; simp only [hg, hbad, hf]; exact List.prefix_refl _
        | some triple =>
          obtain ⟨args1, prog, ss⟩ := triple
          cases ret with
          | none =>
            cases handler with
            | some handler =>
              rw [hcall]; simp only [hg, hbad, hf]; exact List.prefix_refl _
            | none =>
              by_cases hz : s.clock = 0
              · rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hz]; exact List.prefix_refl _
              · apply tailCallStatement_ioEvents_prefix dest args s xs args1 prog ss hg hbad hf hz
                exact htail xs (args1, prog, ss) args1 (prog, ss) prog ss
                  ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, hz⟩
          | some ret =>
            obtain ⟨n, names, retHandler, l1, l2⟩ := ret
            by_cases hnames : sptDomainEmpty names.1 ∨ ¬ n.Nodup
            · rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hnames]; exact List.prefix_refl _
            · cases he : wordSemCutEnvs names s.locals with
              | none =>
                rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hnames, he]; exact List.prefix_refl _
              | some envs =>
                by_cases hz : s.clock = 0
                · rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hnames, he, hz]
                  exact List.prefix_refl _
                · apply returningCallStatement_ioEvents_prefix n names retHandler l1 l2 dest args handler
                    s xs args1 prog ss envs hg hbad hf hnames he hz
                  · exact hcallee xs (args1, prog, ss) args1 (prog, ss) prog ss
                      (n, names, retHandler, l1, l2) n (names, retHandler, l1, l2) names
                      (retHandler, l1, l2) retHandler (l1, l2) l1 l2 envs
                      ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz⟩
                  · intro x ys t popped hev hv hp hd
                    exact hreturn xs (args1, prog, ss) args1 (prog, ss) prog ss
                      (n, names, retHandler, l1, l2) n (names, retHandler, l1, l2) names
                      (retHandler, l1, l2) retHandler (l1, l2) l1 l2 envs
                      (some (.result x ys)) t (.result x ys) x ys popped
                      ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz,
                        hev, rfl, rfl, hv, hp, hd⟩
                  · intro x y t n' hprog l1' l2' hev hh hl hd
                    exact hexception xs (args1, prog, ss) args1 (prog, ss) prog ss
                      (n, names, retHandler, l1, l2) n (names, retHandler, l1, l2) names
                      (retHandler, l1, l2) retHandler (l1, l2) l1 l2 envs
                      (some (.exception x y)) t (.exception x y) x y
                      (n', hprog, l1', l2') n' (hprog, l1', l2') hprog (l1', l2') l1' l2'
                      ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz,
                        hev, rfl, rfl, hh, rfl, rfl, rfl, hl, hd⟩

end WordSemStateFiniteExact

end Flapjack
