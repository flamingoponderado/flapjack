import Flapjack.Compiler.Backend.WordRemove.Proofs.CompileState
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts

/-!
# `word_removeProof`: `word_remove_correct`

Counterpart of `cakeml/compiler/backend/proofs/word_removeProofScript.sml:262-430`:
removing `MustTerminate` preserves the exact wordSem semantics, for some
added clock, on the `compile_state` image of the source state.
-/

namespace Flapjack.Compiler.Backend.WordRemove

open Flapjack Flapjack.WordSemStateFiniteExact

namespace WordRemoveCorrectSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordRemoveCorrectSupport

section Frame

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

@[simp] private theorem cs_locals (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).locals = s.locals := rfl
@[simp] private theorem cs_memory (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).memory = s.memory := rfl
@[simp] private theorem cs_mdomain (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).mdomain = s.mdomain := rfl
@[simp] private theorem cs_shMdomain (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).shMdomain = s.shMdomain := rfl
@[simp] private theorem cs_be (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).be = s.be := rfl
@[simp] private theorem cs_ffi (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).ffi = s.ffi := rfl
@[simp] private theorem cs_codeBuffer (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).codeBuffer = s.codeBuffer := rfl
@[simp] private theorem cs_dataBuffer (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).dataBuffer = s.dataBuffer := rfl
@[simp] private theorem cs_store (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).store = s.store := rfl
@[simp] private theorem cs_fpRegs (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).fpRegs = s.fpRegs := rfl
@[simp] private theorem cs_stack (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).stack = s.stack := rfl
@[simp] private theorem cs_handler (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).handler = s.handler := rfl
@[simp] private theorem cs_stackSize (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : (compileState clk c s).stackSize = s.stackSize := rfl

private theorem cs_code (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    (compileState clk c s).code = sptMap (fun p => (p.1, removeMustTerminate p.2)) s.code := rfl

private theorem cs_sptMem_code (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) (l : Nat) :
    sptMem l (compileState clk c s).code = sptMem l s.code := by
  show sptDomain (sptMap _ s.code) l = sptDomain s.code l
  rw [sptDomain_sptMap]

private theorem shMemSetVar_compileState (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) (res : Option (HolFfiResult F)) (v : Nat) :
    shMemSetVar (rw := width) res v (compileState clk c s) =
      ((shMemSetVar (rw := width) res v s).1,
        compileState clk c (shMemSetVar (rw := width) res v s).2) := by
  cases res with
  | none => rfl
  | some r => cases r <;> rfl

private theorem shMemStore_compileState {rw : Nat} [NeZero rw] (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) (a w : BitVec width) :
    shMemStore (rw := rw) a w (compileState clk c s) =
      ((shMemStore (rw := rw) a w s).1, compileState clk c (shMemStore (rw := rw) a w s).2) := by
  unfold shMemStore
  by_cases h : s.shMdomain a = true
  · simp only [cs_shMdomain, cs_ffi, h, if_true]
    cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [0] (panWordToBytesHOL w false ++ panWordToBytesHOL a false) <;> rfl
  · simp only [cs_shMdomain, h, Bool.false_eq_true, if_false]

private theorem shMemStoreByte_compileState {rw : Nat} [NeZero rw] (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) (a w : BitVec width) :
    shMemStoreByte (rw := rw) a w (compileState clk c s) =
      ((shMemStoreByte (rw := rw) a w s).1, compileState clk c (shMemStoreByte (rw := rw) a w s).2) := by
  unfold shMemStoreByte
  by_cases h : s.shMdomain (riscvByteAlignHOL a) = true
  · simp only [cs_shMdomain, cs_ffi, h, if_true]
    cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [1] ([getByteHOL8 0 w false] ++ panWordToBytesHOL a false) <;> rfl
  · simp only [cs_shMdomain, h, Bool.false_eq_true, if_false]

private theorem shMemStore16_compileState {rw : Nat} [NeZero rw] (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) (a w : BitVec width) :
    shMemStore16 (rw := rw) a w (compileState clk c s) =
      ((shMemStore16 (rw := rw) a w s).1, compileState clk c (shMemStore16 (rw := rw) a w s).2) := by
  unfold shMemStore16
  by_cases h : s.shMdomain (riscvByteAlignHOL a) = true
  · simp only [cs_shMdomain, cs_ffi, h, if_true]
    cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [2] ((panWordToBytesHOL w false).take 2 ++ panWordToBytesHOL a false) <;> rfl
  · simp only [cs_shMdomain, h, Bool.false_eq_true, if_false]

private theorem shMemStore32_compileState {rw : Nat} [NeZero rw] (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) (a w : BitVec width) :
    shMemStore32 (rw := rw) a w (compileState clk c s) =
      ((shMemStore32 (rw := rw) a w s).1, compileState clk c (shMemStore32 (rw := rw) a w s).2) := by
  unfold shMemStore32
  by_cases h : s.shMdomain (riscvByteAlignHOL a) = true
  · simp only [cs_shMdomain, cs_ffi, h, if_true]
    cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [4] ((panWordToBytesHOL w false).take 4 ++ panWordToBytesHOL a false) <;> rfl
  · simp only [cs_shMdomain, h, Bool.false_eq_true, if_false]

set_option linter.unusedSimpArgs false in
private theorem shareInst_compileState (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) (op : WordMemOp) (v : Nat) (ad : BitVec width) :
    shareInst (rw := width) op v ad (compileState clk c s) =
      ((shareInst (rw := width) op v ad s).1,
        compileState clk c (shareInst (rw := width) op v ad s).2) := by
  cases op <;> simp only [shareInst, shMemSetVar_compileState] <;>
    simp only [shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore_compileState, shMemStoreByte_compileState, shMemStore16_compileState,
      shMemStore32_compileState, getVar_compileState, cs_shMdomain, cs_ffi] <;>
    (repeat' split) <;> first | rfl | simp_all [flushState, setVar]

set_option linter.unusedSimpArgs false in
/-- Flapjack infrastructure for the clock-constant, non-`Install` cases of `word_remove_correct`
    (HOL discharges them by rewriting with the `compile_state` simp set). -/
theorem evaluate_compileState_frame (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true)
    (hi : ∀ a b d e f, p ≠ .install a b d e f) :
    evaluate p (compileState clk c s) =
      ((evaluate p s).1, compileState clk c (evaluate p s).2) := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;>
    (try exact absurd rfl (hi _ _ _ _ _)) <;>
    rw [evaluate, evaluate] <;>
    simp only [getVar_compileState, getVars_compileState, wordExp_compileState,
      inst_compileState, alloc_compileState, shareInst_compileState, jumpExc_compileState,
      memStore_compileState, getStore_compileState, cs_sptMem_code, cs_locals, cs_memory,
      cs_mdomain, cs_be, cs_ffi, cs_codeBuffer, cs_dataBuffer] <;>
    (repeat' split) <;> first | rfl | (simp only [compileState]; done) |
      simp_all [flushState, setVar, setVars, setStore, unsetVar, compileState]

/-- The `Install` case: under HOL's `st.compile` premise the compiled oracle and
    compiler agree, and the installed code commutes with `compile_state`
    (HOL `map_union`, `map_fromAList`). -/
theorem evaluate_install_compileState (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F)
    (hc : s.compile = fun cfg => c cfg ∘ List.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2)))
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL) :
    evaluate (.install ptr len dptr dlen names) (compileState clk c s) =
      ((evaluate (.install ptr len dptr dlen names) s).1,
        compileState clk c (evaluate (.install ptr len dptr dlen names) s).2) := by
  rcases hR : evaluate (.install ptr len dptr dlen names) s with ⟨r, s'⟩
  dsimp only
  obtain ⟨locals, localsSize, fpRegs, store, stack, stackLimit, stackMax, stackSize, memory,
    mdomain, shMdomain, permute, compile, oracle, codeBuffer, dataBuffer, gcFun, handler, clock,
    termdep, code, be, ffi⟩ := s
  rw [evaluate] at hR ⊢
  dsimp only [compileState] at hc hR ⊢
  subst hc
  simp only [getVar, Function.comp] at hR ⊢
  rcases hce : wordSemCutEnv names locals with _ | env <;> simp only [hce] at hR ⊢
  · cases hR; rfl
  rcases h1 : sptLookup ptr locals with _ | (w1 | ⟨_, _⟩) <;> simp only [h1] at hR ⊢ <;>
    try (cases hR; rfl)
  rcases h2 : sptLookup len locals with _ | (w2 | ⟨_, _⟩) <;> simp only [h2] at hR ⊢ <;>
    try (cases hR; rfl)
  rcases h3 : sptLookup dptr locals with _ | (w3 | ⟨_, _⟩) <;> simp only [h3] at hR ⊢ <;>
    try (cases hR; rfl)
  rcases h4 : sptLookup dlen locals with _ | (w4 | ⟨_, _⟩) <;> simp only [h4] at hR ⊢ <;>
    try (cases hR; rfl)
  rcases hb1 : wordSemBufferFlush codeBuffer w1 w2 with _ | ⟨bytes, cb⟩ <;>
    rcases hb2 : wordSemBufferFlush dataBuffer w3 w4 with _ | ⟨data, db⟩ <;>
    simp only [hb1, hb2] at hR ⊢ <;> try (cases hR; rfl)
  rcases hO : oracle 0 with ⟨cfg, progs⟩
  simp only [hO] at hR ⊢
  rcases hcc : c cfg (List.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2)) progs) with
    _ | ⟨bytes', data', cfg'⟩ <;> simp only [hcc] at hR ⊢
  · cases hR; rfl
  cases progs with
  | nil => simp only [List.map] at hR ⊢; cases hR; rfl
  | cons p tl =>
    obtain ⟨k, n, q⟩ := p
    have hcode : sptUnion (sptMap (fun p => (p.1, removeMustTerminate p.2)) code)
        (sptFromAList (List.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2))
          ((k, n, q) :: tl))) =
        sptMap (fun p => (p.1, removeMustTerminate p.2))
          (sptUnion code (sptFromAList ((k, n, q) :: tl))) := by
      rw [sptMap_sptUnion, sptMap_sptFromAList]
    simp only [List.map] at hR hcode ⊢
    simp only [holShiftSeq] at hR ⊢
    by_cases hC : bytes = bytes' ∧ data = data' ∧ (oracle (0 + 1)).1 = cfg'
    · simp only [hC, and_self, if_true] at hR ⊢
      cases hR
      simp only [hcode]
      rfl
    · simp only [hC, if_false] at hR ⊢
      cases hR; rfl

end Frame


section Correct

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- HOL's `st.compile` premise of `word_remove_correct`. -/
abbrev removeCompileRel (c : WordCompileFn width C) : WordCompileFn width C :=
  fun cfg => c cfg ∘ List.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2))

private theorem cutState_compile (names : WordLangCutsetsHOL)
    (s s1 : WordSemStateFiniteExact width C F) (h : cutState names s = some s1) :
    s1.compile = s.compile := by
  unfold cutState at h
  split at h
  · cases h
  · cases h; rfl

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `word_remove_correct`, by recursion on HOL's
    evaluator measure (Flapjack infrastructure; the tagged statement is
    `word_remove_correct`). -/
theorem word_remove_correct_aux (c : WordCompileFn width C) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
      evaluate prog st = (res, rst) → res ≠ some .error → st.compile = removeCompileRel c →
      ∃ clk, evaluate (removeMustTerminate prog) (compileState clk c st) =
        (res, compileState 0 c rst)
  | .tick, s, r, s', h, hne, hc => by
      refine ⟨0, ?_⟩
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [show removeMustTerminate (WordLangProgHOL.tick : WordLangProgHOL (BitVec width)) =
        .tick from rfl, ht]
      by_cases hz : s.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [if_pos (by simp [compileState, hz]), flushState_compileState]
      · simp only [hz, if_false, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [if_neg (by simp [compileState, hz]), compileState_decClock 0 c s hz]
  | .mustTerminate q, s, r, s', h, hne, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      by_cases hd : s.termdep = 0
      · simp only [hd, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hd, if_false] at h
      rcases hq : evaluate q { s with
          clock := wordSemMustTerminateLimit width
          termdep := s.termdep - 1 } with ⟨r1, s1⟩
      rw [hq] at h
      have key : r1 ≠ some .timeOut ∧ r = r1 ∧
          s' = { s1 with clock := s.clock, termdep := s.termdep } := by
        rcases r1 with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;>
          simp only [Prod.mk.injEq] at h <;>
          first
            | exact absurd h.1.symm hne
            | exact ⟨by simp, h.1.symm, h.2.symm⟩
      obtain ⟨hr1, rfl, rfl⟩ := key
      have hc1 := evaluate_clock q _ r _ hq
      obtain ⟨k, hk⟩ := word_remove_correct_aux c q _ r s1 hq hne hc
      have hdec := evaluate_dec_clock _ _ _ _ hk
      have hadd := evaluate_add_clock s.clock _ _ r _ ⟨hdec, hr1⟩
      refine ⟨k + wordSemMustTerminateLimit width - s1.clock, ?_⟩
      rw [show removeMustTerminate (WordLangProgHOL.mustTerminate q) = removeMustTerminate q
        from rfl]
      simp only [compileState] at hadd hc1 ⊢
      have hst : s.clock + (k + wordSemMustTerminateLimit width - s1.clock) =
          wordSemMustTerminateLimit width + k - (s1.clock + 0) + s.clock := by omega
      rw [hst]
      rw [Nat.zero_add] at hadd
      exact hadd
  | .seq c1 c2, s, r, s', h, hne, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at h
      have hc1 := evaluate_clock c1 s r1 s1 h1
      have hcomp := (evaluate_consts c1 s r1 s1 h1).2.2.2.2.1
      rw [show removeMustTerminate (WordLangProgHOL.seq c1 c2) =
        .seq (removeMustTerminate c1) (removeMustTerminate c2) from rfl]
      cases r1 with
      | none =>
        simp only at h
        obtain ⟨k1, hk1⟩ := word_remove_correct_aux c c1 s none s1 h1 (by simp) hc
        obtain ⟨k2, hk2⟩ := word_remove_correct_aux c c2 s1 r s' h hne (by rw [← hcomp]; exact hc)
        refine ⟨k1 + k2, ?_⟩
        rw [ht, evaluate_add_clock_compileState _ _ _ _ _ _ ⟨hk1, by simp⟩ k2]
        exact hk2
      | some x =>
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨k1, hk1⟩ := word_remove_correct_aux c c1 s (some x) s1 h1 hne hc
        refine ⟨k1, ?_⟩
        rw [ht, hk1]
  | .ite cmp r1 ri c1 c2, s, r, s', h, hne, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [show removeMustTerminate (WordLangProgHOL.ite cmp r1 ri c1 c2) =
        .ite cmp r1 ri (removeMustTerminate c1) (removeMustTerminate c2) from rfl]
      rcases hx : getVar r1 s with _ | x
      · simp only [hx, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      rcases hy : WordSemStateFiniteExact.getVarImm ri s with _ | y
      · simp only [hx, hy, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hx, hy] at h
      rcases hw : wordSemWordCmp cmp x y with _ | (_ | _)
      · simp only [hw, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      · simp only [hw] at h
        obtain ⟨k, hk⟩ := word_remove_correct_aux c c2 s r s' h hne hc
        refine ⟨k, ?_⟩
        rw [ht, getVar_compileState, getVarImm_compileState, hx, hy]
        simp only [hw]
        exact hk
      · simp only [hw] at h
        obtain ⟨k, hk⟩ := word_remove_correct_aux c c1 s r s' h hne hc
        refine ⟨k, ?_⟩
        rw [ht, getVar_compileState, getVarImm_compileState, hx, hy]
        simp only [hw]
        exact hk
  | .loop names body exitNames, s, r, s', h, hne, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [show removeMustTerminate (WordLangProgHOL.loop names body exitNames) =
        .loop names (removeMustTerminate body) exitNames from rfl]
      rcases hcs : cutState (names, .ln) s with _ | x
      · simp only [hcs, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hcs] at h
      have hcx := cutState_clock_termdep _ _ _ hcs
      have hxc : x.compile = removeCompileRel c := by
        rw [cutState_compile _ _ _ hcs]; exact hc
      rcases hb : evaluate body x with ⟨r1, s1⟩
      rw [hb] at h
      have hc1 := evaluate_clock body x r1 s1 hb
      have hcomp := (evaluate_consts body x r1 s1 hb).2.2.2.2.1
      by_cases hcont : wordSemContLoop r1 = true
      · simp only [hcont, if_true] at h
        have hr1 : r1 ≠ some .error ∧ r1 ≠ some .timeOut := by
          constructor <;> rintro rfl <;> simp [wordSemContLoop] at hcont
        obtain ⟨k1, hk1⟩ := word_remove_correct_aux c body x r1 s1 hb hr1.1 hxc
        by_cases hz : s1.clock = 0
        · simp only [hz, if_true, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨k1, ?_⟩
          rw [ht, cutState_compileState, hcs]
          simp only [Option.map_some]
          rw [hk1]
          simp only [hcont, if_true]
          rw [if_pos (by simp [compileState, hz]), flushState_compileState]
        · simp only [hz, if_false] at h
          obtain ⟨k2, hk2⟩ := word_remove_correct_aux c (.loop names body exitNames)
            (decClock s1) r s' h hne (by show s1.compile = _; rw [← hcomp]; exact hxc)
          refine ⟨k1 + k2, ?_⟩
          rw [ht, cutState_compileState, hcs]
          simp only [Option.map_some]
          rw [evaluate_add_clock_compileState _ _ _ _ _ _ ⟨hk1, hr1.2⟩ k2]
          simp only [hcont, if_true]
          rw [if_neg (by simp only [compileState]; omega), ← compileState_decClock k2 c s1 hz]
          exact hk2
      · simp only [hcont, Bool.false_eq_true, if_false] at h
        have hr1 : r1 ≠ some .error := by
          rintro rfl
          simp only [wordSemExitLoop, Prod.mk.injEq] at h
          exact hne h.1.symm
        obtain ⟨k1, hk1⟩ := word_remove_correct_aux c body x r1 s1 hb hr1 hxc
        refine ⟨k1, ?_⟩
        rw [ht, cutState_compileState, hcs]
        simp only [Option.map_some]
        rw [hk1]
        simp only [hcont, Bool.false_eq_true, if_false]
        rcases r1 with _ | ⟨_, _⟩ | ⟨_, _⟩ | (_ | k) | k | _ | _ | _ | _ <;>
          simp only [Prod.mk.injEq] at h <;>
          first
            | (obtain ⟨rfl, rfl⟩ := h; rfl)
            | skip
        rw [cutState_compileState]
        rcases hce : cutState (exitNames, .ln) s1 with _ | s2 <;>
          simp only [hce, Option.map_none, Option.map_some, Prod.mk.injEq] at h ⊢
        · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | .call none dest args handler, s, r, s', h, hne, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht] at h
      rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
      · simp only [hg, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hg] at h
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hbad, Bool.false_eq_true, if_false] at h
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp only [hf, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hf] at h
      cases handler with
      | some hv =>
        simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      | none =>
        simp only at h
        rw [show removeMustTerminate (WordLangProgHOL.call none dest args none) =
          (.call none dest args none : WordLangProgHOL (BitVec width)) from rfl]
        by_cases hz : s.clock = 0
        · simp only [hz, if_true, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨0, ?_⟩
          rw [ht, getVars_compileState, hg]
          simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I, hf,
            Option.map_some]
          rw [if_pos (by simp [compileState, hz]), flushState_compileState]
        · simp only [hz, if_false] at h
          rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with
            ⟨rc, sc⟩
          rw [hcv] at h
          have hc1 := evaluate_clock prog _ rc sc hcv
          by_cases hb : wordSemBadFunReturn rc = true
          · simp only [hb, if_true, Prod.mk.injEq] at h
            exact absurd h.1.symm hne
          simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨k, hk⟩ := word_remove_correct_aux c prog _ _ sc hcv hne hc
          refine ⟨k, ?_⟩
          rw [ht, getVars_compileState, hg]
          simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I, hf,
            Option.map_some]
          rw [if_neg (by simp only [compileState]; omega), ← compileState_decClock k c s hz,
            callEnv_compileState, hk]
          simp only [hb, Bool.false_eq_true, if_false]
  | .call (some (n, names, retHandler, l1, l2)) dest args handler, s, r, s', h, hne, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht] at h
      have hrm : removeMustTerminate
          (WordLangProgHOL.call (some (n, names, retHandler, l1, l2)) dest args handler) =
          .call (some (n, names, removeMustTerminate retHandler, l1, l2)) dest args
            (handler.map (fun hv => (hv.1, removeMustTerminate hv.2.1, hv.2.2.1, hv.2.2.2))) := by
        cases handler with
        | none => rfl
        | some hv => obtain ⟨_, _, _, _⟩ := hv; rfl
      rw [hrm]
      rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
      · simp only [hg, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hg] at h
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hbad, Bool.false_eq_true, if_false] at h
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs)
          s.code s.stackSize with _ | ⟨args1, prog, ss⟩
      · simp only [hf, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hf] at h
      simp only [wordSemAddRetLoc] at hf
      by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
      · simp only [hdc, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hdc, if_false] at h
      rcases hce : wordSemCutEnvs names s.locals with _ | envs
      · simp only [hce, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hce] at h
      have hpm : ∀ (t : WordSemStateFiniteExact width C F),
          pushEnv envs (handler.map (fun hv => (hv.1, removeMustTerminate hv.2.1, hv.2.2.1, hv.2.2.2))) t =
            pushEnv envs handler t := by
        intro t
        cases handler with
        | none => rfl
        | some hv => obtain ⟨_, _, _, _⟩ := hv; rfl
      by_cases hz : s.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, ?_⟩
        rw [ht, getVars_compileState, hg]
        simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I,
          wordSemAddRetLoc, hf, Option.map_some, hdc, cs_locals, hce]
        rw [if_pos (by simp [compileState, hz]), hpm, pushEnv_compileState, callEnv_compileState]
        simp only [compileState, flushState, hz]
      simp only [hz, if_false] at h
      rcases hcv : evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
        ⟨rc, s2⟩
      rw [hcv] at h
      have hc1 := evaluate_clock prog _ rc s2 hcv
      have hTc : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).compile =
          removeCompileRel c := by
        rcases handler with _ | ⟨_, _, _, _⟩ <;> exact hc
      have hcomp := (evaluate_consts prog _ rc s2 hcv).2.2.2.2.1
      have htgt : ∀ k, WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs (handler.map (fun hv => (hv.1, removeMustTerminate hv.2.1, hv.2.2.1, hv.2.2.2)))
            (decClock (compileState k c s))) =
          compileState k c
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) := by
        intro k
        rw [← compileState_decClock k c s hz, hpm, pushEnv_compileState, callEnv_compileState]
      rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
      rotate_left
      · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
        · simp only [hx, if_true, Prod.mk.injEq] at h
          exact absurd h.1.symm hne
        simp only [hx, if_false] at h
        rcases hp : popEnv s2 with _ | s1
        · simp only [hp, Prod.mk.injEq] at h
          exact absurd h.1.symm hne
        simp only [hp] at h
        have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
          ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
        have hs1c : s1.compile = s2.compile := by
          unfold popEnv at hp
          split at hp <;> cases hp <;> rfl
        by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
        · simp only [hdom, if_true] at h
          obtain ⟨k1, hk1⟩ := word_remove_correct_aux c prog _ _ s2 hcv (by simp) hTc
          obtain ⟨k2, hk2⟩ := word_remove_correct_aux c retHandler (setVars n ys s1) r s' h hne
            (by show s1.compile = _; rw [hs1c, ← hcomp]; exact hTc)
          refine ⟨k1 + k2, ?_⟩
          rw [ht, getVars_compileState, hg]
          simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I,
            wordSemAddRetLoc, hf, Option.map_some, hdc, cs_locals, hce]
          rw [if_neg (by simp only [compileState]; omega), htgt,
            evaluate_add_clock_compileState _ _ _ _ _ _ ⟨hk1, by simp⟩ k2]
          simp only [hx, if_false, popEnv_compileState, hp, Option.map_some, cs_locals, hdom,
            if_true, setVars_compileState]
          exact hk2
        · simp only [hdom, if_false, Prod.mk.injEq] at h
          exact absurd h.1.symm hne
      · cases handler with
        | none =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨k1, hk1⟩ := word_remove_correct_aux c prog _ _ _ hcv hne hTc
          refine ⟨k1, ?_⟩
          rw [ht, getVars_compileState, hg]
          simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I,
            wordSemAddRetLoc, hf, Option.map_some, hdc, cs_locals, hce]
          rw [if_neg (by simp only [compileState]; omega), htgt, hk1]
          rfl
        | some hv =>
          obtain ⟨n', hprog, l1', l2'⟩ := hv
          simp only at h
          by_cases hx : x ≠ WordLocW.loc l1' l2'
          · rw [if_pos hx] at h
            simp only [Prod.mk.injEq] at h
            exact absurd h.1.symm hne
          rw [if_neg hx] at h
          by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
          · simp only [hdom, if_true] at h
            obtain ⟨k1, hk1⟩ := word_remove_correct_aux c prog _ _ s2 hcv (by simp) hTc
            obtain ⟨k2, hk2⟩ := word_remove_correct_aux c hprog (setVar n' y s2) r s' h hne
              (by show s2.compile = _; rw [← hcomp]; exact hTc)
            refine ⟨k1 + k2, ?_⟩
            have htgt' := htgt (k1 + k2)
            simp only [Option.map_some] at htgt'
            rw [ht, getVars_compileState, hg]
            simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I,
              wordSemAddRetLoc, hf, Option.map_some, hdc, cs_locals, hce]
            rw [if_neg (by simp only [compileState]; omega), htgt',
              evaluate_add_clock_compileState _ _ _ _ _ _ ⟨hk1, by simp⟩ k2]
            simp only [Option.map_some]
            rw [if_neg hx]
            simp only [cs_locals, hdom, if_true, setVar_compileState]
            exact hk2
          · simp only [hdom, if_false, Prod.mk.injEq] at h
            exact absurd h.1.symm hne
      all_goals
        simp only [Prod.mk.injEq] at h
        first
          | exact absurd h.1.symm hne
          | (obtain ⟨rfl, rfl⟩ := h
             obtain ⟨k1, hk1⟩ := word_remove_correct_aux c prog _ _ _ hcv hne hTc
             refine ⟨k1, ?_⟩
             rw [ht, getVars_compileState, hg]
             simp only [hbad, Bool.false_eq_true, if_false, cs_code, cs_stackSize, findCode_map_I,
               wordSemAddRetLoc, hf, Option.map_some, hdc, cs_locals, hce]
             rw [if_neg (by simp only [compileState]; omega), htgt, hk1])
  | .install ptr len dptr dlen names, s, r, s', h, _, hc =>
      ⟨0, by rw [show removeMustTerminate (WordLangProgHOL.install ptr len dptr dlen names) =
          .install ptr len dptr dlen names from rfl, evaluate_install_compileState 0 c s hc, h]⟩
  | .skip, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.skip : WordLangProgHOL (BitVec width)) =
        .skip from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .move a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.move a b : WordLangProgHOL (BitVec width)) =
        .move a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .inst a, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.inst a) = .inst a from rfl,
        evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .assign a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.assign a b) = .assign a b from rfl,
        evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .get a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.get a b : WordLangProgHOL (BitVec width)) =
        .get a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .set a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.set a b) = .set a b from rfl,
        evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .store a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.store a b) = .store a b from rfl,
        evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .alloc a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.alloc a b : WordLangProgHOL (BitVec width)) =
        .alloc a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .storeConsts a b d e f, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.storeConsts a b d e f) =
        .storeConsts a b d e f from rfl,
        evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .raise a, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.raise a : WordLangProgHOL (BitVec width)) =
        .raise a from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | WordLangProgHOL.return a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.return a b : WordLangProgHOL (BitVec width)) =
        .return a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | WordLangProgHOL.break a, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.break a : WordLangProgHOL (BitVec width)) =
        .break a from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | WordLangProgHOL.continue a, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.continue a : WordLangProgHOL (BitVec width)) =
        .continue a from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .opCurrHeap a b d, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.opCurrHeap a b d : WordLangProgHOL (BitVec width)) =
        .opCurrHeap a b d from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .locValue a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.locValue a b : WordLangProgHOL (BitVec width)) =
        .locValue a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .codeBufferWrite a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate
          (WordLangProgHOL.codeBufferWrite a b : WordLangProgHOL (BitVec width)) =
        .codeBufferWrite a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .dataBufferWrite a b, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate
          (WordLangProgHOL.dataBufferWrite a b : WordLangProgHOL (BitVec width)) =
        .dataBufferWrite a b from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .ffi a b d e f g, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.ffi a b d e f g : WordLangProgHOL (BitVec width)) =
        .ffi a b d e f g from rfl, evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
  | .shareInst a b d, s, r, s', h, _, _ => ⟨0, by
      rw [show removeMustTerminate (WordLangProgHOL.shareInst a b d) = .shareInst a b d from rfl,
        evaluate_compileState_frame 0 c s _ rfl (by intros; nofun), h]⟩
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcx with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.setVars,
      WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep, true_and] at *
    omega

end Correct

/-- Exact HOL `word_remove_correct` (`word_removeProofScript.sml:262-430`, with
    the resumed `Loop` case):

    ```
    ∀prog st res rst.
      evaluate (prog,st) = (res,rst) ∧
      st.compile = (λcfg. c cfg o (MAP (I ## I ## remove_must_terminate))) ∧
      res ≠ SOME Error ⇒
      ∃clk. evaluate (remove_must_terminate prog, compile_state clk c st) =
            (res, compile_state 0 c rst)
    ```

    HOL's free variable `c` is the outermost explicit binder; `I ## I ## f` on
    the `(num # num # prog)` triples is `fun t => (t.1, t.2.1, f t.2.2)`. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "word_remove_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_remove_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (c : WordCompileFn width C) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
      evaluate prog st = (res, rst) ∧
        st.compile = (fun cfg => c cfg ∘
          List.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2))) ∧
        res ≠ some .error →
      ∃ clk, evaluate (removeMustTerminate prog) (compileState clk c st) =
        (res, compileState 0 c rst) := by
  intro prog st res rst ⟨h, hc, hne⟩
  exact word_remove_correct_aux c prog st res rst h hne hc

end Flapjack.Compiler.Backend.WordRemove
