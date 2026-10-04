import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Motive
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap

/-!
# `evaluate_stack_swap` stack-insensitive leaf cases

The HOL `evaluate_stack_swap` cases for statements that neither read nor
recurse through the stack. The untagged helpers show that such a statement
commutes with replacing the stack (Flapjack proof infrastructure, analogous to
the clock- and permute-constancy lemmas).
-/

namespace Flapjack

namespace WordSemStateFiniteExact

section StackConst

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem wordExp_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) :
    ∀ e : WordLangExpHOL (BitVec width), wordExp { s with stack := k } e = wordExp s e
  | .const w => by rw [wordExp, wordExp]
  | .var v => by rw [wordExp, wordExp]; rfl
  | .lookup n => by rw [wordExp, wordExp]; rfl
  | .load a => by
      rw [wordExp, wordExp, wordExp_withStack s k a]
      rfl
  | .op op args => by
      rw [wordExp, wordExp]
      have : (args.attach.map fun (x : { x // x ∈ args }) => wordExp { s with stack := k } x.1) =
          (args.attach.map fun (x : { x // x ∈ args }) => wordExp s x.1) := by
        apply List.map_congr_left
        intro ⟨e, he⟩ _
        have := List.sizeOf_lt_of_mem he
        exact wordExp_withStack s k e
      simp only [] at this ⊢
      rw [this]
  | .shift sh e1 e2 => by
      rw [wordExp, wordExp, wordExp_withStack s k e1, wordExp_withStack s k e2]
termination_by e => sizeOf e

theorem getVars_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) :
    ∀ ns, getVars ns { s with stack := k } = getVars ns s
  | [] => rfl
  | n :: ns => by
      simp only [getVars, getVars_withStack s k ns]
      rfl

theorem memStore_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (a : BitVec width) (w : WordLocW width) :
    memStore a w { s with stack := k } =
      (memStore a w s).map (fun s' => { s' with stack := k }) := by
  unfold memStore
  by_cases h : s.mdomain a = true <;> simp [h]

set_option linter.unusedSimpArgs false in
theorem inst_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (i : WordLangInst (BitVec width)) :
    inst i { s with stack := k } = (inst i s).map (fun s' => { s' with stack := k }) := by
  cases i with
  | skip => rfl
  | const r w => simp only [inst, assign, wordExp_withStack]; split <;> rfl
  | arith a =>
    cases a <;> simp only [inst, assign, wordExp_withStack, getVars_withStack] <;>
      (repeat' split) <;> first | rfl | simp_all
  | mem op r a =>
    cases a
    cases op <;> simp only [inst, wordExp_withStack, getVar, memStore_withStack] <;>
      (repeat' split) <;> first | rfl | (subst_vars; rfl) |
        (simp_all [memLoad, memStore, setVar]; done) |
        (simp_all [memLoad, memStore, setVar]; obtain ⟨_, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)
theorem shMemSetVar_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (res : Option (HolFfiResult F)) (v : Nat) :
    shMemSetVar (rw := width) res v { s with stack := k } =
      ((shMemSetVar (rw := width) res v s).1,
        match (shMemSetVar (rw := width) res v s).1 with
        | some (.finalFfi _) => (shMemSetVar (rw := width) res v s).2
        | _ => { (shMemSetVar (rw := width) res v s).2 with stack := k }) := by
  cases res with
  | none => rfl
  | some r => cases r <;> rfl

/-- The swapped-stack result state of a stack-insensitive statement: flushing
results (`TimeOut`, `FinalFFI`, `NotEnoughSpace`) are identical, every other
result carries the replacement stack. -/
def stackSwapRes {rw : Nat} [NeZero rw] (r : Option (WordSemResult rw))
    (s1 : WordSemStateFiniteExact width C F) (k : List (WordSemStackFrame width)) :
    WordSemStateFiniteExact width C F :=
  match r with
  | some .timeOut => s1
  | some (.finalFfi _) => s1
  | some .notEnoughSpace => s1
  | _ => { s1 with stack := k }

theorem shMemSetVar_withStack' (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (res : Option (HolFfiResult F)) (v : Nat) :
    shMemSetVar (rw := width) res v { s with stack := k } =
      ((shMemSetVar (rw := width) res v s).1,
        stackSwapRes (shMemSetVar (rw := width) res v s).1 (shMemSetVar (rw := width) res v s).2 k) := by
  cases res with
  | none => rfl
  | some r => cases r <;> rfl

set_option linter.unusedSimpArgs false in
theorem shareInst_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (op : WordMemOp) (v : Nat) (ad : BitVec width) :
    shareInst (rw := width) op v ad { s with stack := k } =
      ((shareInst (rw := width) op v ad s).1,
        stackSwapRes (shareInst (rw := width) op v ad s).1
          (shareInst (rw := width) op v ad s).2 k) := by
  cases op <;> simp only [shareInst] <;>
    simp only [shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32, getVar, shMemSetVar_withStack'] <;>
    (repeat' split) <;>
    first | rfl | simp_all [stackSwapRes, flushState, setVar]

/-- The statements whose evaluation neither reads the stack nor recurses. -/
def wordProgStackConst {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _
  | .alloc _ _ | .raise _ => false
  | _ => true

set_option linter.unusedSimpArgs false in
/-- A stack-insensitive statement commutes with replacing the stack. -/
theorem evaluate_withStack_const (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (p : WordLangProgHOL (BitVec width))
    (hp : wordProgStackConst p = true) :
    evaluate p { s with stack := k } =
      ((evaluate p s).1, stackSwapRes (evaluate p s).1 (evaluate p s).2 k) := by
  cases p <;> simp only [wordProgStackConst, Bool.false_eq_true] at hp <;>
    rw [evaluate, evaluate] <;>
    simp only [getVar, getVars_withStack, wordExp_withStack, inst_withStack,
      shareInst_withStack, memStore_withStack, getStore] <;>
    (repeat' split) <;>
    first | rfl | simp_all [stackSwapRes, flushState, setVar, setVars, setStore, unsetVar, decClock]

/-- Whether a result is one of HOL's flushing results. -/
def isFlushRes {rw : Nat} [NeZero rw] : Option (WordSemResult rw) → Bool
  | some .timeOut => true
  | some (.finalFfi _) => true
  | some .notEnoughSpace => true
  | _ => false

set_option linter.unusedSimpArgs false in
theorem shareInst_facts (s : WordSemStateFiniteExact width C F) (op : WordMemOp) (v : Nat)
    (ad : BitVec width) :
    (∀ x y, (shareInst (rw := width) op v ad s).1 ≠ some (.exception x y)) ∧
    (isFlushRes (shareInst (rw := width) op v ad s).1 = true →
      (shareInst (rw := width) op v ad s).2.stack = [] ∧
        (shareInst (rw := width) op v ad s).2.locals = .ln) ∧
    (isFlushRes (shareInst (rw := width) op v ad s).1 = false →
      (shareInst (rw := width) op v ad s).2.stack = s.stack ∧
        (shareInst (rw := width) op v ad s).2.handler = s.handler) := by
  have key : ∀ (res : Option (HolFfiResult F)) (v : Nat) (s : WordSemStateFiniteExact width C F),
      (∀ x y, (shMemSetVar (rw := width) res v s).1 ≠ some (.exception x y)) ∧
      (isFlushRes (shMemSetVar (rw := width) res v s).1 = true →
        (shMemSetVar (rw := width) res v s).2.stack = [] ∧
          (shMemSetVar (rw := width) res v s).2.locals = .ln) ∧
      (isFlushRes (shMemSetVar (rw := width) res v s).1 = false →
        (shMemSetVar (rw := width) res v s).2.stack = s.stack ∧
          (shMemSetVar (rw := width) res v s).2.handler = s.handler) := by
    intro res v s
    cases res with
    | none => simp [shMemSetVar, isFlushRes]
    | some r => cases r <;> simp [shMemSetVar, isFlushRes, flushState, setVar]
  cases op <;> simp only [shareInst] <;>
    simp only [shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32, getVar] <;>
    (repeat' split) <;>
    first | exact key _ _ _ | simp_all [isFlushRes, flushState, setVar]

set_option linter.unusedSimpArgs false in
/-- A memory store keeps the stack and handler. Flapjack infrastructure. -/
theorem memStore_stack_handler (a : BitVec width) (w : WordLocW width)
    (s s1 : WordSemStateFiniteExact width C F) (h : memStore a w s = some s1) :
    s1.stack = s.stack ∧ s1.handler = s.handler := by
  unfold memStore at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

/-- HOL `inst_const_full` (stack and handler part): a successful instruction
keeps the stack and handler. Flapjack infrastructure for the leaf cases. -/
theorem inst_stack_handler (s s1 : WordSemStateFiniteExact width C F)
    (i : WordLangInst (BitVec width)) (h : inst i s = some s1) :
    s1.stack = s.stack ∧ s1.handler = s.handler := by
  have hk := inst_withStack s s.stack i
  have hp := inst_withPermute s s.permute i
  -- direct case analysis
  cases i with
  | skip => simp only [inst, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | const r w =>
    simp only [inst, assign] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
      (try subst h) <;> simp [setVar]
  | arith a =>
    cases a <;> simp only [inst, assign] at h <;> (repeat' split at h) <;>
      simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;> simp [setVar]
  | mem op r a =>
    cases a
    cases op <;> simp only [inst, getVar] at h <;> (repeat' split at h) <;>
      first
      | exact memStore_stack_handler _ _ _ _ h
      | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
      | (simp only [Option.some.injEq] at h; subst h; exact memStore_stack_handler _ _ _ _ ‹memStore _ _ _ = some _›)
      | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
set_option linter.unusedSimpArgs false in
/-- Result facts of a stack-insensitive statement. -/
theorem evaluate_stackConst_facts (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgStackConst p = true) :
    (∀ x y, (evaluate p s).1 ≠ some (.exception x y)) ∧
    (isFlushRes (evaluate p s).1 = true →
      (evaluate p s).2.stack = [] ∧ (evaluate p s).2.locals = .ln) ∧
    (isFlushRes (evaluate p s).1 = false →
      (evaluate p s).2.stack = s.stack ∧ (evaluate p s).2.handler = s.handler) := by
  cases p <;> simp only [wordProgStackConst, Bool.false_eq_true] at hp <;>
    rw [evaluate] <;>
    (repeat' split) <;>
    first
    | exact shareInst_facts _ _ _ _
    | (refine ⟨by simp, by simp [isFlushRes], fun _ => inst_stack_handler _ _ _ ‹_›⟩)
    | (simp_all [isFlushRes, flushState, setVar, setVars, setStore, unsetVar, decClock, memStore]; done)
    | (refine ⟨by simp, by simp [isFlushRes],
        fun _ => memStore_stack_handler _ _ _ _ ‹memStore _ _ _ = some _›⟩)
    | (dsimp only; split <;> simp [isFlushRes])

end StackConst

end WordSemStateFiniteExact

namespace WordSemStackEq

open WordSemStateFiniteExact

/-- The `evaluate_stack_swap` conclusion for every stack-insensitive statement
(all statements except `MustTerminate`, `Call`, `Seq`, `If`, `Loop`, `Alloc`
and `Raise`). Flapjack infrastructure: the tagged per-case theorems and the
assembly instantiate it. -/
theorem stackSwapPost_stackConst {width : Nat} [NeZero width] {C F : Type}
    (c : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hp : wordProgStackConst c = true) : stackSwapPost c s := by
  obtain ⟨hexc, hflush, hother⟩ := evaluate_stackConst_facts s c hp
  have hsw : ∀ xs, evaluate c { s with stack := xs } =
      ((evaluate c s).1, stackSwapRes (evaluate c s).1 (evaluate c s).2 xs) :=
    fun xs => evaluate_withStack_const s xs c hp
  unfold stackSwapPost
  rcases he : evaluate c s with ⟨res, s1⟩
  rw [he] at hexc hflush hother
  simp only [he] at hsw
  have keep : isFlushRes res = false → s1.handler = s.handler →
      s1.stack = s.stack →
      sKeyEq s.stack s1.stack ∧ s1.handler = s.handler ∧
        ∀ xs, sValEq s.stack xs →
          ∃ st, evaluate c { s with stack := xs } = (res, { s1 with stack := st }) ∧
            sValEq s1.stack st ∧ sKeyEq xs st := by
    intro hf hh hk
    refine ⟨hk ▸ of_eq_true (sKeyEqRefl _), hh, fun xs hxs => ⟨xs, ?_, hk ▸ hxs,
      of_eq_true (sKeyEqRefl _)⟩⟩
    rw [hsw]
    cases res with
    | none => rfl
    | some r => cases r <;> first | rfl | simp [isFlushRes] at hf
  rcases res with _ | r
  · obtain ⟨hk, hh⟩ := hother rfl
    exact keep rfl hh hk
  · cases r with
    | exception x y => exact absurd rfl (hexc x y)
    | error => trivial
    | timeOut =>
        obtain ⟨hk, hl⟩ := hflush rfl
        exact ⟨hk, hl, fun xs _ => by rw [hsw]; rfl⟩
    | notEnoughSpace =>
        obtain ⟨hk, hl⟩ := hflush rfl
        exact ⟨hk, hl, fun xs _ => by rw [hsw]; rfl⟩
    | finalFfi e =>
        obtain ⟨hk, hl⟩ := hflush rfl
        exact ⟨hk, hl, fun xs _ => by rw [hsw]; rfl⟩
    | result v vs =>
        obtain ⟨hk, hh⟩ := hother rfl
        exact keep rfl hh hk
    | «break» k =>
        obtain ⟨hk, hh⟩ := hother rfl
        exact keep rfl hh hk
    | «continue» k =>
        obtain ⟨hk, hh⟩ := hother rfl
        exact keep rfl hh hk

/-- The `evaluate_stack_swap` conclusion for `Raise`. Flapjack infrastructure
for the tagged `Raise` case. -/
theorem stackSwapPost_raise {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : WordSemStateFiniteExact width C F) :
    stackSwapPost (.raise v : WordLangProgHOL (BitVec width)) s := by
  have hsw : ∀ xs, evaluate (.raise v : WordLangProgHOL (BitVec width)) { s with stack := xs } =
      match getVar v s with
      | none => (some .error, { s with stack := xs })
      | some w =>
          match jumpExc { s with stack := xs } with
          | none => (some .error, { s with stack := xs })
          | some (s', l1, l2) => (some (.exception (.loc l1 l2) w), s') := by
    intro xs; rw [evaluate]; rfl
  unfold stackSwapPost
  rw [evaluate]
  cases hv : getVar v s with
  | none => trivial
  | some w =>
    dsimp only
    unfold jumpExc
    by_cases hlt : s.handler < s.stack.length
    · rw [if_pos hlt]
      cases hl : wordSemLastN (s.handler + 1) s.stack with
      | nil => trivial
      | cons fr ls =>
        cases fr with
        | stackFrame m e0 e hn =>
          cases hn with
          | none => trivial
          | some hn =>
            obtain ⟨n, l1, l2⟩ := hn
            dsimp only
            refine ⟨hlt, e0, e, (n, l1, l2), ls, m, e, rfl, rfl, ⟨rfl, rfl⟩,
              of_eq_true (sKeyEqRefl _), rfl, ?_⟩
            rintro xs e0' e' ls' ⟨hl', hxs⟩
            have hlen := sValEqLength _ _ hxs
            have hv' := sValEqLastN _ _ (s.handler + 1) hxs
            rw [hl, hl'] at hv'
            obtain ⟨hvs, hfr, _, _⟩ := hv'
            refine ⟨ls', sptUnion (sptFromAList e') (sptFromAList e0'), ?_,
              ⟨e', rfl, rfl, hfr⟩, hvs, of_eq_true (sKeyEqRefl _)⟩
            rw [hsw, hv]
            dsimp only
            unfold jumpExc
            rw [if_pos (show s.handler < xs.length from hlen ▸ hlt)]
            dsimp only
            rw [hl']
    · rw [if_neg hlt]
      trivial

end WordSemStackEq

namespace WordSemStackEq
namespace EvaluateStackSwapLeafWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapLeafWitnesses

open EvaluateStackSwapLeafWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Skip` case:
the HOL conclusion at `Skip`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Skip {width : Nat} [NeZero width] {C F : Type} :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.skip : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `StoreConsts` case:
the HOL conclusion at `StoreConsts`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_StoreConsts {width : Nat} [NeZero width] {C F : Type} (t1 t2 a o : Nat) (ws : List (Bool × BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.storeConsts t1 t2 a o ws : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Move` case:
the HOL conclusion at `Move`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Move {width : Nat} [NeZero width] {C F : Type} (pri : Nat) (moves : List (Nat × Nat)) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.move pri moves : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Inst` case:
the HOL conclusion at `Inst`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Inst {width : Nat} [NeZero width] {C F : Type} (i : WordLangInst (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.inst i : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Assign` case:
the HOL conclusion at `Assign`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Assign {width : Nat} [NeZero width] {C F : Type} (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.assign v e : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Get` case:
the HOL conclusion at `Get`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Get {width : Nat} [NeZero width] {C F : Type} (v : Nat) (name : WordStoreHOL) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.get v name : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Set` case:
the HOL conclusion at `Set`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Set {width : Nat} [NeZero width] {C F : Type} (name : WordStoreHOL) (e : WordLangExpHOL (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.set name e : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `OpCurrHeap` case:
the HOL conclusion at `OpCurrHeap`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_OpCurrHeap {width : Nat} [NeZero width] {C F : Type} (op : BinOp) (v1 v2 : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.opCurrHeap op v1 v2 : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Store` case:
the HOL conclusion at `Store`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Store {width : Nat} [NeZero width] {C F : Type} (e : WordLangExpHOL (BitVec width)) (v : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.store e v : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Tick` case:
the HOL conclusion at `Tick`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Tick {width : Nat} [NeZero width] {C F : Type} :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.tick : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Return` case:
the HOL conclusion at `Return`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Return {width : Nat} [NeZero width] {C F : Type} (n : Nat) (ms : List Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.return n ms : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Break` case:
the HOL conclusion at `Break`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Break {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.break k : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Continue` case:
the HOL conclusion at `Continue`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Continue {width : Nat} [NeZero width] {C F : Type} (k : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.continue k : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `LocValue` case:
the HOL conclusion at `LocValue`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_LocValue {width : Nat} [NeZero width] {C F : Type} (r l1 : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.locValue r l1 : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Install` case:
the HOL conclusion at `Install`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_Install {width : Nat} [NeZero width] {C F : Type} (r1 r2 r3 r4 : Nat) (names : WordLangCutsetsHOL) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.install r1 r2 r3 r4 names : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `CodeBufferWrite` case:
the HOL conclusion at `CodeBufferWrite`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_CodeBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `DataBufferWrite` case:
the HOL conclusion at `DataBufferWrite`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_DataBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `FFI` case:
the HOL conclusion at `FFI`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_FFI {width : Nat} [NeZero width] {C F : Type} (ffiIndex : Flapjack.Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.ffi ffiIndex ptr1 len1 ptr2 len2 names : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `ShareInst` case:
the HOL conclusion at `ShareInst`, for every state; no sub-program, so no induction
hypothesis and no extra premise. -/
theorem evaluateStackSwap_ShareInst {width : Nat} [NeZero width] {C F : Type} (op : WordMemOp) (v : Nat) (ad : WordLangExpHOL (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.shareInst op v ad : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_stackConst _ s rfl

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Raise` case:
the HOL conclusion at `Raise n`, for every state; no sub-program and no extra
premise. -/
theorem evaluateStackSwap_Raise {width : Nat} [NeZero width] {C F : Type} (n : Nat) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.raise n : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_raise n s

end WordSemStackEq

end Flapjack
