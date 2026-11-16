module

public import Flapjack.Pancake.WordLang.MaxVarExp
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

@[expose] public section

/-!
# wordProps `evaluate_add_clock` over the exact wordSem evaluator

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:1383`
(bead `flapjack-pxn.18.5.9.1.1`).  HOL's proof uses the "CONST lemmas": each
wordSem helper commutes with a change of `clock`.  It also uses
`evaluate_clock_const`: every non-recursive statement returns its input clock
unchanged and runs the same under any clock.  These are untagged support
here, because their HOL statements are generated per constructor.  The tagged
`evaluate_add_clock` is proved by recursion on HOL's termination measure, as
`evaluate_clock` is.
-/

namespace Flapjack

namespace WordSemEvaluateAddClockSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateAddClockSupport

namespace WordSemStateFiniteExact

section ClockConst

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem wordExp_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) :
    ∀ e : WordLangExpHOL (BitVec width), wordExp { s with clock := k } e = wordExp s e := by
  intro e
  set_option tactic.fun_induction.unfolding false in
    fun_induction maxVarExpHOL e with
    | case3 operator arguments ih =>
        simp only [wordExp]
        have hmap := List.map_congr_left (l := arguments.attach)
          (fun e _ => ih e.val e.property)
        rw [hmap]
    | case5 expression _ _ _ _ => cases expression <;> grind only [wordExp, memLoad, getVar, getStore]
    | _ => simp_all only [wordExp, memLoad, getVar]

theorem getVars_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) :
    ∀ ns, getVars ns { s with clock := k } = getVars ns s
  | [] => rfl
  | n :: ns => by
      simp only [getVars, getVars_withClock s k ns]
      rfl

theorem memStore_withClock (s : WordSemStateFiniteExact width C F) (k : Nat)
    (a : BitVec width) (w : WordLocW width) :
    memStore a w { s with clock := k } = (memStore a w s).map (fun s' => { s' with clock := k }) := by
  unfold memStore
  by_cases h : s.mdomain a = true <;> simp [h]

set_option linter.unusedSimpArgs false in
theorem inst_withClock (s : WordSemStateFiniteExact width C F) (k : Nat)
    (i : WordLangInst (BitVec width)) :
    inst i { s with clock := k } = (inst i s).map (fun s' => { s' with clock := k }) := by
  cases i with
  | skip => rfl
  | const r w => simp only [inst, assign, wordExp_withClock]; split <;> rfl
  | arith a =>
    cases a <;> simp only [inst, assign, wordExp_withClock, getVars_withClock] <;>
      (repeat' split) <;> first | rfl | simp_all
  | mem op r a =>
    cases a
    cases op <;> simp only [inst, wordExp_withClock, getVar, memStore_withClock] <;>
      (repeat' split) <;> first | rfl | (subst_vars; rfl) |
        (simp_all [memLoad, memStore, setVar]; done) |
        (simp_all [memLoad, memStore, setVar]; obtain ⟨_, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)
  | fp f =>
    cases f <;> simp only [inst, getFpVar, getVar] <;>
      (repeat' split) <;> first | rfl | simp_all

theorem pushEnv_withClock (s : WordSemStateFiniteExact width C F) (k : Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    pushEnv envs h { s with clock := k } = { pushEnv envs h s with clock := k } := by
  cases h with
  | none => rfl
  | some v => obtain ⟨_, _, _, _⟩ := v; rfl

theorem popEnv_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) :
    popEnv { s with clock := k } = (popEnv s).map (fun s' => { s' with clock := k }) := by
  unfold popEnv
  simp only
  split <;> rfl

theorem gc_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) :
    gc { s with clock := k } = (gc s).map (fun s' => { s' with clock := k }) := by
  unfold gc
  simp only
  split
  · rfl
  · split <;> rfl

theorem jumpExc_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) :
    jumpExc { s with clock := k } =
      (jumpExc s).map (fun p => ({ p.1 with clock := k }, p.2.1, p.2.2)) := by
  unfold jumpExc
  simp only
  split
  · split <;> rfl
  · rfl

theorem cutState_withClock (s : WordSemStateFiniteExact width C F) (k : Nat)
    (names : WordLangCutsetsHOL) :
    cutState names { s with clock := k } =
      (cutState names s).map (fun s' => { s' with clock := k }) := by
  unfold cutState
  simp only
  split <;> rfl

theorem flushState_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) (b : Bool) :
    flushState b { s with clock := k } = { flushState b s with clock := k } := by
  cases b <;> rfl

theorem alloc_withClock (s : WordSemStateFiniteExact width C F) (k : Nat) (w : BitVec width)
    (names : WordLangCutsetsHOL) :
    alloc w names { s with clock := k } =
      ((alloc w names s).1, { (alloc w names s).2 with clock := k }) := by
  unfold alloc
  simp only
  split
  · rfl
  · rename_i envs _
    have hpush : pushEnv envs none (setStore .allocSize (.word w) { s with clock := k }) =
        { pushEnv envs none (setStore .allocSize (.word w) s) with clock := k } :=
      pushEnv_withClock (setStore .allocSize (.word w) s) k envs none
    rw [hpush, gc_withClock]
    cases gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
    | none => rfl
    | some g =>
      simp only [Option.map_some, popEnv_withClock]
      cases popEnv g with
      | none => rfl
      | some p =>
        simp only [Option.map_some]
        cases hs : getStore .allocSize p with
        | none => simp [getStore] at hs ⊢; simp [hs]
        | some a =>
          have hs' : getStore .allocSize { p with clock := k } = some a := hs
          simp only [hs']
          have hsp : hasSpace a { p with clock := k } = hasSpace a p := rfl
          rw [hsp]
          split <;> rfl

theorem shMemSetVar_withClock (s : WordSemStateFiniteExact width C F) (k : Nat)
    (res : Option (HolFfiResult F)) (v : Nat) :
    shMemSetVar (rw := width) res v { s with clock := k } =
      ((shMemSetVar (rw := width) res v s).1,
        { (shMemSetVar (rw := width) res v s).2 with clock := k }) := by
  cases res with
  | none => rfl
  | some r => cases r <;> rfl

set_option linter.unusedSimpArgs false in
theorem shareInst_withClock (s : WordSemStateFiniteExact width C F) (k : Nat)
    (op : WordMemOp) (v : Nat) (ad : BitVec width) :
    shareInst (rw := width) op v ad { s with clock := k } =
      ((shareInst (rw := width) op v ad s).1,
        { (shareInst (rw := width) op v ad s).2 with clock := k }) := by
  cases op <;> simp only [shareInst, shMemSetVar_withClock] <;>
    simp only [shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32, getVar] <;>
    (repeat' split) <;> first | rfl | simp_all [flushState, setVar]

/-- The statements of HOL's `evaluate_clock_const`: those whose evaluation
    neither reads the clock nor recurses. -/
def wordProgClockConst {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _ | .tick => false
  | _ => true

set_option linter.unusedSimpArgs false in
/-- HOL `evaluate_clock_const` / `evaluate_clock_with_const`
    (`wordPropsScript.sml:1318-1345`): a clock-constant statement runs the
    same under any clock and keeps it. -/
theorem evaluate_withClock_const (s : WordSemStateFiniteExact width C F) (k : Nat)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true) :
    evaluate p { s with clock := k } = ((evaluate p s).1, { (evaluate p s).2 with clock := k }) := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;>
    rw [evaluate, evaluate] <;>
    simp only [getVar, getVars_withClock, wordExp_withClock, inst_withClock, alloc_withClock,
      shareInst_withClock, jumpExc_withClock, memStore_withClock, getStore] <;>
    (repeat' split) <;> first | rfl | simp_all [flushState, setVar, setVars, setStore, unsetVar]

end ClockConst

section AddClock

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- A clock-constant statement keeps the clock. -/
theorem evaluate_const_clock (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true) :
    (evaluate p s).2.clock = s.clock := by
  have h := evaluate_withClock_const s s.clock p hp
  have hs : ({ s with clock := s.clock } : WordSemStateFiniteExact width C F) = s := rfl
  rw [hs] at h
  have := congrArg (fun x => x.2.clock) h
  simpa using this

/-- Exact HOL `wordProps$evaluate_clock_with_const`
    (`wordPropsScript.sml:1334-1341`): HOL's generated conjunction of the
    twenty per-constructor clock-constant facts, each saying that the
    statement runs the same under any clock and keeps that clock. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_clock_with_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_clock_with_const {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate .skip { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate .skip s)) ∧
    (∀ (n : Nat) (names : WordLangCutsetsHOL)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.alloc n names) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.alloc n names) s)) ∧
    (∀ (t1 t2 addr offset : Nat) (words : List (Bool × BitVec width))
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.storeConsts t1 t2 addr offset words) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k }))
          (evaluate (.storeConsts t1 t2 addr offset words) s)) ∧
    (∀ (pri : Nat) (moves : List (Nat × Nat))
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.move pri moves) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.move pri moves) s)) ∧
    (∀ (i : WordLangInst (BitVec width))
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.inst i) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.inst i) s)) ∧
    (∀ (v : Nat) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.assign v exp) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.assign v exp) s)) ∧
    (∀ (v : Nat) (name : WordStoreHOL)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.get v name) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.get v name) s)) ∧
    (∀ (v : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.set v exp) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.set v exp) s)) ∧
    (∀ (b : BinOp) (dst src : Nat)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.opCurrHeap b dst src) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.opCurrHeap b dst src) s)) ∧
    (∀ (exp : WordLangExpHOL (BitVec width)) (v : Nat)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.store exp v) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.store exp v) s)) ∧
    (∀ (n : Nat) (ms : List Nat)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.return n ms) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.return n ms) s)) ∧
    (∀ (n : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.raise n) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.raise n) s)) ∧
    (∀ (label : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.break label) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.break label) s)) ∧
    (∀ (label : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.continue label) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.continue label) s)) ∧
    (∀ (destination source : Nat)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.locValue destination source) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.locValue destination source) s)) ∧
    (∀ (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.install ptr len dptr dlen names) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k }))
          (evaluate (.install ptr len dptr dlen names) s)) ∧
    (∀ (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.codeBufferWrite r1 r2) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.codeBufferWrite r1 r2) s)) ∧
    (∀ (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.dataBufferWrite r1 r2) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.dataBufferWrite r1 r2) s)) ∧
    (∀ (function : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
      (names : WordLangCutsetsHOL)
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.ffi function ptr1 len1 ptr2 len2 names) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k }))
          (evaluate (.ffi function ptr1 len1 ptr2 len2 names) s)) ∧
    (∀ (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (k : Nat),
      evaluate (.shareInst op v exp) { s with clock := k } =
        (fun ((r : Option (WordSemResult width)),
            (s : WordSemStateFiniteExact width C F)) =>
          (r, { s with clock := k })) (evaluate (.shareInst op v exp) s)) := by
  refine ⟨fun s k => ?_, fun n names s k => ?_, fun t1 t2 addr offset words s k => ?_,
    fun pri moves s k => ?_, fun i s k => ?_, fun v exp s k => ?_,
    fun v name s k => ?_, fun v exp s k => ?_, fun b dst src s k => ?_,
    fun exp v s k => ?_, fun n ms s k => ?_, fun n s k => ?_,
    fun label s k => ?_, fun label s k => ?_, fun destination source s k => ?_,
    fun ptr len dptr dlen names s k => ?_, fun r1 r2 s k => ?_,
    fun r1 r2 s k => ?_, fun function ptr1 len1 ptr2 len2 names s k => ?_,
    fun op v exp s k => ?_⟩
  all_goals
    exact evaluate_withClock_const s k _ (by rfl)

/-- Exact HOL `wordProps$evaluate_clock_const`
    (`wordPropsScript.sml:1311-1318`): HOL's generated conjunction of the
    twenty per-constructor facts that a clock-constant statement keeps the
    input clock. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_clock_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_clock_const {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate .skip s = (result, s') → s'.clock = s.clock) ∧
    (∀ (n : Nat) (names : WordLangCutsetsHOL)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.alloc n names) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (t1 t2 addr offset : Nat) (words : List (Bool × BitVec width))
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.storeConsts t1 t2 addr offset words) s = (result, s') →
        s'.clock = s.clock) ∧
    (∀ (pri : Nat) (moves : List (Nat × Nat))
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.move pri moves) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (i : WordLangInst (BitVec width))
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.inst i) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (v : Nat) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.assign v exp) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (v : Nat) (name : WordStoreHOL)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.get v name) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (v : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.set v exp) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (b : BinOp) (dst src : Nat)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.opCurrHeap b dst src) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (exp : WordLangExpHOL (BitVec width)) (v : Nat)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.store exp v) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (n : Nat) (ms : List Nat)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.return n ms) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (n : Nat) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate (.raise n) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (label : Nat) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate (.break label) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (label : Nat) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate (.continue label) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (destination source : Nat) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate (.locValue destination source) s = (result, s') →
        s'.clock = s.clock) ∧
    (∀ (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.install ptr len dptr dlen names) s = (result, s') →
        s'.clock = s.clock) ∧
    (∀ (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate (.codeBufferWrite r1 r2) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate (.dataBufferWrite r1 r2) s = (result, s') → s'.clock = s.clock) ∧
    (∀ (function : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
      (names : WordLangCutsetsHOL)
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.ffi function ptr1 len1 ptr2 len2 names) s = (result, s') →
        s'.clock = s.clock) ∧
    (∀ (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate (.shareInst op v exp) s = (result, s') → s'.clock = s.clock) := by
  refine ⟨fun s result s' => ?_, fun n names s result s' => ?_,
    fun t1 t2 addr offset words s result s' => ?_,
    fun pri moves s result s' => ?_, fun i s result s' => ?_,
    fun v exp s result s' => ?_, fun v name s result s' => ?_,
    fun v exp s result s' => ?_, fun b dst src s result s' => ?_,
    fun exp v s result s' => ?_, fun n ms s result s' => ?_,
    fun n s result s' => ?_, fun label s result s' => ?_,
    fun label s result s' => ?_, fun destination source s result s' => ?_,
    fun ptr len dptr dlen names s result s' => ?_,
    fun r1 r2 s result s' => ?_, fun r1 r2 s result s' => ?_,
    fun function ptr1 len1 ptr2 len2 names s result s' => ?_,
    fun op v exp s result s' => ?_⟩
  all_goals
    intro h
    have hs' : s' = (evaluate _ s).2 := (Prod.ext_iff.mp h).2.symm
    rw [hs']
    exact evaluate_const_clock s _ (by rfl)

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_add_clock`, by recursion on HOL's
    termination measure. -/
theorem evaluate_add_clock_aux (e : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      (evaluate p s).1 ≠ some .timeOut →
      evaluate p { s with clock := s.clock + e } =
        ((evaluate p s).1, { (evaluate p s).2 with clock := (evaluate p s).2.clock + e })
  | .tick, s, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [ht, ht]
      by_cases hz : s.clock = 0
      · simp [hz] at h
      · simp only [hz, if_false]
        rw [if_neg (by simp; omega)]
        simp only [decClock]
        rw [show s.clock + e - 1 = s.clock - 1 + e by omega]
  | .mustTerminate q, s, _ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      by_cases hz : s.termdep = 0
      · simp [hz]
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
        | none => rfl
        | some x => cases x <;> rfl
  | .seq c1 c2, s, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [ht, ht]
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at h
      have hc := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        simp only at h ⊢
        rw [evaluate_add_clock_aux e c1 s (by rw [h1]; simp), h1]
        simp only
        exact evaluate_add_clock_aux e c2 s1 h
      | some x =>
        simp only at h ⊢
        rw [evaluate_add_clock_aux e c1 s (by rw [h1]; exact h), h1]
  | .ite cmp r1 ri c1 c2, s, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [ht, ht]
      have hv : getVar r1 { s with clock := s.clock + e } = getVar r1 s := rfl
      have hi : getVarImm ri { s with clock := s.clock + e } = getVarImm ri s := by
        cases ri <;> rfl
      rw [hv, hi]
      rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
        simp only [hx, hy] at h ⊢
      rcases hw : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hw] at h ⊢
      · exact evaluate_add_clock_aux e c2 s h
      · exact evaluate_add_clock_aux e c1 s h
  | .loop names c exitNames, s, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht] at h
      rw [ht, ht, cutState_withClock]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · rfl
      simp only [hcs, Option.map_some] at h ⊢
      have hc2 := cutState_clock_termdep _ _ _ hcs
      rw [← hc2.1]
      rcases hb : evaluate c s' with ⟨rb, s1⟩
      rw [hb] at h
      have hc := evaluate_clock c s' rb s1 hb
      have hrb : rb ≠ some .timeOut := by
        intro hr
        subst hr
        simp [wordSemContLoop, wordSemExitLoop] at h
      rw [evaluate_add_clock_aux e c s' (by rw [hb]; exact hrb), hb]
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true] at h ⊢
        by_cases hz : s1.clock = 0
        · simp [hz] at h
        · simp only [hz, if_false, wordSemSTOP] at h ⊢
          rw [if_neg (by simp; omega)]
          have hd : decClock { s1 with clock := s1.clock + e } =
              { decClock s1 with clock := (decClock s1).clock + e } := by
            simp only [decClock]
            rw [show s1.clock + e - 1 = s1.clock - 1 + e by omega]
          rw [hd]
          exact evaluate_add_clock_aux e (.loop names c exitNames) (decClock s1) h
      · simp only [hcont, Bool.false_eq_true, if_false] at h ⊢
        rcases rb with _ | x
        · simp [wordSemContLoop] at hcont
        · cases x with
          | «break» n =>
            by_cases hn : n = 0
            · subst hn
              simp only at h ⊢
              rw [cutState_withClock]
              rcases hce : cutState (exitNames, .ln) s1 with _ | s2
              · rfl
              · have hc3 := cutState_clock_termdep _ _ _ hce
                simp only [Option.map_some]
                rw [hc3.1]
            · split <;> simp_all
          | _ => rfl
  | .call ret dest args handler, s, h => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht] at h
      rw [ht, ht, getVars_withClock]
      rcases hg : getVars args s with _ | xs
      · rfl
      simp only [hg] at h ⊢
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
      simp only [hbad, Bool.false_eq_true, if_false] at h ⊢
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp only [hf]
      simp only [hf] at h ⊢
      cases ret with
      | none =>
        cases handler with
        | some _ => rfl
        | none =>
          simp only at h ⊢
          by_cases hz : s.clock = 0
          · simp [hz] at h
          simp only [hz, if_false] at h ⊢
          rw [if_neg (by simp; omega)]
          have hd : callEnv args1 ss (decClock { s with clock := s.clock + e }) =
              { callEnv args1 ss (decClock s) with
                clock := (callEnv args1 ss (decClock s)).clock + e } := by
            simp only [callEnv, decClock]
            rw [show s.clock + e - 1 = s.clock - 1 + e by omega]
          rw [hd]
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at h
          have hc := evaluate_clock prog _ rc sc hcv
          have hrc : rc ≠ some .timeOut := by
            intro hr
            subst hr
            simp [wordSemBadFunReturn] at h
          rw [evaluate_add_clock_aux e prog (callEnv args1 ss (decClock s)) (by rw [hcv]; exact hrc),
            hcv]
          simp only
          split <;> rfl
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only at h ⊢
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
        simp only [hdc, if_false] at h ⊢
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · rfl
        simp only [hce] at h ⊢
        by_cases hz : s.clock = 0
        · simp [hz] at h
        simp only [hz, if_false] at h ⊢
        rw [if_neg (by simp; omega)]
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
        rw [hcv] at h
        have hc := evaluate_clock prog _ rc s2 hcv
        have hrc : rc ≠ some .timeOut := by
          intro hr
          subst hr
          simp at h
        rw [evaluate_add_clock_aux e prog _ (by rw [hcv]; exact hrc), hcv]
        simp only
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · rfl
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]
          simp only [hx, if_false] at h ⊢
          rw [popEnv_withClock]
          rcases hp : popEnv s2 with _ | s1
          · rfl
          simp only [hp, Option.map_some] at h ⊢
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
          · have hdom' : sptDomainEqUnion ({ s1 with clock := s2.clock + e } :
                WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
            simp only [hdom, hdom', if_true] at h ⊢
            rw [← hc2.1]
            have hsv : setVars n ys { s1 with clock := s1.clock + e } =
                { setVars n ys s1 with clock := (setVars n ys s1).clock + e } := rfl
            rw [hsv]
            exact evaluate_add_clock_aux e retHandler (setVars n ys s1) h
          · have hdom' : ¬ sptDomainEqUnion ({ s1 with clock := s2.clock + e } :
                WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
            simp only [hdom, hdom', if_false]
            rw [hc2.1]
        · cases handler with
          | none => rfl
          | some hv =>
            obtain ⟨n', hprog, l1', l2'⟩ := hv
            simp only at h ⊢
            by_cases hx : x ≠ WordLocW.loc l1' l2'
            · rw [if_pos hx, if_pos hx]
            simp only [hx, if_false] at h ⊢
            by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
            · have hdom' : sptDomainEqUnion ({ s2 with clock := s2.clock + e } :
                  WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
              simp only [hdom, hdom', if_true] at h ⊢
              have hsv : setVar n' y { s2 with clock := s2.clock + e } =
                  { setVar n' y s2 with clock := (setVar n' y s2).clock + e } := rfl
              rw [hsv]
              exact evaluate_add_clock_aux e hprog (setVar n' y s2) h
            · have hdom' : ¬ sptDomainEqUnion ({ s2 with clock := s2.clock + e } :
                  WordSemStateFiniteExact width C F).locals envs.fst envs.snd := hdom
              simp only [hdom, hdom', if_false]
        · rfl
        · rfl
        · exact absurd rfl hrc
        · rfl
        · rfl
        · rfl
  | .skip, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .move a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .inst a, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .assign a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .get a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .set a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .store a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .alloc a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .storeConsts a b c d f, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .raise a, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | WordLangProgHOL.return a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | WordLangProgHOL.break a, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | WordLangProgHOL.continue a, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .opCurrHeap a b c, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .locValue a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .install a b c d f, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .codeBufferWrite a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .dataBufferWrite a b, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .ffi a b c d f g, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
  | .shareInst a b c, s, _ => by
      rw [evaluate_withClock_const s _ _ rfl, evaluate_const_clock s _ rfl]
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

/-- Exact HOL `wordProps$evaluate_add_clock` (`wordPropsScript.sml:1383-1386`):

    ```
    ∀p s r s'.
      evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
      evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)
    ```

    HOL's free variable `extra` is the outermost binder. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_add_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_add_clock {width : Nat} [NeZero width] {C : Type} {F : Type} (extra : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (r : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate p s = (r, s') ∧ r ≠ some .timeOut →
      evaluate p { s with clock := s.clock + extra } = (r, { s' with clock := s'.clock + extra }) := by
  intro p s r s' ⟨h, hr⟩
  have := evaluate_add_clock_aux extra p s (by rw [h]; exact hr)
  rw [h] at this
  exact this

/-- Exact HOL `wordProps$cont_loop_not_timeout` (`wordPropsScript.sml:1457-1460`):
    a result that continues the loop is never `TimeOut`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "cont_loop_not_timeout"
  (words_as_type_indexed_bitvec)]
theorem contLoopNotTimeout {width : Nat} [NeZero width]
    (res : Option (WordSemResult width)) :
    wordSemContLoop res = true → res ≠ some .timeOut := by
  cases res with
  | none => simp [wordSemContLoop]
  | some r =>
    cases r <;> simp [wordSemContLoop]

/-- Exact HOL `wordProps$evaluate_add_clock_body` (`wordPropsScript.sml:1464-1471`):
    a continuing evaluation keeps the same result under any larger clock. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_add_clock_body"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_add_clock_body {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate c s = (res, s') ∧ wordSemContLoop res = true →
      ∀ extra,
        evaluate c { s with clock := s.clock + extra } =
          (res, { s' with clock := s'.clock + extra }) := by
  intro c s res s' ⟨h, hcont⟩ extra
  exact evaluate_add_clock extra c s res s' ⟨h, contLoopNotTimeout res hcont⟩

end AddClock

end WordSemStateFiniteExact

end Flapjack
