module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-!
# wordProps `evaluate_option_le_stack_max_preserved`

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4026-4283`:
if the frame-size bound `stack_size s.stack + s.locals_size` is below
`s.stack_max`, the same bound holds of the final state of any evaluation.
HOL proves it by `recInduct evaluate_ind`; here it is one recursion on HOL's
termination measure, following the clauses of `evaluate`.

The cases use the same helper facts as HOL: `flush_state`, `pop_env`,
`push_call` and `set_store` preservation, `stack_size_some_at_least_one`,
`LASTN_stack_size_SOME` and the `gc`/`dec_stack` constants of the `Alloc`
clause.  HOL's `OPTION_MAP2 $+` is `wordSemOptionAdd`.

Inherited assumption: `evaluate`'s `Inst` clause calls the tagged `inst`,
which carries `(reals_as_rational_cuts)` for its `FPSqrt` rendering; the
theorem records that inherited `docs/SOUNDNESS.md` item 8 assumption in the
theorem map.  No numerical floating-point claim is made.
-/

namespace Flapjack

namespace WordSemEvaluateStackMaxPreservedSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateStackMaxPreservedSupport

namespace WordSemStateFiniteExact

open Flapjack.Compiler.Backend.BackendProps

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- The frame-size bound that HOL's `evaluate_option_le_stack_max_preserved`
    carries: the stack size plus the locals size is below `stack_max`.
    Flapjack infrastructure toward that theorem; no separate HOL original. -/
def StackMaxOk (s : WordSemStateFiniteExact width C F) : Prop :=
  optionLe (wordSemOptionAdd (wordSemStackSize s.stack) s.localsSize) s.stackMax

/-- `StackMaxOk` depends only on the stack, the locals size and the stack
    maximum.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_congr {s t : WordSemStateFiniteExact width C F}
    (hstack : t.stack = s.stack) (hlocals : t.localsSize = s.localsSize)
    (hmax : t.stackMax = s.stackMax) : StackMaxOk s → StackMaxOk t := by
  intro h
  unfold StackMaxOk at h ⊢
  rwa [hstack, hlocals, hmax]

/-- `set_var` leaves the frame-size bound alone.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_setVar (n : Nat) (v : WordLocW width)
    (s : WordSemStateFiniteExact width C F) :
    StackMaxOk (setVar n v s) ↔ StackMaxOk s := by
  unfold StackMaxOk setVar
  simp

/-- `set_vars` leaves the frame-size bound alone.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_setVars (names : List Nat) (values : List (WordLocW width))
    (s : WordSemStateFiniteExact width C F) :
    StackMaxOk (setVars names values s) ↔ StackMaxOk s := by
  unfold StackMaxOk setVars
  simp

/-- `set_store` leaves the frame-size bound alone.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_setStore (v : WordStoreHOL) (x : WordLocW width)
    (s : WordSemStateFiniteExact width C F) :
    StackMaxOk (setStore v x s) ↔ StackMaxOk s := by
  unfold StackMaxOk setStore
  simp

/-- Taking a clock tick leaves the frame-size bound alone.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem stackMaxOk_decClock (s : WordSemStateFiniteExact width C F) :
    StackMaxOk (decClock s) ↔ StackMaxOk s := by
  unfold StackMaxOk decClock
  simp

/-- `cut_state` only rewrites the locals, so the frame-size bound survives.
    Flapjack infrastructure toward `evaluate_option_le_stack_max_preserved`;
    no separate HOL original. -/
theorem stackMaxOk_cutState {names : WordLangCutsetsHOL}
    {s t : WordSemStateFiniteExact width C F} (h : cutState names s = some t) :
    StackMaxOk s → StackMaxOk t := by
  obtain ⟨_, rfl⟩ := cutStateConst _ _ _ h
  exact fun h' => h'

/-- `flush_state` keeps the frame-size bound below `stack_max`; this is HOL's
    `flush_state_option_le_stack_max_preserved` restated for `StackMaxOk`.
    Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_flushState (all : Bool) {s : WordSemStateFiniteExact width C F}
    (h : StackMaxOk s) : StackMaxOk (flushState all s) := by
  have := flushStateOptionLeStackMaxPreserved s all h
  simpa only [StackMaxOk] using this

/-- `call_env` sets `stack_max` from its own stack size and locals size, so
    the frame-size bound holds of any call state.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_callEnv (args : List (WordLocW width)) (sz : Option Nat)
    (s : WordSemStateFiniteExact width C F) : StackMaxOk (callEnv args sz s) := by
  simp only [StackMaxOk, callEnv, wordSemOptionMax_eq]
  rw [optionLe_max_right]
  exact Or.inr (optionLe_refl _)

/-- Adding an unknown size on the right gives an unknown size.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem wordSemOptionAdd_none_right (a : Option Nat) : wordSemOptionAdd a none = none := by
  rcases a with _ | x <;> rfl

/-- Adding an unknown size on the left gives an unknown size.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem wordSemOptionAdd_none_left (a : Option Nat) : wordSemOptionAdd none a = none := by
  rcases a with _ | x <;> rfl

/-- A stack size plus any locals size is at least one, in the `option_le`
    order.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem optionLe_one_optionAdd (stack : List (WordSemStackFrame width)) (sz : Option Nat) :
    optionLe (some 1) (wordSemOptionAdd (wordSemStackSize stack) sz) := by
  rcases sz with _ | z
  · rw [wordSemOptionAdd_none_right]
    exact trivial
  · rcases hs : wordSemStackSize stack with _ | y
    · rw [wordSemOptionAdd_none_left]
      exact trivial
    · have := stackSizeSomeAtLeastOne stack y hs
      simp only [wordSemOptionAdd, optionLe]
      omega

/-- `fix_clock` only rewrites the clock and the term dependency, so it keeps
    the frame-size bound.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_fixClock {s t : WordSemStateFiniteExact width C F}
    (r : Option (WordSemResult width)) (h : StackMaxOk t) :
    StackMaxOk (fixClock s (r, t)).2 := by
  simp only [fixClock, StackMaxOk] at h ⊢
  exact h

/-- The stack size of a cons.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem wordSemStackSize_cons (fr : WordSemStackFrame width)
    (rest : List (WordSemStackFrame width)) :
    wordSemStackSize (fr :: rest) =
      wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize rest) := rfl

/-- `dec_stack` rebuilds only the value lists of the frames, so the stack size
    is unchanged.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem decStack_stackSize :
    ∀ (xs : List (WordLocW width)) (stk stk' : List (WordSemStackFrame width)),
      wordSemDecStack xs stk = some stk' → wordSemStackSize stk' = wordSemStackSize stk := by
  intro xs stk
  induction stk generalizing xs with
  | nil =>
    intro stk' h
    cases xs with
    | nil =>
      simp only [wordSemDecStack] at h
      simp only [Option.some.injEq] at h
      subst h
      rfl
    | cons _ _ => simp [wordSemDecStack] at h
  | cons fr rest ih =>
    intro stk' h
    cases fr with
    | stackFrame n l0 l handler =>
      simp only [wordSemDecStack] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i s hstep
          simp only [Option.some.injEq] at h
          subst h
          rw [wordSemStackSize_cons, wordSemStackSize_cons, ih (xs.drop l.length) s hstep]
          cases handler <;> rfl

/-- `dec_stack` of a non-empty stack is non-empty.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem decStack_ne_nil {xs : List (WordLocW width)} {fr : WordSemStackFrame width}
    {st stk' : List (WordSemStackFrame width)}
    (h : wordSemDecStack xs (fr :: st) = some stk') : stk' ≠ [] := by
  cases fr with
  | stackFrame n l0 l handler =>
    simp only [wordSemDecStack] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i s _
        simp only [Option.some.injEq] at h
        subst h
        simp

/-- `dec_stack` keeps a handler-free frame handler-free.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem decStack_cons_none {xs : List (WordLocW width)} {m : Option Nat}
    {e0 e : List (Nat × WordLocW width)} {rest stk' : List (WordSemStackFrame width)}
    (h : wordSemDecStack xs (WordSemStackFrame.stackFrame m e0 e none :: rest) =
      some stk') :
    ∃ (m' : Option Nat) (e0' e' : List (Nat × WordLocW width))
      (rest' : List (WordSemStackFrame width)),
      stk' = WordSemStackFrame.stackFrame m' e0' e' none :: rest' := by
  simp only [wordSemDecStack] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i s _
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨m, _, _, s, rfl⟩

/-- `push_env` without a handler puts one frame on top of the stack.
    Flapjack infrastructure toward `evaluate_option_le_stack_max_preserved`;
    no separate HOL original. -/
theorem pushEnv_none_stack (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (s : WordSemStateFiniteExact width C F) :
    (pushEnv envs none s).stack =
      WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1)
        (wordSemEnvToList envs.2 s.permute).1 none :: s.stack := by
  obtain ⟨l, permute, hl⟩ : ∃ l permute, wordSemEnvToList envs.2 s.permute = (l, permute) :=
    ⟨_, _, rfl⟩
  simp only [pushEnv, hl]

/-- `gc` only rewrites the stack through `dec_stack`.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem gc_stackDec {s g : WordSemStateFiniteExact width C F} (hg : gc s = some g) :
    ∃ wl : List (WordLocW width), wordSemDecStack wl s.stack = some g.stack := by
  unfold gc at hg
  dsimp only at hg
  split at hg
  · simp at hg
  · rename_i wl m st _
    split at hg
    · simp at hg
    · rename_i stack hdec
      simp only [Option.some.injEq] at hg
      subst hg
      exact ⟨wl, hdec⟩

/-- Pushing the allocation frame and collecting leaves `stack_max` at the
    maximum of the incoming bound and the new stack size.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem gcPushEnv_stackMax_eq (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (w : BitVec width) (s g : WordSemStateFiniteExact width C F)
    (hg : gc (pushEnv envs none (setStore .allocSize (.word w) s)) = some g) :
    g.stackMax = wordSemOptionMax (setStore .allocSize (.word w) s).stackMax
      (wordSemStackSize g.stack) := by
  obtain ⟨wl, hdec⟩ := gc_stackDec hg
  have hgc := gcConst _ _ hg
  have hp := pushEnv_stackMax_eq envs none (setStore .allocSize (.word w) s)
  have hstk := pushEnv_none_stack envs (setStore .allocSize (.word w) s)
  rw [hstk] at hdec
  have hsize := decStack_stackSize wl _ _ hdec
  have hstk' : wordSemStackSize (pushEnv envs none (setStore .allocSize (.word w) s)).stack =
      wordSemStackSize (WordSemStackFrame.stackFrame (setStore .allocSize (.word w) s).localsSize
        (sptToAList envs.1) (wordSemEnvToList envs.2 (setStore .allocSize (.word w) s).permute).1
        none :: (setStore .allocSize (.word w) s).stack) := by
    rw [hstk]
  rw [hgc.2.2.2.2.2.2.2.2.2.2.2.1, hp, hstk', hsize]

/-- After the allocation frame is popped, the frame-size bound is below
    `stack_max` when the stack maximum was taken from the stack size.
    Flapjack infrastructure toward `evaluate_option_le_stack_max_preserved`;
    no separate HOL original. -/
theorem stackMaxOk_popEnv_none {s t : WordSemStateFiniteExact width C F} {M : Option Nat}
    {m : Option Nat} {e0 e : List (Nat × WordLocW width)} {rest : List (WordSemStackFrame width)}
    (hstack : s.stack = WordSemStackFrame.stackFrame m e0 e none :: rest)
    (hpop : popEnv s = some t)
    (hmax : s.stackMax = wordSemOptionMax M (wordSemStackSize s.stack)) :
    StackMaxOk t := by
  have hs : s = { s with stack := WordSemStackFrame.stackFrame m e0 e none :: rest } := by
    rw [← hstack]
  rw [hs] at hpop
  simp only [popEnv, Option.some.injEq] at hpop
  rw [← hpop]
  rw [hstack] at hmax
  simp only [StackMaxOk, hmax, wordSemStackSize_cons, wordSemStackSizeFrame]
  rw [wordSemOptionMax_eq, wordSemOptionAdd_comm m (wordSemStackSize rest)]
  rw [optionLe_max_right]
  exact Or.inr (optionLe_refl _)

/-- The allocation frame plus the collected stack keeps the frame-size bound
    below `stack_max` after the frame is popped.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_gcPushEnv_popEnv (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (w : BitVec width) (s g s' : WordSemStateFiniteExact width C F)
    (hg : gc (pushEnv envs none (setStore .allocSize (.word w) s)) = some g)
    (hp : popEnv g = some s') : StackMaxOk s' := by
  obtain ⟨wl, hdec⟩ := gc_stackDec hg
  rw [pushEnv_none_stack] at hdec
  obtain ⟨m', e0', e', rest', hgs⟩ := decStack_cons_none hdec
  exact stackMaxOk_popEnv_none hgs hp (gcPushEnv_stackMax_eq envs w s g hg)

/-- Popping the pushed allocation frame cannot fail.  Flapjack infrastructure
    toward `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem gcPushEnv_popEnv_ne_none (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (w : BitVec width) (s g : WordSemStateFiniteExact width C F)
    (hg : gc (pushEnv envs none (setStore .allocSize (.word w) s)) = some g) :
    popEnv g ≠ none := by
  intro hpn
  obtain ⟨wl, hdec⟩ := gc_stackDec hg
  rw [pushEnv_none_stack] at hdec
  have hne : g.stack ≠ [] := decStack_ne_nil hdec
  cases hgs : g.stack with
  | nil => exact hne hgs
  | cons fr rest =>
    cases fr with
    | stackFrame m e0 e handler =>
      cases handler with
      | none =>
        have hg' : g = { g with stack := WordSemStackFrame.stackFrame m e0 e none :: rest } := by
          rw [← hgs]
        rw [hg'] at hpn
        simp only [popEnv] at hpn
        simp at hpn
      | some h =>
        have hg' : g =
            { g with stack := WordSemStackFrame.stackFrame m e0 e (some h) :: rest } := by
          rw [← hgs]
        rw [hg'] at hpn
        simp only [popEnv] at hpn
        simp at hpn

/-- The `Alloc` clause keeps the frame-size bound: the frame pushed for the
    allocation records the incoming locals size, and popping it after
    collection restores that size.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_alloc (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) (h : StackMaxOk s) :
    StackMaxOk (alloc w names s).2 := by
  unfold alloc
  split
  · exact stackMaxOk_flushState true h
  · rename_i envs _
    split
    · exact stackMaxOk_flushState true h
    · rename_i g hg
      split
      · rename_i hpn
        exact absurd hpn (gcPushEnv_popEnv_ne_none envs w s g hg)
      · rename_i s' hp
        have hok := stackMaxOk_gcPushEnv_popEnv envs w s g s' hg hp
        split
        · exact hok
        · split
          · exact hok
          · exact hok
          · exact stackMaxOk_flushState true hok

/-- `jump_exc` pops the stack down to the frame that holds the handler; the
    returned state keeps that frame's recorded locals size and the frames
    below it.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem jumpExc_spec {s s' : WordSemStateFiniteExact width C F} {l1 l2 : Nat}
    (h : jumpExc s = some (s', l1, l2)) :
    s.handler < s.stack.length ∧
    ∃ (m : Option Nat) (e0 e : List (Nat × WordLocW width)) (xs : List (WordSemStackFrame width))
      (n : Nat),
      wordSemLastN (s.handler + 1) s.stack =
        WordSemStackFrame.stackFrame m e0 e (some (n, l1, l2)) :: xs ∧
      s' = { s with handler := n, locals := sptUnion (sptFromAList e) (sptFromAList e0),
                     stack := xs, localsSize := m } := by
  unfold jumpExc at h
  split at h
  · rename_i hlt
    split at h
    · rename_i m e0 e n l1' l2' xs heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs', hl1, hl2⟩ := h
      subst hl1 hl2
      exact ⟨hlt, m, e0, e, xs, n, heq, hs'.symm⟩
    · cases h
  · cases h

/-- The state HOL's clock-zero returning call returns: the call frame's stack
    maximum with an emptied stack, flushed.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
def callTimeoutState (args : List (WordLocW width)) (sz : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  let y := (callEnv args sz (pushEnv envs handler s)).stackMax
  flushState true { s with stack := [], stackMax := y }

/-- The flushed clock-zero call state keeps the frame-size bound below
    `stack_max`.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_callTimeout (args : List (WordLocW width)) (sz : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    StackMaxOk (callTimeoutState args sz envs handler s) := by
  have hone : optionLe (some 1) (callEnv args sz (pushEnv envs handler s)).stackMax := by
    simp only [callEnv, wordSemOptionMax_eq]
    rw [optionLe_max_right]
    exact Or.inr (optionLe_one_optionAdd _ _)
  simpa only [callTimeoutState, StackMaxOk, flushState, wordSemStackSize, List.foldr_nil,
    wordSemOptionAdd, Nat.add_zero] using hone

/-- A sum of known sizes is known, and so are both summands.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem wordSemOptionAdd_some {a b : Option Nat} {c : Nat}
    (h : wordSemOptionAdd a b = some c) :
    ∃ x y, a = some x ∧ b = some y ∧ x + y = c := by
  rcases a with _ | x
  · rw [wordSemOptionAdd_none_left] at h
    exact absurd h (by simp)
  rcases b with _ | y
  · rw [wordSemOptionAdd_none_right] at h
    exact absurd h (by simp)
  simp only [wordSemOptionAdd, Option.some.injEq] at h
  exact ⟨x, y, rfl, rfl, h⟩

/-- A mapped size of three plus a known size fixes the source size.
    Flapjack infrastructure toward `evaluate_option_le_stack_max_preserved`;
    no separate HOL original. -/
theorem optionMap_add_three {m : Option Nat} {c : Nat}
    (h : Option.map (fun x => 3 + x) m = some c) :
    ∃ c', m = some c' ∧ c = 3 + c' := by
  rcases m with _ | c'
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨c', rfl, h.symm⟩

/-- A state with an unknown stack maximum satisfies the frame-size bound.
    Flapjack infrastructure toward `evaluate_option_le_stack_max_preserved`;
    no separate HOL original. -/
theorem stackMaxOk_of_stackMax_none {s : WordSemStateFiniteExact width C F}
    (h : s.stackMax = none) : StackMaxOk s := by
  simp [StackMaxOk, h, optionLe]

/-- A successful install returns a state whose `stack_max` is unknown, while
    the error branch keeps the incoming state.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_ite_result {r s : WordSemStateFiniteExact width C F}
    (hr : r.stackMax = none) (hs : StackMaxOk s) (c : Prop) [Decidable c] :
    StackMaxOk (if c then (none, r)
      else (some (WordSemResult.error : WordSemResult width), s)).2 := by
  by_cases hc : c
  · rw [if_pos hc]
    exact stackMaxOk_of_stackMax_none hr
  · rw [if_neg hc]
    exact hs

/-- The `ShareInst` clause keeps the frame-size bound: the shared-memory
    operations either rewrite the store or flush the state.  Flapjack
    infrastructure toward `evaluate_option_le_stack_max_preserved`; no
    separate HOL original. -/
theorem stackMaxOk_shareInst (op : WordMemOp) (v : Nat) (ad : BitVec width)
    (s : WordSemStateFiniteExact width C F) (h : StackMaxOk s) :
    StackMaxOk (shareInst (rw := width) op v ad s).2 := by
  cases op <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32] <;>
    (repeat' split) <;>
    first
      | exact h
      | exact stackMaxOk_flushState true h

/-- The `FFI` clause keeps the frame-size bound: the final event flushes the
    state and the returning event only rewrites the memory, locals, FP
    registers and FFI state.  Flapjack infrastructure toward
    `evaluate_option_le_stack_max_preserved`; no separate HOL original. -/
theorem stackMaxOk_ffi (ffiIndex : Flapjack.Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F)
    (h : StackMaxOk s) :
    StackMaxOk (evaluate (.ffi ffiIndex ptr1 len1 ptr2 len2 names) s).2 := by
  rw [evaluate]
  repeat' split
  all_goals first
    | exact h
    | exact stackMaxOk_flushState true h

end Helpers

section Evaluate

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_option_le_stack_max_preserved`, by
    recursion on HOL's termination measure.  The cases follow HOL's
    `evaluate_ind` clauses. -/
theorem stackMaxOk_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      StackMaxOk s → StackMaxOk (evaluate p s).2
  | .tick, s => by
      intro h
      rw [evaluate]
      split
      · exact stackMaxOk_flushState true h
      · exact (stackMaxOk_decClock s).mpr h
  | .mustTerminate q, s => by
      intro h
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]; exact h
      · simp only [hz, dite_false, if_false]
        have hq : StackMaxOk
            { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } :=
          stackMaxOk_congr rfl rfl rfl h
        have ih := stackMaxOk_evaluate q
            { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } hq
        rcases hcv : evaluate q
            { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }
          with ⟨r, s1⟩
        rw [hcv] at ih
        simp only
        cases r with
        | none => exact stackMaxOk_congr rfl rfl rfl ih
        | some x =>
          cases x <;> first
            | exact h
            | exact stackMaxOk_congr rfl rfl rfl ih
  | .seq c1 c2, s => by
      intro h
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      have ih1 := stackMaxOk_evaluate c1 s h
      rcases h1 : evaluate c1 s with ⟨r1, t1⟩
      rw [h1] at ih1
      have hc := evaluate_clock c1 s r1 t1 h1
      dsimp only
      cases r1 with
      | none => exact stackMaxOk_evaluate c2 t1 ih1
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s => by
      intro h
      have ht := (evaluate_def_rebound (width := width) (C := C)
        (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only
      all_goals try exact h
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
      · exact h
      · exact stackMaxOk_evaluate c2 s h
      · exact stackMaxOk_evaluate c1 s h
  | .loop names c exitNames, s => by
      intro h
      have ht := (evaluate_def_rebound (width := width) (C := C)
        (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · exact h
      dsimp only
      have hcut := stackMaxOk_cutState hcs h
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := stackMaxOk_evaluate c s' hcut
      rcases hb : evaluate c s' with ⟨rb, t1⟩
      rw [hb] at ih
      dsimp only
      have hc := evaluate_clock c s' rb t1 hb
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : t1.clock = 0
        · simp only [if_pos hz]
          exact stackMaxOk_flushState true ih
        · simp only [if_neg hz, wordSemSTOP]
          exact stackMaxOk_evaluate (.loop names c exitNames) (decClock t1)
            ((stackMaxOk_decClock t1).mpr ih)
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split
          · exact ih
          · rename_i s2 hce
            exact stackMaxOk_cutState hce ih
        · exact ih
  | .call ret dest args handler, s => by
      intro h
      have ht := (evaluate_def_rebound (width := width) (C := C)
        (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 s ret handler dest args
      rw [ht]
      rcases hg : getVars args s with _ | xs
      · exact h
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
        exact h
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · exact h
      cases ret with
      | none =>
        cases handler with
        | some _ => exact h
        | none =>
          by_cases hz : s.clock = 0
          · simp only [hz, if_true]
            exact stackMaxOk_flushState true h
          simp only [hz, if_false]
          have hcall : StackMaxOk (callEnv args1 ss (decClock s)) :=
            stackMaxOk_callEnv _ _ _
          have ih := stackMaxOk_evaluate prog (callEnv args1 ss (decClock s)) hcall
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          have hc := evaluate_clock prog (callEnv args1 ss (decClock s)) rc sc hcv
          dsimp only
          by_cases hret : wordSemBadFunReturn rc = true
          · simp only [hret, if_true]
            exact ih
          simp only [hret, Bool.false_eq_true, if_false]
          exact ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
          exact h
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact h
        by_cases hz : s.clock = 0
        · simp only [hz, if_true]
          exact stackMaxOk_callTimeout args1 ss envs handler s
        simp only [hz, if_false]
        have hcall : StackMaxOk (callEnv args1 ss (pushEnv envs handler (decClock s))) :=
          stackMaxOk_callEnv _ _ _
        have ih := stackMaxOk_evaluate prog
          (callEnv args1 ss (pushEnv envs handler (decClock s))) hcall
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, sc⟩
        rw [hcv] at ih
        have hc := evaluate_clock prog
          (callEnv args1 ss (pushEnv envs handler (decClock s))) rc sc hcv
        cases rc with
        | none => exact ih
        | some x =>
          cases x with
          | result v ys =>
            dsimp only
            split
            · exact ih
            · split
              · exact ih
              · rename_i s1 hp
                have hp' : StackMaxOk s1 := popEnv_optionLe_stackMax_preserved sc s1 ⟨ih, hp⟩
                have hc2 : s1.clock = sc.clock ∧ s1.termdep = sc.termdep :=
                  ⟨popEnv_clock sc s1 hp, popEnv_termdep sc s1 hp⟩
                split
                · exact stackMaxOk_evaluate retHandler (setVars n ys s1)
                    ((stackMaxOk_setVars _ _ _).mpr hp')
                · exact hp'
          | exception v w =>
            dsimp only
            cases handler with
            | none => exact ih
            | some hv =>
              obtain ⟨n2, hprog, l1', l2'⟩ := hv
              dsimp only
              by_cases hx : v ≠ .loc l1' l2'
              · rw [if_pos hx]
                exact ih
              · rw [if_neg hx]
                by_cases hdom : sptDomainEqUnion sc.locals envs.1 envs.2
                · rw [if_pos hdom]
                  exact stackMaxOk_evaluate hprog (setVar n2 w sc)
                    ((stackMaxOk_setVar _ _ _).mpr ih)
                · rw [if_neg hdom]
                  exact ih
          | «break» k => exact ih
          | «continue» k => exact ih
          | timeOut => exact ih
          | notEnoughSpace => exact ih
          | finalFfi ev => exact ih
          | error => exact ih
  | .skip, s => by
      intro h
      rw [evaluate]
      exact h
  | .alloc n names, s => by
      intro h
      rw [evaluate]
      rcases getVar n s with _ | v
      · exact h
      cases v with
      | word w => exact stackMaxOk_alloc w names s h
      | loc l1 l2 => exact h
  | .storeConsts t1 t2 addr offset words, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .move pri moves, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .inst i, s => by
      intro h
      rw [evaluate]
      split
      · rename_i s1 hi
        exact stackMaxOk_congr (instConstFull i s s1 hi).2.2.2.2.2.2.2.2.1
          (instConstFull i s s1 hi).2.2.2.2.2.2.2.2.2.1
          (instConstFull i s s1 hi).2.2.2.2.2.2.2.2.2.2.2.1 h
      · exact h
  | .assign v exp, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .get v name, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .set v exp, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .opCurrHeap b dst src, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .store exp v, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals first
        | exact h
        | (rename_i s1 hm
           exact stackMaxOk_congr (memStoreConst _ _ s s1 hm).2.2.2.2.2.2.2.2.2.2.2.2.2.1
             (memStoreConst _ _ s s1 hm).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
             (memStoreConst _ _ s s1 hm).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h)
  | .return n ms, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals first
        | exact h
        | exact stackMaxOk_flushState false h
  | .raise n, s => by
      intro h
      rw [evaluate]
      rcases getVar n s with _ | w <;> simp only
      · exact h
      rcases hj : jumpExc s with _ | ⟨s', l1, l2⟩
      · exact h
      simp only
      obtain ⟨hlen, m, e0, e, xs, n', hlastN, hs'⟩ := jumpExc_spec hj
      rw [hs']
      rcases hs : s.stackMax with _ | M
      · simp only [hs, StackMaxOk, optionLe]
      have hb := h
      rw [StackMaxOk, hs] at hb
      rcases hx : wordSemStackSize s.stack with _ | x
      · rw [hx] at hb
        simp only [wordSemOptionAdd, optionLe] at hb
      rcases hl : s.localsSize with _ | b
      · rw [hx, hl] at hb
        simp only [wordSemOptionAdd, optionLe] at hb
      rw [hx, hl] at hb
      simp only [wordSemOptionAdd, optionLe, Option.some.injEq] at hb
      obtain ⟨y, hy, hle⟩ := lastNStackSizeSome (s.handler + 1) s.stack _ x
        ⟨hlastN, hx, by omega⟩
      rw [wordSemStackSize_cons] at hy
      simp only [wordSemStackSizeFrame] at hy
      obtain ⟨c, d, hmap, hxs, hcd⟩ := wordSemOptionAdd_some hy
      obtain ⟨c', hmc, hc3⟩ := optionMap_add_three hmap
      simp only [StackMaxOk, hs, hmc, hxs, wordSemOptionAdd, optionLe]
      omega
  | .break k, s => by
      intro h
      rw [evaluate]
      exact h
  | .continue k, s => by
      intro h
      rw [evaluate]
      exact h
  | .locValue r l1, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .install ptr len dptr dlen names, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals first
        | exact h
        | (simp only [StackMaxOk]
           split_ifs with hc
           · exact trivial
           · exact h)
  | .codeBufferWrite r1 r2, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .dataBufferWrite r1 r2, s => by
      intro h
      rw [evaluate]
      repeat' split
      all_goals exact h
  | .ffi ffiIndex ptr1 len1 ptr2 len2 names, s =>
      stackMaxOk_ffi ffiIndex ptr1 len1 ptr2 len2 names s
  | .shareInst op v exp, s => by
      intro h
      rw [evaluate]
      rcases wordExp s exp with _ | w
      · exact h
      cases w with
      | loc _ _ => exact h
      | word ad => exact stackMaxOk_shareInst op v ad s h
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

/-- Exact HOL `evaluate_option_le_stack_max_preserved`
    (`wordPropsScript.sml:4026-4283`): if the frame-size bound of the incoming
    state is below its `stack_max`, so is the bound of the final state.
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "evaluate_option_le_stack_max_preserved"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_option_le_stack_max_preserved {width : Nat} [NeZero width] {C : Type}
    {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (r : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F),
      evaluate p s = (r, t) ∧
        optionLe (wordSemOptionAdd (wordSemStackSize s.stack) s.localsSize) s.stackMax →
      optionLe (wordSemOptionAdd (wordSemStackSize t.stack) t.localsSize) t.stackMax := by
  intro p s r t ⟨h, hok⟩
  have := stackMaxOk_evaluate p s hok
  rwa [h] at this

end WordSemStateFiniteExact

end Flapjack
