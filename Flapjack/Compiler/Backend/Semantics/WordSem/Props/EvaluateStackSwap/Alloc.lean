import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Leaves

/-!
# `evaluate_stack_swap` `Alloc` case

The `Alloc` case of `wordPropsScript.sml:2316-2363` `evaluate_stack_swap`
(proof at `wordPropsScript.sml:2371-2411`). The untagged helpers follow the
HOL case: the pushed frame does not depend on the stack below it,
`gc_s_val_eq` transports the collection to a value-equal stack, the popped
frames coincide by `s_val_and_key_eq`, and `push_env_pop_env_s_key_eq` gives
the key equality with the original stack. They are Flapjack proof
infrastructure for the tagged case.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

section AllocCase

variable {width : Nat} [NeZero width] {C F : Type}

private theorem stackSizeCons' (fr : WordSemStackFrame width)
    (rest : List (WordSemStackFrame width)) :
    wordSemStackSize (fr :: rest) =
      wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize rest) := rfl

/-- Pushing a handler-free frame over a value-equal stack: only the stack below
the new frame changes. -/
theorem pushEnv_none_withStack (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (s : WordSemStateFiniteExact width C F) (xs : List (WordSemStackFrame width))
    (h : sValEq s.stack xs) :
    pushEnv envs none { s with stack := xs } =
      { pushEnv envs none s with
        stack := .stackFrame s.localsSize (sptToAList envs.1)
          (wordSemEnvToList envs.2 s.permute).1 none :: xs } := by
  simp only [pushEnv]
  rw [stackSizeCons', stackSizeCons', sValEqStackSize _ _ h]

/-- The frame popped after a collection over a value-equal stack is the same
frame. -/
theorem popEnv_withStack (g : WordSemStateFiniteExact width C F)
    (fr : WordSemStackFrame width) (gs zs : List (WordSemStackFrame width))
    (hg : g.stack = fr :: gs) :
    popEnv { g with stack := fr :: zs } =
      (popEnv g).map (fun p => { p with stack := zs }) := by
  unfold popEnv
  rw [hg]
  rcases fr with ⟨m, e0, e, _ | ⟨n, l1, l2⟩⟩ <;> rfl

/-- Allocation results under `evaluate_stack_swap`: an error, a normal return
preserving the stack keys and handler, or `NotEnoughSpace` with a flushed state,
each transported to every value-equal stack. -/
theorem alloc_stackSwap (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) :
    (alloc w names s).1 = some .error ∨
    ((alloc w names s).1 = none ∧ sKeyEq s.stack (alloc w names s).2.stack ∧
      (alloc w names s).2.handler = s.handler ∧
      ∀ xs, sValEq s.stack xs →
        ∃ st, alloc w names { s with stack := xs } =
            (none, { (alloc w names s).2 with stack := st }) ∧
          sValEq (alloc w names s).2.stack st ∧ sKeyEq xs st) ∨
    ((alloc w names s).1 = some .notEnoughSpace ∧ (alloc w names s).2.stack = [] ∧
      (alloc w names s).2.locals = .ln ∧
      ∀ xs, sValEq s.stack xs → alloc w names { s with stack := xs } = alloc w names s) := by
  rw [alloc]
  cases hc : wordSemCutEnvs names s.locals with
  | none => exact Or.inl rfl
  | some envs =>
  dsimp only
  have hA := fun xs (hxs : sValEq s.stack xs) =>
    pushEnv_none_withStack (C := C) (F := F) envs (setStore .allocSize (.word w) s) xs hxs
  cases hgc : gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
  | none => exact Or.inl rfl
  | some g =>
  dsimp only
  have hkg := gcSKeyEq _ _ hgc
  obtain ⟨n0, l, ls, opt, hgst, y, hpop, -, -, hky⟩ := pushEnvPopEnvSKeyEq envs none
    (setStore .allocSize (.word w) s) g hkg
  rw [hpop]
  dsimp only
  -- swapped run reaches the same popped state with a transported stack
  have hswap : ∀ xs, sValEq s.stack xs →
      ∃ g' zs, gc (pushEnv envs none (setStore .allocSize (.word w) { s with stack := xs })) =
          some g' ∧ popEnv g' = some { y with stack := zs } ∧
        sValEq y.stack zs ∧ sKeyEq xs zs := by
    intro xs hxs
    have hset : setStore .allocSize (.word w) { s with stack := xs } =
        { setStore .allocSize (.word w) s with stack := xs } := rfl
    rw [hset, hA xs hxs]
    have hvA : sValEq (pushEnv envs none (setStore .allocSize (.word w) s)).stack
        (.stackFrame (setStore .allocSize (.word w) s).localsSize (sptToAList envs.1)
          (wordSemEnvToList envs.2 (setStore .allocSize (.word w) s).permute).1 none :: xs) :=
      ⟨hxs, of_eq_true (sFrameValEqRefl _)⟩
    obtain ⟨z, hgz, hvz, hkz⟩ := gcSValEq _ g _ g ⟨hvA, hgc⟩
    rw [hgz]
    -- the popped frames coincide
    rw [hgst] at hvz
    have hkA : sKeyEq g.stack (pushEnv envs none (setStore .allocSize (.word w) s)).stack :=
      (sKeyEqSym _ _).mp hkg
    cases z with
    | nil => exact absurd hvz (by simp [sValEq])
    | cons fz zs =>
      obtain ⟨hvzs, hfv⟩ := hvz
      obtain ⟨hkzs, hfk⟩ := hkz
      rw [hgst] at hkA
      obtain ⟨-, hfkA⟩ := hkA
      have hfeq : WordSemStackFrame.stackFrame n0 (sptToAList envs.1) l opt = fz := by
        have := sValAndKeyEq [WordSemStackFrame.stackFrame n0 (sptToAList envs.1) l opt] [fz]
          ⟨⟨trivial, hfv⟩, ⟨trivial, ?_⟩⟩
        · exact List.cons.inj this |>.1
        · -- frame keys: via the pushed frame
          have h1 : sKeyEq [WordSemStackFrame.stackFrame n0 (sptToAList envs.1) l opt]
              [WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1)
                (wordSemEnvToList envs.2 s.permute).1 none] := ⟨trivial, hfkA⟩
          have h2 : sKeyEq [fz] [WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1)
                (wordSemEnvToList envs.2 s.permute).1 none] := ⟨trivial, hfk⟩
          exact (sKeyEqTrans _ _ _ ⟨h1, (sKeyEqSym _ _).mp h2⟩).2
      subst hfeq
      have hp := popEnv_withStack g _ ls zs hgst
      rw [hpop] at hp
      refine ⟨_, zs, rfl, hp, ?_, (sKeyEqSym _ _).mp hkzs⟩
      have hys : y.stack = ls := by
        unfold popEnv at hpop
        rw [hgst] at hpop
        rcases opt with _ | ⟨_, _, _⟩ <;>
          (simp only [Option.some.injEq] at hpop; subst hpop; rfl)
      rw [hys]
      exact hvzs
  have hhy : y.handler = s.handler := by
    unfold popEnv at hpop
    rw [hgst] at hpop
    have hgh : g.handler = s.handler := by
      unfold gc at hgc
      simp only at hgc
      split at hgc
      · cases hgc
      · split at hgc
        · cases hgc
        · simp only [Option.some.injEq] at hgc; subst hgc; rfl
    have hopt : opt = none := by
      have := hkg
      rw [hgst] at this
      obtain ⟨-, hf⟩ := this
      exact ((sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp hf).2.1.symm
    subst hopt
    simp only [Option.some.injEq] at hpop
    subst hpop
    exact hgh
  cases hst : getStore .allocSize y with
  | none => exact Or.inl rfl
  | some a =>
  dsimp only
  cases hsp : hasSpace a y with
  | none => exact Or.inl rfl
  | some b =>
  cases b with
  | true =>
    refine Or.inr (Or.inl ⟨rfl, ?_, hhy, fun xs hxs => ?_⟩)
    · exact (sKeyEqTrans _ _ _ ⟨of_eq_true (sKeyEqRefl _), hky⟩)
    · obtain ⟨g', zs, hg', hp', hv, hk⟩ := hswap xs hxs
      refine ⟨zs, ?_, hv, hk⟩
      rw [alloc, hc]
      dsimp only
      rw [hg']
      dsimp only
      rw [hp']
      dsimp only
      have : getStore .allocSize { y with stack := zs } = getStore .allocSize y := rfl
      rw [this, hst]
      dsimp only
      have : hasSpace a { y with stack := zs } = hasSpace a y := rfl
      rw [this, hsp]
  | false =>
    refine Or.inr (Or.inr ⟨rfl, rfl, rfl, fun xs hxs => ?_⟩)
    obtain ⟨g', zs, hg', hp', -, -⟩ := hswap xs hxs
    rw [alloc, hc]
    dsimp only
    rw [hg']
    dsimp only
    rw [hp']
    dsimp only
    have : getStore .allocSize { y with stack := zs } = getStore .allocSize y := rfl
    rw [this, hst]
    dsimp only
    have : hasSpace a { y with stack := zs } = hasSpace a y := rfl
    rw [this, hsp]
    rfl

/-- The `evaluate_stack_swap` conclusion for `Alloc`. -/
theorem stackSwapPost_alloc (n : Nat) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) :
    stackSwapPost (.alloc n names : WordLangProgHOL (BitVec width)) s := by
  have hsw : ∀ xs, evaluate (.alloc n names : WordLangProgHOL (BitVec width))
      { s with stack := xs } =
      match getVar n s with
      | some (.word w) => alloc w names { s with stack := xs }
      | _ => (some .error, { s with stack := xs }) := by
    intro xs; rw [evaluate]; rfl
  unfold stackSwapPost
  rw [evaluate]
  cases hv : getVar n s with
  | none => trivial
  | some x =>
  cases x with
  | loc _ _ => trivial
  | word w =>
  dsimp only
  simp only [hv] at hsw
  rcases alloc_stackSwap w names s with he | ⟨he, hk, hh, hx⟩ | ⟨he, hk, hl, hx⟩
  · rcases ha : alloc w names s with ⟨r, s1⟩
    rw [ha] at he
    dsimp only at he
    subst he
    trivial
  · rcases ha : alloc w names s with ⟨r, s1⟩
    rw [ha] at he hk hh hx
    dsimp only at he hk hh hx
    subst he
    refine ⟨hk, hh, fun xs hxs => ?_⟩
    rw [hsw]
    exact hx xs hxs
  · rcases ha : alloc w names s with ⟨r, s1⟩
    rw [ha] at he hk hl hx
    dsimp only at he hk hl hx
    subst he
    exact ⟨hk, hl, fun xs hxs => by rw [hsw]; exact hx xs hxs⟩

end AllocCase

namespace EvaluateStackSwapAllocWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapAllocWitnesses

open EvaluateStackSwapAllocWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Alloc` case
(proof `wordPropsScript.sml:2371-2411`): the HOL conclusion at `Alloc n names`,
for every state; no sub-program and no extra premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackSwap_Alloc {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (names : WordLangCutsetsHOL) :
    ∀ s : WordSemStateFiniteExact width C F,
      stackSwapPost (.alloc n names : WordLangProgHOL (BitVec width)) s :=
  fun s => stackSwapPost_alloc n names s

end WordSemStackEq

end Flapjack
