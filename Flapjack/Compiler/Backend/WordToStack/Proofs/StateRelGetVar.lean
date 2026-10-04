import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.WordGcFunctions
import Flapjack.Misc.ListEl
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-!
# `state_rel` variable lookup: `state_rel_get_var_imp` family

The three register/stack-slot lookup consequences of the full Word-to-Stack
`state_rel` (`word_to_stackProofScript.sml:2868-2910`).
-/

namespace Flapjack.WordToStackProofs.StateRelGetVar
open Flapjack.Compiler.Encoders.Asm

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- The local-placement conjunct of `stateRel`; Flapjack projection helper with
no separate HOL original. -/
theorem stateRel_locals {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f f' : Nat}
    {s : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (h : stateRel ac k f f' s t lens extra) :
    ∀ n v, sptLookup n s.locals = some v →
      n % 2 = 0 ∧
      if n / 2 < k then t.regs.lookup (n / 2) = some v
      else ((t.stack.drop (t.stackSpace + extra)).take f)[f - 1 - (n / 2 - k)]? = some v ∧
        n / 2 < k + f' := by
  unfold stateRel at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Exact HOL `state_rel_get_var_imp` (`word_to_stackProofScript.sml:2868-2882`).
All relation parameters, including the frame sizes and `extra`, stay arbitrary;
HOL `FLOOKUP t.regs x` is the canonical register map's lookup. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelGetVarImp {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) (extra x : Nat)
    (v : WordLocW width) :
    stateRel ac k f f' s t lens extra ∧ WordSemStateFiniteExact.getVar (2 * x) s = some v ∧
      x < k → t.regs.lookup x = some v := by
  rintro ⟨related, lookup, lt⟩
  have h := stateRel_locals related (2 * x) v lookup
  have hx : 2 * x / 2 = x := by omega
  rw [hx, if_pos lt] at h
  exact h.2

/-- Exact HOL `state_rel_get_var_imp'` (`word_to_stackProofScript.sml:2884-2893`).
Both `get_var`s are the native WordSem and StackSem lookups. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelGetVarImp' {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) (extra n : Nat)
    (v : WordLocW width) :
    stateRel ac k f f' s t lens extra ∧ WordSemStateFiniteExact.getVar n s = some v ∧
      n % 2 = 0 ∧ n / 2 < k → StackSemStateOps.getVar (n / 2) t = some v := by
  rintro ⟨related, lookup, even, lt⟩
  have hn : n = 2 * (n / 2) := by omega
  rw [hn] at lookup
  exact stateRelGetVarImp ac k f f' s t lens extra (n / 2) v ⟨related, lookup, lt⟩

/-- Exact HOL `state_rel_get_var_imp2` (`word_to_stackProofScript.sml:2895-2915`).
HOL's total `EL` is `holEl`; the relation is at `extra = 0` as in HOL. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelGetVarImp2 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) (x : Nat)
    (v : WordLocW width) :
    stateRel ac k f f' s t lens 0 ∧ WordSemStateFiniteExact.getVar (2 * x) s = some v ∧
      ¬ x < k → holEl (t.stackSpace + (f + k - (x + 1))) t.stack = v := by
  rintro ⟨related, lookup, nlt⟩
  have h := stateRel_locals related (2 * x) v lookup
  have hx : 2 * x / 2 = x := by omega
  rw [hx, if_neg nlt] at h
  obtain ⟨-, slot, bound⟩ := h
  have hi : f - 1 - (x - k) = f + k - (x + 1) := by omega
  rw [hi, Nat.add_zero, List.getElem?_take, List.getElem?_drop] at slot
  split at slot
  · obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp slot
    rw [holEl_eq_getElem _ _ hlt, heq]
  · cases slot

end Flapjack.WordToStackProofs.StateRelGetVar
