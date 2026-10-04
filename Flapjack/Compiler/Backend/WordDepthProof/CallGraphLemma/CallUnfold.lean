import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Motive
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap

/-!
# `max_depth_call_graph_lemma`: `Call` unfolding support

Flapjack infrastructure for the `Call` case: the evaluator's `Call` clause
under its successful argument/code lookups, the `find_code` lookup for a
named destination, and small `subspt`/`option_le` facts.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

theorem findCode_some_dest {width : Nat} [NeZero width] {Code StackSize : Type}
    {d : Nat} {argsR args1 : List (WordLocW width)} {code : Spt (Nat × Code)}
    {ssize : Spt StackSize} {prog : Code} {ss : Option StackSize}
    (h : wordSemFindCode (some d) argsR code ssize = some (args1, prog, ss)) :
    (∃ a, sptLookup d code = some (a, prog)) ∧ ss = sptLookup d ssize ∧ args1 = argsR := by
  simp only [wordSemFindCode] at h
  rcases hl : sptLookup d code with _ | ⟨a, e⟩
  · simp [hl] at h
  · simp only [hl] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨⟨a, rfl⟩, rfl, rfl⟩
    · cases h

theorem subspt_lookup_some {α : Type} {a b : Spt α} (h : sptSubspt a b) {k : Nat} {v : α}
    (hk : sptLookup k a = some v) : sptLookup k b = some v :=
  (sptSubsptLookup a b).mp h k v hk

theorem optionLe_ne_none {a b : Option Nat} (h : optionLe a b) (hb : b ≠ none) : a ≠ none := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp_all [optionLe]

theorem wordSemLastN_length_succ {α : Type} (x : α) (xs : List α) :
    wordSemLastN (xs.length + 1) (x :: xs) = x :: xs := by
  simp [wordSemLastN, List.take_of_length_le]

/-- The tail-call (`ret = NONE`, `handler = NONE`) branch of `evaluate`'s `Call`
clause after successful argument and code lookups and a nonzero clock. -/
theorem evaluate_call_tail {width : Nat} [NeZero width] {C F : Type}
    {dest : Option Nat} {args : List Nat} {s : WordSemStateFiniteExact width C F}
    {xs args1 : List (WordLocW width)} {prog : WordLangProgHOL (BitVec width)} {ss : Option Nat}
    (hg : WordSemStateFiniteExact.getVars args s = some xs) (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize =
      some (args1, prog, ss)) (hz : s.clock ≠ 0) :
    evaluate (.call none dest args none) s =
      (if wordSemBadFunReturn (evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))).1 then
        (some .error, (evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))).2)
      else evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hz]

end Flapjack.Compiler.Backend.WordDepthProof
