module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DecStack
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! Agreement of source-related roots with the encoded collector stack. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack
local instance : Nonempty DataSem.Value := ⟨.number 0⟩

private theorem joinEnv_values {width : Nat} [NeZero width]
    (env : Spt DataSem.Value) (gc : List (Nat × WordLocW width))
    (valid : ∀ pair ∈ gc, pair.1 ≠ 0 ∧ pair.1 % 2 = 0) :
    (joinEnv env gc).map Prod.snd = gc.map Prod.snd := by
  induction gc with
  | nil => rfl
  | cons pair gc ih =>
    have head := valid pair (by simp)
    have tail : ∀ pair ∈ gc, pair.1 ≠ 0 ∧ pair.1 % 2 = 0 := by
      intro pair member
      exact valid pair (List.mem_cons_of_mem _ member)
    rcases pair with ⟨key, value⟩
    have step : joinEnv env ((key, value) :: gc) =
        (holThe (sptLookup ((key - 2) / 2) env), value) :: joinEnv env gc := by
      simp [joinEnv, head]
    rw [step]
    simp only [List.map_cons]
    rw [ih tail]

/-- All collector roots in related word frames occur in the flattened
source-to-word stack, in the same order. -/
theorem flatStack_values_eq_encStack {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (target : List (WordSemStackFrame width))
    (related : List.Forall₂ stackRel source target) :
    (flatStack source target).map Prod.snd = wordSemEncStack target := by
  induction related with
  | nil => rfl
  | @cons frame wordFrame source target head tail ih =>
    rcases wordFrame with ⟨size, nonGc, gc, handler⟩
    cases frame with
    | env n env =>
      cases handler with
      | none =>
        have keys := (show stackEnvRel n size env nonGc gc from head).1
        simp only [flatStack, List.map_append, wordSemEncStack, ih]
        rw [joinEnv_values env gc keys]
      | some h => simp [stackRel] at head
    | exc n env saved =>
      cases handler with
      | none => simp [stackRel] at head
      | some h =>
        have keys := (show stackEnvRel n size env nonGc gc ∧ h.1 = saved from head).1.1
        simp only [flatStack, List.map_append, wordSemEncStack, ih]
        rw [joinEnv_values env gc keys]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "FILTER_enc_stack_lemma"
  (words_as_type_indexed_bitvec)]
theorem filter_encStack {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (target : List (WordSemStackFrame width))
    (related : List.Forall₂ stackRel source target) :
    ((flatStack source target).map Prod.snd).filter wordSemIsWordLoc =
      (wordSemEncStack target).filter wordSemIsWordLoc := by
  rw [flatStack_values_eq_encStack source target related]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
