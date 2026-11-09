module

public import Flapjack.Compiler.Backend.ClosKnown.Merge
public import Flapjack.Compiler.Backend.ClosKnownProps.Merge
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Misc.ListEl
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! The source approximation-to-value relation for known closures. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosSem

/-- An approximation is sound for a closure-language runtime value. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_val"]
inductive ValApproxVal : ValApprox → Value → Prop where
  | other (v : Value) : ValApproxVal .other v
  | int (i : Int) : ValApproxVal (.int i) (.number i)
  | tuple (tag : Nat) (approxs : List ValApprox) (values : List Value) :
      List.Forall₂ ValApproxVal approxs values → ValApproxVal (.tuple tag approxs) (.block tag values)
  | closNoInline (loc arity : Nat) (env : List Value) (body : ClosLang.Exp) :
      ValApproxVal (.closNoInline loc arity) (.closure (some loc) [] env arity body)
  | recNoInline (loc arity base : Nat) (env : List Value) (fns : List (Nat × ClosLang.Exp))
      (index : Nat) (h : loc = base + 2 * index ∧ index < fns.length ∧
        arity = (@Flapjack.holEl (Nat × ClosLang.Exp) ⟨(0, .var .none 0)⟩ index fns).1) :
      ValApproxVal (.closNoInline loc arity) (.recclosure (some base) [] env fns index)
  | clos (loc arity size : Nat) (body : ClosLang.Exp) (env : List Value) :
      ValApproxVal (.clos loc arity body size) (.closure (some loc) [] env arity body)

/-- Pairwise merge preserves a pointwise relation when each left element
does. This is proof infrastructure. -/
private theorem mergeListRel (as : List ValApprox) (vs : List Value) (bs : List ValApprox)
    (rel : List.Forall₂ ValApproxVal as vs) (lengthEq : as.length = bs.length)
    (step : ∀ a ∈ as, ∀ v, ValApproxVal a v → ∀ b, ValApproxVal (mergeHOL a b) v) :
    List.Forall₂ ValApproxVal (mergeListHOL as bs) vs := by
  induction rel generalizing bs with
  | nil => cases bs <;> simp_all [mergeListHOL]
  | cons h rest ih =>
    cases bs with
    | nil => simp at lengthEq
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at lengthEq
      rw [mergeListHOL]
      apply List.Forall₂.cons (step _ (by simp) _ h b)
      exact ih bs lengthEq (fun a ha => step a (by simp [ha]))

/-- Merging another approximation preserves a value described by the first. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_val_merge_I_lemma"]
theorem valApproxValMergeLeft (a : ValApprox) (v : Value) (h : ValApproxVal a v) :
    ∀ b, ValApproxVal (mergeHOL a b) v := by
  have all : ∀ n (a : ValApprox) (v : Value), sizeOf a < n → ValApproxVal a v →
      ∀ b, ValApproxVal (mergeHOL a b) v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a v bound rel b
      cases rel with
      | other v => cases b <;> simp [mergeHOL, ValApproxVal.other]
      | int i =>
        cases b <;> simp [mergeHOL, ValApproxVal.other, ValApproxVal.int]
        case int j => split <;> simp [ValApproxVal.other, ValApproxVal.int]
      | tuple tag as vs rel =>
        cases b <;> simp [mergeHOL, ValApproxVal.other, ValApproxVal.tuple, rel]
        case tuple tag' bs =>
          split
          · apply ValApproxVal.tuple
            apply mergeListRel as vs bs rel
            · simp_all
            · intro child member value childRel otherApprox
              have small := List.sizeOf_lt_of_mem member
              have childBound : sizeOf child + 1 < n := by
                simp only [ValApprox.tuple.sizeOf_spec] at bound
                omega
              exact (ih (sizeOf child + 1) childBound) child value (by omega) childRel otherApprox
          · exact ValApproxVal.other _
      | closNoInline loc arity env body =>
        cases b <;> simp [mergeHOL, ValApproxVal.other, ValApproxVal.closNoInline]
        case closNoInline l a => split <;> simp [ValApproxVal.other, ValApproxVal.closNoInline]
      | recNoInline loc arity base env fns index recConditions =>
        cases b <;> simp [mergeHOL, ValApproxVal.other, ValApproxVal.recNoInline, recConditions]
        case closNoInline l a =>
          split <;> simp [ValApproxVal.other, ValApproxVal.recNoInline, recConditions]
      | clos loc arity size body env =>
        cases b <;> simp [mergeHOL, ValApproxVal.other, ValApproxVal.clos]
        case clos l a b' sz => split <;> simp [ValApproxVal.other, ValApproxVal.clos]
  exact all (sizeOf a + 1) a v (by omega) h

/-- Merging either sound approximation remains sound for the same value. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_val_merge_I"]
theorem valApproxValMerge (a1 : ValApprox) (v : Value) (a2 : ValApprox)
    (h : ValApproxVal a1 v ∨ ValApproxVal a2 v) : ValApproxVal (mergeHOL a1 a2) v := by
  rcases h with h | h
  · exact valApproxValMergeLeft a1 v h a2
  · rw [ClosKnownProps.mergeComm a1 a2]
    exact valApproxValMergeLeft a2 v h a1

end Flapjack.Compiler.Backend.ClosKnown
