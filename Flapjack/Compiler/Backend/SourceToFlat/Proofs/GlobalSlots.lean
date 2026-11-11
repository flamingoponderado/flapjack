module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.AllocDefsLookup

@[expose] public section

/-! Extract a reserved global slot block and use it in the declaration step.
The source oracle and its complete index invariant are not yet represented here;
the free-range condition is the portion needed to extract the blank slots. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- A bounded range containing only empty slots splits into a prefix, a block
of empty slots, and a suffix. -/
theorem split_blank_slots {α : Type} (slots : List (Option α)) (start count : Nat)
    (bound : start + count ≤ slots.length)
    (blank : ∀ i, start ≤ i → i < start + count → slots[i]?.getD none = none) :
    ∃ pre post, slots = pre ++ (List.replicate count none ++ post) ∧ pre.length = start := by
  induction slots generalizing start count with
  | nil =>
    have : start = 0 ∧ count = 0 := by simp at bound; omega
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨[], [], by simp, rfl⟩
  | cons head tail ih =>
    cases start with
    | zero =>
      cases count with
      | zero => exact ⟨[], head :: tail, by simp, rfl⟩
      | succ count =>
        have emptyHead : head = none := by
          have h := blank 0 (by omega) (by omega)
          simpa using h
        have tailBound : count ≤ tail.length := by simp at bound; omega
        have tailBlank : ∀ i, 0 ≤ i → i < 0 + count → tail[i]?.getD none = none := by
          intro i _ hi
          have h := blank (i + 1) (by omega) (by omega)
          simpa using h
        obtain ⟨pre, post, split, size⟩ := ih 0 count (by simpa using tailBound) tailBlank
        have : pre = [] := by
          cases pre with
          | nil => rfl
          | cons _ _ => simp at size
        subst pre
        refine ⟨[], post, ?_, rfl⟩
        simpa [emptyHead, List.replicate_succ] using congrArg (fun xs => head :: xs) split
    | succ start =>
      have tailBound : start + count ≤ tail.length := by simp at bound; omega
      have tailBlank : ∀ i, start ≤ i → i < start + count → tail[i]?.getD none = none := by
        intro i lo hi
        have h := blank (i + 1) (by omega) (by omega)
        simpa using h
      obtain ⟨pre, post, split, size⟩ := ih start count tailBound tailBlank
      refine ⟨head :: pre, post, ?_, by simp [size]⟩
      simpa using congrArg (fun xs => head :: xs) split

end Flapjack.Compiler.Backend.SourceToFlat
