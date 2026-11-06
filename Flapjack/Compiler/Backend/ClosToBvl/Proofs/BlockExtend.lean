import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockCompare

/-! Block extension in the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon

private theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {xs zs : List α} {ys ws : List β} (first : List.Forall₂ R xs ys)
    (second : List.Forall₂ R zs ws) : List.Forall₂ R (xs ++ zs) (ys ++ ws) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Block extension preserves the prefix and selected slice of related fields. -/
theorem blockExtend_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (tag : Nat) (args : List ClosSem.Value) (targets : List BvlSem.Value)
    (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targets)
    (value : ClosSem.Value)
    (run : ClosSem.doApp (.blockOp (.consExtend tag)) args s = .val (value, next)) :
    ∃ targetValue, BvlSem.doApp (.blockOp (.consExtend (closTagShift tag))) targets t = .val (targetValue, t) ∧
      next = s ∧ vRel s.maxApp f t.refs t.code value targetValue := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyBlock] at run
  | cons a rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyBlock] at run
    | cons b rest =>
      cases rest with
      | nil => simp [ClosSem.doApp, ClosSem.applyBlock] at run
      | cons c rest =>
        cases rest with
        | nil => simp [ClosSem.doApp, ClosSem.applyBlock] at run
        | cons d initial =>
          cases a <;> simp [ClosSem.doApp, ClosSem.applyBlock] at run
          cases b <;> try simp at run
          cases c <;> try simp at run
          cases d <;> try simp at run
          rename_i oldTag fields lower len total
          cases related with
          | cons blockRel tail =>
            obtain ⟨targetFields, rfl, fieldsRel⟩ := vRel_block_inv blockRel
            cases tail with
            | cons lowerRel tail =>
              have lowerEq := vRel_number_inv lowerRel
              subst_vars
              cases tail with
              | cons lenRel tail =>
                have lenEq := vRel_number_inv lenRel
                subst_vars
                cases tail with
                | @cons _ targetTotal _ targetInitial totalRel initialRel =>
                  have totalEq := vRel_number_inv totalRel
                  subst targetTotal
                  have lengths := fieldsRel.length_eq
                  have initialLengths := initialRel.length_eq
                  split at run
                  · simp at run
                  · rename_i guard
                    split at guard
                    · simp at guard
                    · rename_i invalid
                      simp only [Option.some.injEq] at guard
                      subst_vars
                      have invalidTarget : ¬(lower < 0 ∨ len < 0 ∨ Int.ofNat targetFields.length < lower + len ∨
                          total = 0 ∨ total ≠ Int.ofNat targetInitial.length + len) := by
                        simpa [lengths, initialLengths] using invalid
                      simp only [Result.val.injEq, Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have resultRel : List.Forall₂ (vRel s.maxApp f t.refs t.code)
                          (initial ++ (fields.drop lower.toNat).take len.toNat)
                          (targetInitial ++ (targetFields.drop lower.toNat).take len.toNat) :=
                        forall₂_append initialRel (List.forall₂_take _ (List.forall₂_drop _ fieldsRel))
                      refine ⟨.block (closTagShift tag) _, ?_, rfl, .block resultRel⟩
                      simp only [BvlSem.doApp, BvlSem.applyBlock]
                      split_ifs; rfl
/-- Failures of closure block primitives are type errors. -/
theorem blockOp_error {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.blockOp op) args s = .err error) : error = .abort .typeError := by
  cases h : ClosSem.applyBlock op args s with
  | none => simpa [ClosSem.doApp, h] using run.symm
  | some pair => simp [ClosSem.doApp, h] at run

end Flapjack.Compiler.Backend.ClosToBvl
