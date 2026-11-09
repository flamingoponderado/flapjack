import Flapjack.Compiler.Backend.BviTmc.Proofs.WellFormed
import Flapjack.Compiler.Backend.BviTmc.Proofs.PureExtraction

/-! Well-formedness of recursive-call extraction results. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

mutual
/-- The singleton conjunct of the source recursive-call invariant. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_wf_inr_lemma"]
theorem extractOne_wf_inr (n loc tag : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (cb : CallBlock)
    (run : extractOneSource n loc tag e = some (bs, .inr cb)) :
    wfBlock bs.length cb ∧ ∃ left child right, cb = .callBlock tag left child right := by
  cases e with
  | call ticks dest args handler =>
    simp only [extractOneSource, callToBlockSource] at run
    split at run
    next =>
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨?_, [], .rCall ticks indices, [], rfl⟩
        simp only [wfBlock]
        exact ⟨wfVars_empty _, by simpa using wfVars_bind args indices 0 last h,
          wfVars_empty _, by decide⟩
    next => simp at run
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons childTag =>
        simp only [extractOneSource] at run
        cases h : extractListSource n loc childTag args with
        | none => simp [h] at run
        | some pair =>
          obtain ⟨bindings, kind⟩ := pair
          cases kind with
          | inl vs => simp only [h] at run; split at run <;> simp_all
          | inr child =>
            have childWf := (extractList_wf_inr n loc childTag args bindings child h).1
            simp only [h, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at run
            obtain ⟨rfl, rfl⟩ := run.symm
            exact ⟨⟨wfVars_empty _, childWf, wfVars_empty _, by decide⟩, [], child, [], rfl⟩
      | _ => simp only [extractOneSource] at run; split at run <;> simp_all
    | _ => simp only [extractOneSource] at run; split at run <;> simp_all
  | _ => simp only [extractOneSource] at run; split at run <;> simp_all
termination_by expBudget e
decreasing_by all_goals simp_all [expBudget]

/-- Recursive-call list extraction returns a well-formed outer frame. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_wf_inr"]
theorem extractList_wf_inr (n loc tag : Nat) (args bs : List Bvi.Exp) (cb : CallBlock)
    (run : extractListSource n loc tag args = some (bs, .inr cb)) :
    wfBlock bs.length cb ∧ ∃ left child right, cb = .callBlock tag left child right := by
  cases args with
  | nil => simp [extractListSource] at run
  | cons x xs =>
    cases xs with
    | nil => exact extractOne_wf_inr n loc tag x bs cb (by simpa [extractListSource] using run)
    | cons y ys =>
      simp only [extractListSource] at run
      cases h : extractListSource n loc tag (y :: ys) with
      | none => simp [h] at run
      | some pair =>
        obtain ⟨tailBs, kind⟩ := pair
        cases kind with
        | inl vs =>
          have tailWf := PureExtraction.extractList_wf_inl n loc tag (y :: ys) tailBs vs h
          cases first : extractOneSource n loc tag x with
          | none => simp [h, first] at run
          | some pair =>
            obtain ⟨firstBs, firstKind⟩ := pair
            cases firstKind with
            | inl indices => simp only [h, first] at run; split at run <;> simp_all
            | inr firstCb =>
              have firstWf := extractOne_wf_inr n loc tag x firstBs firstCb first
              cases firstCb with
              | rCall ticks args => simp [h, first] at run
              | callBlock t left child right =>
                cases left with
                | cons a rest => simp [h, first] at run
                | nil =>
                  cases right with
                  | cons a rest => simp [h, first] at run
                  | nil =>
                    simp [h, first] at run
                    obtain ⟨rfl, rfl⟩ := run.symm
                    refine ⟨?_, [], child, shiftVarsSource firstBs.length vs, rfl⟩
                    simp only [wfBlock, List.length_append]
                    refine ⟨wfVars_empty _, ?_, ?_, ?_⟩
                    · exact wfBlock_expand _ _ child firstWf.1.2.1 (by omega)
                    · simpa [shiftVarsSource, shiftVars] using wfVars_shift tailBs.length firstBs.length vs tailWf.2.1
                    · simpa [shiftVarsSource] using tailWf.2.2
        | inr tailCb =>
          have tailWf := extractList_wf_inr n loc tag (y :: ys) tailBs tailCb h
          obtain ⟨wf, left, child, right, rfl⟩ := tailWf
          simp [h, shiftBlock] at run
          obtain ⟨rfl, rfl⟩ := run.symm
          refine ⟨?_, 0 :: shiftVars 1 left, shiftBlock 1 child, shiftVars 1 right, rfl⟩
          have shifted := wfBlock_shift_sing tailBs.length (.callBlock tag left child right) wf
          simp only [shiftBlock, wfBlock] at shifted ⊢
          exact ⟨wfVars_cons _ 0 _ (by simp) shifted.1, shifted.2⟩
termination_by listBudget args
decreasing_by all_goals simp_all only [listBudget]; omega
end

/-- Every successful top-level conversion produces a well-formed skeleton. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_wf"]
theorem toBlock_wf (n loc : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (cb : CallBlock)
    (run : toBlockSource n loc e = some (bs, cb)) : wfBlock bs.length cb := by
  cases e with
  | call ticks dest args handler =>
    simp only [toBlockSource, callToBlockSource] at run
    split at run
    next =>
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        simpa [wfBlock] using wfVars_bind args indices 0 last h
    next => simp at run
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons tag =>
        simp only [toBlockSource] at run
        cases h : extractListSource n loc tag args with
        | none => simp [h] at run
        | some pair =>
          obtain ⟨bindings, kind⟩ := pair
          cases kind with
          | inl vs => simp [h] at run
          | inr child =>
            have wf := (extractList_wf_inr n loc tag args bindings child h).1
            simp [h] at run
            obtain ⟨rfl, rfl⟩ := run.symm
            exact wf
      | _ => simp [toBlockSource] at run
    | _ => simp [toBlockSource] at run
  | _ => simp [toBlockSource] at run

/-- Successful conversion arises from a constructor or a direct self-call. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_cases"]
theorem toBlock_cases (n loc : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (cb : CallBlock)
    (run : toBlockSource n loc e = some (bs, cb)) :
    (∃ tag args left child right,
      e = .op (.blockOp (.cons tag)) args ∧ cb = .callBlock tag left child right) ∨
    (∃ ticks args vs, e = .call ticks (some loc) args none ∧ cb = .rCall ticks vs) := by
  cases e with
  | call ticks dest args handler =>
    simp only [toBlockSource, callToBlockSource] at run
    split at run
    next same =>
      obtain ⟨rfl, rfl⟩ := same
      cases h : bind 0 args with
      | mk indices last =>
        simp only [h, Option.some.injEq, Prod.mk.injEq] at run
        exact Or.inr ⟨ticks, args, indices, rfl, run.2.symm⟩
    next => simp at run
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons tag =>
        simp only [toBlockSource] at run
        cases h : extractListSource n loc tag args with
        | none => simp [h] at run
        | some pair =>
          obtain ⟨bindings, kind⟩ := pair
          cases kind with
          | inl vs => simp [h] at run
          | inr child =>
            obtain ⟨_, left, inner, right, shape⟩ := extractList_wf_inr n loc tag args bindings child h
            simp [h] at run
            exact Or.inl ⟨tag, args, left, inner, right, rfl, run.2.symm.trans shape⟩
      | _ => simp [toBlockSource] at run
    | _ => simp [toBlockSource] at run
  | _ => simp [toBlockSource] at run

end Flapjack.Compiler.Backend.BviTmc
