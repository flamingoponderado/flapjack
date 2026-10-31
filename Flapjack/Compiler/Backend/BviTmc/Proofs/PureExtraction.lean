import Flapjack.Compiler.Backend.BviTmc.Proofs.PureEvaluation

/-! Correctness of TMC's pure-expression extraction. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BviSem BvlSem
namespace PureExtraction

private theorem extractOne_inl_shape (n loc tag : Nat) (e : Bvi.Exp)
    (bs : List Bvi.Exp) (vs : List Nat)
    (run : extractOneSource n loc tag e = some (bs, .inl vs)) :
    bs = [e] ∧ vs = [0] ∧ pureExp n e = true := by
  cases e with
  | call ticks dest args handler =>
    simp only [extractOneSource] at run
    cases h : callToBlockSource loc ticks dest args handler with
    | none => simp [h] at run
    | some pair => obtain ⟨bs', cb⟩ := pair; simp [h] at run
  | op op args =>
    cases op with
    | blockOp block =>
      cases block with
      | cons childTag =>
        simp only [extractOneSource] at run
        cases h : extractListSource n loc childTag args with
        | none => simp [h] at run
        | some result =>
          obtain ⟨bindings, kind⟩ := result
          cases kind with
          | inr cb => simp [h] at run
          | inl indices =>
            simp only [h] at run
            split at run <;> simp_all
      | _ => simp only [extractOneSource] at run; split at run <;> simp_all
    | _ => simp only [extractOneSource] at run; split at run <;> simp_all
  | _ => simp only [extractOneSource] at run; split at run <;> simp_all

theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- The singleton conjunct of the source extraction lemma. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inl_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb_aux_inl_single {C F : Type}
    (n loc tag : Nat) (e : Bvi.Exp) (bs : List Bvi.Exp) (vs : List Nat)
    (run : extractOneSource n loc tag e = some (bs, .inl vs)) :
    bs = [e] ∧ ∀ env, n ≤ env.length → ∃ values,
      ∀ state : BviState C F,
        evaluate [e] env state = (.val values, state) ∧
        evaluate (vs.map Bvi.Exp.var) values state = (.val values, state) := by
  obtain ⟨rfl, rfl, pure⟩ := extractOne_inl_shape n loc tag e bs vs run
  refine ⟨rfl, ?_⟩
  intro env bound
  obtain ⟨value, evaluates⟩ := PureEvaluation.evaluatePureExp (C := C) (F := F) e n pure env bound
  refine ⟨[value], ?_⟩
  intro state
  exact ⟨evaluates state, by simp [BviSem.evaluate]⟩

private theorem extractList_inl_shape (n loc tag : Nat) (args bs : List Bvi.Exp) (vs : List Nat)
    (run : extractListSource n loc tag args = some (bs, .inl vs)) :
    bs = args ∧ vs = List.range args.length ∧ pureExps n args = true := by
  cases args with
  | nil => simpa [extractListSource, pureExps] using run.symm
  | cons x xs =>
    cases xs with
    | nil =>
      have single := extractOne_inl_shape n loc tag x bs vs (by simpa [extractListSource] using run)
      simpa [pureExps] using single
    | cons y ys =>
      simp only [extractListSource] at run
      cases tail : extractListSource n loc tag (y :: ys) with
      | none => simp [tail] at run
      | some result =>
        obtain ⟨bindings, kind⟩ := result
        cases kind with
        | inr cb => cases shifted : shiftBlock 1 cb <;> simp [tail, shifted] at run
        | inl indices =>
          have tailShape := extractList_inl_shape n loc tag (y :: ys) bindings indices tail
          obtain ⟨rfl, rfl, tailPure⟩ := tailShape
          cases first : extractOneSource n loc tag x with
          | none => simp [tail, first] at run
          | some result =>
            obtain ⟨firstBindings, firstKind⟩ := result
            cases firstKind with
            | inr cb =>
              cases cb with
              | rCall ticks args => simp [tail, first] at run
              | callBlock t left child right =>
                cases left <;> cases right <;> simp [tail, first] at run
            | inl firstIndices =>
              obtain ⟨rfl, rfl, headPure⟩ := extractOne_inl_shape n loc tag x firstBindings firstIndices first
              simp only [tail, first] at run
              split at run
              next =>
                simp only [Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq] at run
                obtain ⟨rfl, rfl⟩ := run.symm
                refine ⟨rfl, ?_, by simp [pureExps, headPure, tailPure]⟩
                change 0 :: (List.range (y :: ys).length).map (· + 1) =
                  List.range ((y :: ys).length + 1)
                rw [List.range_succ_eq_map]
              next => simp at run
termination_by args.length
decreasing_by simp_wf; simp_all

/-- Pure extraction preserves the expressions and retrieves their evaluated values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_bvi_to_cb_aux_inl"
  (fmap_as_finite_support := [refs])]
theorem evaluate_bvi_to_cb_aux_inl {C F : Type}
    (n loc tag : Nat) (args bs : List Bvi.Exp) (vs : List Nat)
    (run : extractListSource n loc tag args = some (bs, .inl vs)) :
    bs = args ∧ ∀ env, n ≤ env.length → ∃ values,
      ∀ state : BviState C F,
        evaluate args env state = (.val values, state) ∧
        evaluate (vs.map Bvi.Exp.var) values state = (.val values, state) := by
  obtain ⟨rfl, rfl, pure⟩ := extractList_inl_shape n loc tag args bs vs run
  refine ⟨rfl, ?_⟩
  intro env bound
  obtain ⟨values, valuesRun⟩ := PureEvaluation.evaluate_pure_exps (C := C) (F := F) n bs pure env bound
  refine ⟨values, ?_⟩
  intro state
  have length := BviSem.evaluate_length bs env state state values (valuesRun state)
  exact ⟨valuesRun state, by simpa only [length] using BviTailrec.evaluate_var_range values state⟩

end PureExtraction
end Flapjack.Compiler.Backend.BviTmc
