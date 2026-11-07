import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractCorrespondence
import Flapjack.Compiler.Backend.BackendCommon.SmallInt

/-! Well-formedness of TMC constructor call skeletons. -/
namespace Flapjack.Compiler.Backend.BviTmc

/-- Every index in a list remains in range after adding one binder. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_shift_sing"]
theorem wfVars_shift_sing (n : Nat) (vs : List Nat) (wf : wfVars n vs) :
    wfVars (n + 1) (shiftVars 1 vs) := by
  simpa [Nat.add_comm] using wfVars_shift n 1 vs wf

/-- A bounded index can be prepended to a well-formed list. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_cons"]
theorem wfVars_cons (n v : Nat) (vs : List Nat) (bound : v < n) (wf : wfVars n vs) :
    wfVars n (v :: vs) := by
  intro index member
  rcases List.mem_cons.mp member with rfl | member
  · exact bound
  · exact wf index member

/-- Consecutive binders are within the environment they occupy. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_vars_bind"]
theorem wfVars_bind {α : Type} (bs : List α) (vs : List Nat) (n n' : Nat)
    (binding : bind n bs = (vs, n')) : wfVars (n + bs.length) vs := by
  induction bs generalizing n vs n' with
  | nil =>
    simp [bind] at binding
    obtain ⟨rfl, rfl⟩ := binding
    exact wfVars_empty _
  | cons x xs ih =>
    cases h : bind (n + 1) xs with
    | mk indices last =>
      simp only [bind, h, Prod.mk.injEq] at binding
      obtain ⟨rfl, rfl⟩ := binding.symm
      apply wfVars_cons
      · simp
      · have rest := ih indices (n + 1) last h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

/-- A call skeleton uses bounded variables and small constructor arities. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_cb_def"]
def wfBlock (n : Nat) : CallBlock → Prop
  | .rCall _ args => wfVars n args
  | .callBlock _ left child right =>
      wfVars n left ∧ wfBlock n child ∧ wfVars n right ∧
        BackendCommon.smallEnoughInt (Int.ofNat right.length)

/-- Increasing the available environment preserves skeleton well-formedness. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_cb_expand"]
theorem wfBlock_expand (n1 n2 : Nat) (cb : CallBlock) (wf : wfBlock n1 cb)
    (bound : n1 ≤ n2) : wfBlock n2 cb := by
  induction cb with
  | rCall ticks args => exact wfVars_expand n1 n2 args wf bound
  | callBlock tag left child right ih =>
    exact ⟨wfVars_expand n1 n2 left wf.1 bound, ih wf.2.1,
      wfVars_expand n1 n2 right wf.2.2.1 bound, wf.2.2.2⟩

/-- Shifting a skeleton by one accommodates one new environment binder. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "wf_cb_shift_sing"]
theorem wfBlock_shift_sing (n : Nat) (cb : CallBlock) (wf : wfBlock n cb) :
    wfBlock (n + 1) (shiftBlock 1 cb) := by
  induction cb with
  | rCall ticks args => exact wfVars_shift_sing n args wf
  | callBlock tag left child right ih =>
    exact ⟨wfVars_shift_sing n left wf.1, ih wf.2.1,
      wfVars_shift_sing n right wf.2.2.1, by simpa [shiftVars] using wf.2.2.2⟩

/-- Extracting a recursive call from one argument creates an empty outer frame. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_sing"]
theorem extractList_single_shape (n loc tag : Nat) (arg : Bvi.Exp) (bs : List Bvi.Exp)
    (cb : CallBlock) (run : extractListSource n loc tag [arg] = some (bs, .inr cb)) :
    ∃ child, cb = .callBlock tag [] child [] := by
  simp only [extractListSource] at run
  cases arg with
  | call ticks dest args handler =>
    simp only [extractOneSource] at run
    cases h : callToBlockSource loc ticks dest args handler with
    | none => simp [h] at run
    | some pair =>
      obtain ⟨bindings, child⟩ := pair
      simp [h] at run
      exact ⟨child, run.2.symm⟩
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
          | inr child => simp [h] at run; exact ⟨child, run.2.symm⟩
          | inl vs => simp only [h] at run; split at run <;> simp_all
      | _ => simp only [extractOneSource] at run; split at run <;> simp_all
    | _ => simp only [extractOneSource] at run; split at run <;> simp_all
  | _ => simp only [extractOneSource] at run; split at run <;> simp_all

end Flapjack.Compiler.Backend.BviTmc
