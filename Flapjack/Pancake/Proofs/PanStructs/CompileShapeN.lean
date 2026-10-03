import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Misc.ListEl

/-! The proof-side `compile_shape_n` of pan_structsProofScript.sml:317-334 and
its name-freedom lemmas `compile_shape_n_no_name` and `compile_shape_no_name`
(1584-1602). -/

namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

mutual
  /-- Exact HOL `compile_shape_n_def` (`pan_structsProofScript.sml:317-334`).
  The `Comb` clause's `MAP` is the list helper `compileShapesNHOL`, as for the
  reviewed `compileShapeExact`; `EL` is the reviewed `holEl`, and the field-name
  type stays the HOL type parameter. The recursion follows HOL's termination
  measure (remaining context length, then shape size). -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_def"]
  noncomputable def compileShapeNHOL {α : Type} (sctxt : List (MlS × List (α × ShapeHOL)))
      (n : Nat) : ShapeHOL → ShapeHOL
    | .one => .one
    | .comb shs => .comb (compileShapesNHOL sctxt n shs)
    | .named nm =>
        match h : afindi nm (sctxt.drop n) with
        | none => .one
        | some j =>
            have : n + j < sctxt.length := by
              have := afindi_less_length nm _ j h
              simp only [List.length_drop] at this
              omega
            .comb (compileShapesNHOL sctxt (n + j + 1)
              ((@holEl _ ⟨(ofString "", [])⟩ (n + j) sctxt).2.map Prod.snd))
  termination_by shape => (sctxt.length - n, sizeOf shape)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; omega)

  /-- `MAP (compile_shape_n sctxt n)` over a shape list. -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_def"]
  noncomputable def compileShapesNHOL {α : Type} (sctxt : List (MlS × List (α × ShapeHOL)))
      (n : Nat) : List ShapeHOL → List ShapeHOL
    | [] => []
    | sh :: shs => compileShapeNHOL sctxt n sh :: compileShapesNHOL sctxt n shs
  termination_by shapes => (sctxt.length - n, sizeOf shapes)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (apply Prod.Lex.right; omega)
end

/-- Exact HOL `compile_shape_n_no_name` (`pan_structsProofScript.sml:1584-1596`):
`is_wf_shape_nil` is `is_wf_shape` in the empty struct context. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_no_name"]
theorem compileShapeNNoName {α : Type} :
    ∀ (ctxt : List (MlS × List (α × ShapeHOL))) (n : Nat) (sh : ShapeHOL),
      isWfShapeExactHOL [] (compileShapeNHOL ctxt n sh) = true := by
  intro ctxt n sh
  induction n, sh using compileShapeNHOL.induct ctxt
    (motive2 := fun n shs => isWfShapesExactHOL [] (compileShapesNHOL ctxt n shs) = true) with
  | case1 n => simp [compileShapeNHOL, isWfShapeExactHOL]
  | case2 n shs ih => rw [compileShapeNHOL]; simpa [isWfShapeExactHOL] using ih
  | case3 n nm h =>
    rw [compileShapeNHOL]
    split
    · simp [isWfShapeExactHOL]
    · rename_i j h'; rw [h] at h'; cases h'
  | case4 n nm j h hlt ih =>
    rw [compileShapeNHOL]
    split
    · rename_i h'; rw [h] at h'; cases h'
    · rename_i j' h'
      rw [h] at h'
      cases h'
      simpa [isWfShapeExactHOL] using ih
  | case5 n => simp [compileShapesNHOL, isWfShapesExactHOL]
  | case6 n sh shs ih1 ih2 => simp [compileShapesNHOL, isWfShapesExactHOL, ih1, ih2]

/-- Exact HOL `compile_shape_n_eq` (`pan_structsProofScript.sml:369-383`):
`compile_shape_n` at offset `n` is `compile_shape` on the context suffix. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_eq"]
theorem compileShapeNEq {α : Type} :
    ∀ (sctxt : List (MlS × List (α × ShapeHOL))) (n : Nat) (sh : ShapeHOL),
      compileShapeNHOL sctxt n sh = compileShapeExact (sctxt.drop n) sh := by
  intro sctxt n sh
  induction n, sh using compileShapeNHOL.induct sctxt
    (motive2 := fun n shs => compileShapesNHOL sctxt n shs = compileShapesExact (sctxt.drop n) shs) with
  | case1 n => simp [compileShapeNHOL, compileShapeExact]
  | case2 n shs ih => rw [compileShapeNHOL, compileShapeExact, ih]
  | case3 n nm h =>
    rw [compileShapeNHOL]
    split
    · rw [compileShapeExact]
      have hf : (fun entry : MlS × List (α × ShapeHOL) => ! decide (entry.1 = nm)) =
          (fun entry => decide (nm ≠ entry.1)) := by
        funext e
        by_cases he : e.1 = nm
        · simp [he]
        · have hne : nm ≠ e.1 := fun h => he h.symm
          simp [he, hne]
      have hd : (sctxt.drop n).dropWhile (fun entry => ! decide (entry.1 = nm)) = [] := by
        rw [hf, afindi_dropWhile, h]
      split
      · rename_i hdrop; rw [hd] at hdrop; cases hdrop
      · rfl
    · rename_i j h'; rw [h] at h'; cases h'
  | case4 n nm j h hlt ih =>
    rw [compileShapeNHOL]
    split
    · rename_i h'; rw [h] at h'; cases h'
    · rename_i j' h'
      rw [h] at h'
      cases h'
      rw [compileShapeExact]
      have hf : (fun entry : MlS × List (α × ShapeHOL) => ! decide (entry.1 = nm)) =
          (fun entry => decide (nm ≠ entry.1)) := by
        funext e
        by_cases he : e.1 = nm
        · simp [he]
        · have hne : nm ≠ e.1 := fun h => he h.symm
          simp [he, hne]
      have hd : (sctxt.drop n).dropWhile (fun entry => ! decide (entry.1 = nm)) =
          @holEl _ ⟨(ofString "", [])⟩ (n + j) sctxt :: sctxt.drop (n + j + 1) := by
        rw [hf, afindi_dropWhile, h]
        dsimp only
        rw [List.drop_drop, @holEl_eq_getElem _ ⟨(ofString "", [])⟩ _ _ hlt]
        simpa [Nat.add_comm] using List.drop_eq_getElem_cons hlt
      split
      · rename_i fields suffix hdrop
        rw [hd] at hdrop
        injection hdrop with hhead hsuffix
        subst hsuffix
        rw [ih]
        dsimp only
        rw [hhead]
      · rename_i hdrop; rw [hd] at hdrop; cases hdrop
  | case5 n => simp [compileShapesNHOL, compileShapesExact]
  | case6 n sh shs ih1 ih2 => rw [compileShapesNHOL, compileShapesExact, ih1, ih2]

/-- Exact HOL `compile_shape_no_name` (`pan_structsProofScript.sml:1598-1602`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_no_name"]
theorem compileShapeNoName {α : Type} :
    ∀ (ctxt : List (MlS × List (α × ShapeHOL))) (sh : ShapeHOL),
      isWfShapeExactHOL [] (compileShapeExact ctxt sh) = true := by
  intro ctxt sh
  have h := compileShapeNEq ctxt 0 sh
  rw [List.drop_zero] at h
  rw [← h]
  exact compileShapeNNoName ctxt 0 sh

end Flapjack.Pancake.PanStructs.CompileShapeExact
