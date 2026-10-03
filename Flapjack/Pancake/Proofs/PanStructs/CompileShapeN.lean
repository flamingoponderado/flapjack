import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Misc.ListEl
import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

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
      isWfShapeExactHOL ([] : StructContextExact) (compileShapeNHOL ctxt n sh) = true := by
  intro ctxt n sh
  induction n, sh using compileShapeNHOL.induct ctxt
    (motive2 := fun n shs => isWfShapesExactHOL ([] : StructContextExact) (compileShapesNHOL ctxt n shs) = true) with
  | case1 n => simp [compileShapeNHOL]
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
  | case5 n => simp [compileShapesNHOL]
  | case6 n sh shs ih1 ih2 => simp [compileShapesNHOL, ih1, ih2]

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
        exact List.drop_eq_getElem_cons hlt
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
      isWfShapeExactHOL ([] : StructContextExact) (compileShapeExact ctxt sh) = true := by
  intro ctxt sh
  have h := compileShapeNEq ctxt 0 sh
  rw [List.drop_zero] at h
  rw [← h]
  exact compileShapeNNoName ctxt 0 sh


/-- The struct-context lookup is the association-list lookup. Flapjack
infrastructure; no HOL original. -/
theorem structContextLookupHOL_eq_lookup (name : MlS) :
    ∀ ctx : StructContextExact, structContextLookupHOL name ctx = ctx.lookup name
  | [] => rfl
  | (candidate, info) :: rest => by
      by_cases h : name = candidate
      · subst h; simp
      · have hb : (name == candidate) = false := by simp [h]
        simp [h, hb, List.lookup_cons, structContextLookupHOL_eq_lookup name rest]

/-- With distinct keys, a member's key looks up its value. Flapjack
infrastructure; no HOL original. -/
theorem lookup_of_mem_nodup {β : Type} (k : MlS) (v : β) :
    ∀ l : List (MlS × β), (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, h => by simp at h
  | (k', v') :: rest, hnd, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with he | he
      · cases he; simp
      · have hk : k ≠ k' := by
          rintro rfl
          exact hnd.1 (List.mem_map.mpr ⟨(k, v), he, rfl⟩)
        have hb : (k == k') = false := by simp [hk]
        simp [List.lookup_cons, hb, lookup_of_mem_nodup k v rest hnd.2 he]

/-- Exact HOL `size_of_compile_shape_n` (`pan_structsProofScript.sml:480-510`,
local in HOL). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_compile_shape_n"]
theorem sizeOfCompileShapeN (ctxt : StructContextExact) :
    ∀ (sh_ctxt : List (MlS × List (MlS × ShapeHOL))) (n : Nat) (sh : ShapeHOL),
      sh_ctxt = ctxt.map (fun entry => (entry.1, entry.2.fields)) ∧
        isWfShapeExactHOL (ctxt.drop n) sh = true ∧
        Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact ctxt →
      sizeOfShapeWithContextHOL [] (compileShapeNHOL sh_ctxt n sh) =
        sizeOfShapeWithContextHOL ctxt sh := by
  rintro sh_ctxt n sh ⟨rfl, hwf, hok⟩
  have hafindi : ∀ (nm : MlS) (m : Nat),
      afindi nm ((ctxt.map (fun entry => (entry.1, entry.2.fields))).drop m) =
        afindi nm (ctxt.drop m) := by
    intro nm m
    rw [← List.map_drop, afindi_map_eq]
    intro x y _; rfl
  revert hwf
  induction n, sh using compileShapeNHOL.induct (ctxt.map (fun entry => (entry.1, entry.2.fields)))
    (motive2 := fun n shs => isWfShapesExactHOL (ctxt.drop n) shs = true →
      sizeOfShapesWithContextHOL [] (compileShapesNHOL
          (ctxt.map (fun entry => (entry.1, entry.2.fields))) n shs) =
        sizeOfShapesWithContextHOL ctxt shs) with
  | case1 n => intro _; simp [compileShapeNHOL, sizeOfShapeWithContextHOL]
  | case2 n shs ih =>
    intro hwf
    rw [compileShapeNHOL]
    simp only [sizeOfShapeWithContextHOL]
    exact ih (by simpa [isWfShapeExactHOL] using hwf)
  | case3 n nm h =>
    intro hwf
    exfalso
    simp only [isWfShapeExactHOL, structContextLookupHOL_eq_lookup, afindi_lookup] at hwf
    rw [hafindi] at h
    simp [h] at hwf
  | case4 n nm j h hlt ih =>
    intro _
    have hj : n + j < ctxt.length := by simpa using hlt
    have h' : afindi nm (ctxt.drop n) = some j := by rw [← hafindi]; exact h
    have hname : (ctxt[n + j]'hj).1 = nm := by
      have := afindi_el_fst nm (ctxt.drop n) j h'
      simp only [List.getElem?_drop] at this
      rw [List.getElem?_eq_getElem hj] at this
      simpa using this
    have hel : @holEl _ ⟨(ofString "", [])⟩ (n + j)
        (ctxt.map (fun entry => (entry.1, entry.2.fields))) =
        ((ctxt[n + j]'hj).1, (ctxt[n + j]'hj).2.fields) := by
      rw [@holEl_eq_getElem _ ⟨(ofString "", [])⟩ _ _ hlt]
      simp
    obtain ⟨hfields, hkeys, hshapes, hsizes⟩ := hok
    have hwfFields : isWfShapesExactHOL (ctxt.drop (n + j + 1))
        ((ctxt[n + j]'hj).2.fields.map Prod.snd) = true :=
      hshapes (n + j) _ _ (by rw [List.getElem?_eq_getElem hj])
    have hlookup : structContextLookupHOL nm ctxt = some (ctxt[n + j]'hj).2 := by
      rw [structContextLookupHOL_eq_lookup]
      apply lookup_of_mem_nodup nm _ ctxt hkeys
      rw [← hname]
      exact List.getElem_mem hj
    rw [compileShapeNHOL]
    split
    · rename_i h''; rw [h] at h''; cases h''
    · rename_i j' h''
      rw [h] at h''
      cases h''
      dsimp only
      rw [hel]
      simp only [sizeOfShapeWithContextHOL, hlookup]
      rw [hel] at ih
      rw [ih hwfFields]
      have := hsizes (ctxt[n + j]'hj) (List.getElem_mem hj)
      rw [this]
      rfl
  | case5 n => simp [compileShapesNHOL, sizeOfShapesWithContextHOL]
  | case6 n sh shs ih1 ih2 hwf =>
    simp only [isWfShapesExactHOL, Bool.and_eq_true] at hwf
    simp only [compileShapesNHOL, sizeOfShapesWithContextHOL, ih1 hwf.1, ih2 hwf.2]

/-- Exact HOL `size_of_compile_shape` (`pan_structsProofScript.sml:512-520`);
the free `ctxt` and `sh` are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_compile_shape"]
theorem sizeOfCompileShape (ctxt : StructContextExact) (sh : ShapeHOL) :
    isWfShapeExactHOL ctxt sh = true ∧
      Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact ctxt →
    sizeOfShapeWithContextHOL []
        (compileShapeExact (ctxt.map (fun entry => (entry.1, entry.2.fields))) sh) =
      sizeOfShapeWithContextHOL ctxt sh := by
  rintro ⟨hwf, hok⟩
  have h := compileShapeNEq (ctxt.map (fun entry => (entry.1, entry.2.fields))) 0 sh
  rw [List.drop_zero] at h
  rw [← h]
  exact sizeOfCompileShapeN ctxt _ 0 sh ⟨rfl, by simpa using hwf, hok⟩

namespace CompileShapeNSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end CompileShapeNSupport

/-- Exact HOL `size_of_shape_compile_pass_eq` (`pan_structsProofScript.sml:1604-1612`);
the free `s`, `shape` and `str_ctxt` are bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_shape_compile_pass_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem sizeOfShapeCompilePassEq {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (shape : ShapeHOL)
    (str_ctxt : List (MlS × List (MlS × ShapeHOL))) :
    Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact s.structs ∧
      isWfShapeExactHOL s.structs shape = true ∧
      str_ctxt = s.structs.map (fun entry => (entry.1, entry.2.fields)) →
    sizeOfShapeHOL (compileShapeExact str_ctxt shape) =
      sizeOfShapeWithContextHOL s.structs shape := by
  rintro ⟨hok, hwf, rfl⟩
  rw [← sizeOfShapeWithContextHOL_eq _ [] (compileShapeNoName _ shape)]
  exact sizeOfCompileShape s.structs shape ⟨hwf, hok⟩

end Flapjack.Pancake.PanStructs.CompileShapeExact
