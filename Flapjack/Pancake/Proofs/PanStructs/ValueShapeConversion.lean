import Flapjack.Pancake.Proofs.PanStructs.MemLoadConversion
namespace Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack list projection plumbing, no independent HOL original. -/
theorem fields_values_valid {width : Nat} [NeZero width] (context : StructContextExact)
    (fields : List (MlS × ValueHOL width)) :
    valuesFldsOkHOLExact context (fields.map Prod.snd) = fieldsFldsOkHOLExact context fields := by
  induction fields with
  | nil => simp [valuesFldsOkHOLExact, fieldsFldsOkHOLExact]
  | cons entry rest ih =>
    rcases entry with ⟨name, value⟩
    simp only [List.map_cons, valuesFldsOkHOLExact, fieldsFldsOkHOLExact, ih]

@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "shape_of_convert_v_ind"
  (words_as_type_indexed_bitvec)]
theorem shapeOfConvertVInd {width : Nat} [NeZero width] (context : StructContextExact) :
    ∀ (sctxt : List (MlS × List (MlS × ShapeHOL))) (n : Nat) (shape : ShapeHOL)
      (value : ValueHOL width),
    structInfosOkHOLExact context ∧
    isWfShapeExactHOL (context.drop n) shape = true ∧
    valueFldsOkHOLExact context value = true ∧
    sctxt = context.map (fun entry => (entry.1, entry.2.fields)) ∧
    shapeOfHOLExact value = shape →
    compileShapeNHOL sctxt n shape = shapeOfHOLExact (convertV value) := by
  intro sctxt n shape value ⟨hok, hwf, hv, hctx, hshape⟩
  subst sctxt
  obtain ⟨_, hkeys, hshapes, _⟩ := hok
  have hafindi : ∀ name m,
      afindi name ((context.map (fun entry => (entry.1, entry.2.fields))).drop m) =
        afindi name (context.drop m) := by
    intro name m
    rw [← List.map_drop, afindi_map_eq]
    intro _ _ _
    rfl
  revert value hwf hv hshape
  induction n, shape using compileShapeNHOL.induct
      (context.map (fun entry => (entry.1, entry.2.fields)))
    (motive2 := fun n shapes => ∀ values : List (ValueHOL width),
      isWfShapesExactHOL (context.drop n) shapes = true →
      valuesFldsOkHOLExact context values = true →
      values.map shapeOfHOLExact = shapes →
      compileShapesNHOL (context.map (fun entry => (entry.1, entry.2.fields))) n shapes =
        values.map (fun value => shapeOfHOLExact (convertV value))) with
  | case1 n =>
    intro value _ _ hs
    cases value <;> simp [shapeOfHOLExact] at hs
    simp [compileShapeNHOL, convertV, shapeOfHOLExact]
  | case2 n shapes ih =>
    intro value hwf hv hs
    cases value with
    | val word => simp [shapeOfHOLExact] at hs
    | nStruct name fields => simp [shapeOfHOLExact] at hs
    | rStruct values =>
      simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hs
      have hc := ih values (by simpa [isWfShapeExactHOL] using hwf)
        (by simpa [valueFldsOkHOLExact] using hv) hs
      simpa [compileShapeNHOL, convertV, shapeOfHOLExact, List.map_map, Function.comp_def] using congrArg ShapeHOL.comb hc
  | case3 n name hmissing =>
    intro value hwf _ _
    simp only [isWfShapeExactHOL, structContextLookupHOL_eq_lookup, afindi_lookup] at hwf
    rw [hafindi] at hmissing
    simp [hmissing] at hwf
  | case4 n name j hfound hbound ih =>
    intro value _ hv hs
    have hj : n + j < context.length := by simpa using hbound
    have hfound' : afindi name (context.drop n) = some j := by rw [← hafindi]; exact hfound
    have hname : (context[n + j]'hj).1 = name := by
      have he := afindi_el_fst name (context.drop n) j hfound'
      simp only [List.getElem?_drop] at he
      rw [List.getElem?_eq_getElem hj] at he
      simpa using he
    have hlookup : structContextLookupHOL name context = some (context[n + j]'hj).2 := by
      rw [structContextLookupHOL_eq_lookup]
      apply lookup_of_mem_nodup name _ context hkeys
      rw [← hname]
      exact List.getElem_mem hj
    have hel : @holEl _ ⟨(Flapjack.Basis.Pure.MlString.ofString "", [])⟩ (n + j)
        (context.map (fun entry => (entry.1, entry.2.fields))) =
        ((context[n + j]'hj).1, (context[n + j]'hj).2.fields) := by
      rw [@holEl_eq_getElem _ ⟨(Flapjack.Basis.Pure.MlString.ofString "", [])⟩ _ _ hbound]
      simp
    rw [hel] at ih
    cases value with
    | val word => simp [shapeOfHOLExact] at hs
    | rStruct values => simp [shapeOfHOLExact] at hs
    | nStruct nm fields =>
      simp only [shapeOfHOLExact, ShapeHOL.named.injEq] at hs
      subst nm
      simp only [valueFldsOkHOLExact, hlookup, Bool.and_eq_true] at hv
      have hfieldshapes := (shapeEqListHOL_eq_true _ _).mp hv.2.2
      have hvalues : valuesFldsOkHOLExact context (fields.map Prod.snd) = true := by
        rw [fields_values_valid]
        exact hv.1
      have hfieldwf := hshapes (n + j) _ _ (by rw [List.getElem?_eq_getElem hj])
      have hc := ih (fields.map Prod.snd) hfieldwf hvalues
        (by simpa [List.map_map, Function.comp_def] using hfieldshapes)
      rw [compileShapeNHOL]
      split
      · rename_i hbad
        rw [hfound] at hbad
        cases hbad
      · rename_i j' he
        rw [hfound] at he
        cases he
        dsimp only
        rw [hel]
        simpa [convertV, shapeOfHOLExact, List.map_map, Function.comp_def] using congrArg ShapeHOL.comb hc
  | case5 n values _ _ hs =>
    have hempty : values = [] := List.map_eq_nil_iff.mp hs
    subst values
    simp [compileShapesNHOL]
  | case6 n sh rest ihhead ihtail values hwf hv hs =>
    cases values with
    | nil => simp at hs
    | cons value values =>
      simp only [List.map_cons, List.cons.injEq] at hs
      simp only [isWfShapesExactHOL, Bool.and_eq_true] at hwf
      simp only [valuesFldsOkHOLExact, Bool.and_eq_true] at hv
      rw [compileShapesNHOL, ihhead value hwf.1 hv.1 hs.1,
        ihtail values hwf.2 hv.2 hs.2]
      rfl
/-- Whole original shape conversion theorem. The unused n has the independent
polymorphic HOL type confirmed by the original kernel, rather than Nat. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "shape_of_convert_v"
  (words_as_type_indexed_bitvec)]
theorem shapeOfConvertV {width : Nat} [NeZero width] {β : Type}
    (context : StructContextExact) (value : ValueHOL width)
    (sctxt : List (MlS × List (MlS × ShapeHOL))) (_n : β)
    (h : valueFldsOkHOLExact context value = true ∧
      sctxt = context.map (fun entry => (entry.1, entry.2.fields)) ∧
      isWfShapeValueHOLExact context value = true ∧
      structInfosOkHOLExact context) :
    compileShapeExact sctxt (shapeOfHOLExact value) = shapeOfHOLExact (convertV value) := by
  have hc := shapeOfConvertVInd context sctxt 0 (shapeOfHOLExact value) value
    ⟨h.2.2.2, by simpa using isWfShapeValueHOLExact_shapeOfHOLExact context value h.2.2.1,
      h.1, h.2.1, rfl⟩
  rw [compileShapeNEq, List.drop_zero] at hc
  exact hc

/-- Original local reversed theorem after HOL's exact std_ss simplification:
unused n and the context-map equality binder are eliminated in the source. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "shape_of_convert_v_rev"
  (words_as_type_indexed_bitvec)]
theorem shapeOfConvertVRev {width : Nat} [NeZero width]
    (context : StructContextExact) (value : ValueHOL width)
    (h : valueFldsOkHOLExact context value = true ∧
      isWfShapeValueHOLExact context value = true ∧ structInfosOkHOLExact context) :
    shapeOfHOLExact (convertV value) =
      compileShapeExact (context.map (fun entry => (entry.1, entry.2.fields)))
        (shapeOfHOLExact value) :=
  (shapeOfConvertV context value _ () ⟨h.1, rfl, h.2.1, h.2.2⟩).symm

end Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
