module

public import Flapjack.Pancake.Semantics.PanProps
public import Flapjack.Pancake.Semantics.PanSem.DecCallExact
public import Flapjack.Pancake.Semantics.PanProps.WithShape
public import Flapjack.Pancake.Semantics.PanCommonProps.FiniteMapExact

@[expose] public section

/-!
# `list_rel_length_shape_of_flatten` over the exact value carrier

Exact ports of HOL `panProps$list_rel_length_shape_of_flatten_better[local]` and
`list_rel_length_shape_of_flatten` (`cakeml/pancake/semantics/panPropsScript.sml:244-262`),
and of `list_rel_flatten_with_shape_length` / `list_rel_flatten_with_shape_flookup`
(lines 549-613), which combine the `with_shape` lemmas of `PanProps/WithShape.lean`
with `update_eq_zip_flookup` (`PanCommonProps/FiniteMapExact.lean`).
HOL `LIST_REL` is the exact `ListRel`, `EVERY is_wf_shape_v_nil` is membership
over `isWfShapeValueHOLExact []`, and `size_of_shape`/`shape_of`/`flatten` are
the `sizeOfShapeHOL`/`shapeOfHOLExact`/`flattenHOL` functions over `ValueHOL`.
HOL's `'a word` is the positive-width word carrier of `ValueHOL width`
(`words_as_type_indexed_bitvec`).
-/

namespace Flapjack

instance valueHOLNonempty {width : Nat} [NeZero width] : Nonempty (ValueHOL width) :=
  ⟨.val (.word 0)⟩

open Flapjack.Pancake.PanLang (MlS ShapeHOL sizeOfShapeHOL sizeOfShapesHOL
  sizeOfShapesHOL_cons withShapeHOL StructContextExact isWfShapeExactHOL)

/-- Exact port of HOL `list_rel_length_shape_of_flatten_better[local]`
    (`panPropsScript.sml:244-253`): `LIST_REL (λvsh arg. vsh = shape_of arg)
    vshs args /\ EVERY is_wf_shape_v_nil args ==>
    size_of_shape (Comb vshs) = LENGTH (FLAT (MAP flatten args))`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "list_rel_length_shape_of_flatten_better"
  (words_as_type_indexed_bitvec)]
theorem listRelLengthShapeOfFlattenBetterHOL {width : Nat} [NeZero width] :
    ∀ (vshs : List ShapeHOL) (args : List (ValueHOL width)),
      ListRel (fun vsh arg => vsh = shapeOfHOLExact arg) vshs args ∧
        (∀ arg, arg ∈ args → isWfShapeValueHOLExact [] arg = true) →
      sizeOfShapeHOL (.comb vshs) = (args.map flattenHOL).flatten.length := by
  intro vshs args ⟨hrel, hwf⟩
  induction hrel with
  | nil => simp [sizeOfShapeHOL, sizeOfShapesHOL]
  | @cons vsh arg vshs args hhead _ ih =>
      have hshape : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact arg) = true := by
        rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl arg]
        exact hwf arg (by simp)
      have hlen := flattenHOL_length_eq_sizeOfShapeHOL arg hshape
      have htail := ih (fun other hmem => hwf other (by simp [hmem]))
      simp only [sizeOfShapeHOL, sizeOfShapesHOL] at htail ⊢
      simp [List.flatten_cons, List.length_append, hhead, hlen, htail]

/-- Exact port of HOL `list_rel_length_shape_of_flatten`
    (`panPropsScript.sml:256-262`): `LIST_REL (λvsh arg. SND vsh = shape_of arg)
    vshs args /\ EVERY is_wf_shape_v_nil args ==>
    size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "list_rel_length_shape_of_flatten"
  (words_as_type_indexed_bitvec)]
theorem listRelLengthShapeOfFlattenHOL {width : Nat} [NeZero width] {β : Type} :
    ∀ (vshs : List (β × ShapeHOL)) (args : List (ValueHOL width)),
      ListRel (fun vsh arg => vsh.2 = shapeOfHOLExact arg) vshs args ∧
        (∀ arg, arg ∈ args → isWfShapeValueHOLExact [] arg = true) →
      sizeOfShapeHOL (.comb (vshs.map Prod.snd)) =
        (args.map flattenHOL).flatten.length := by
  intro vshs args ⟨hrel, hwf⟩
  apply listRelLengthShapeOfFlattenBetterHOL
  refine ⟨?_, hwf⟩
  clear hwf
  induction hrel with
  | nil => exact .nil
  | cons hhead _ ih => exact .cons hhead ih

/-! ## `list_rel_flatten_with_shape_length` / `_flookup`

The two HOL theorems at `panPropsScript.sml:549` and `:585` read the `n`-th group
of `with_shape sh ns` through `el_el_with_shape` and look up its `n'`-th element
in `FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))` through `update_eq_zip_flookup`.
Their exact Lean twins use the tagged `withShapeHOL`, `elElWithShapeHOL` and
`updateEqZipFlookupExactHOL`, the canonical `HolFiniteMapExact.empty` carrier
for HOL `FEMPTY`, and `flattenHOL`/`shapeOfHOLExact`/`isWfShapeValueHOLExact`
for the `ValueHOL width` arguments.  HOL's `LIST_REL (λsh arg. sh = shape_of
arg) sh args` is the exact `ListRel` relation, and `EVERY is_wf_shape_v_nil
args` is membership over `isWfShapeValueHOLExact []`.  The helpers below are
untagged infrastructure: Lean's `getElem` needs the bounds that HOL's total
`EL` supplies, and the shape well-formedness that HOL discharges inside
`el_el_with_shape`'s proof is derived here from the `LIST_REL` hypothesis.
-/

/-- The exact `LIST_REL` hypothesis exposes the pointwise shape equality at a
    common index. -/
theorem listRelGetElem {width : Nat} [NeZero width]
    {shapes : List ShapeHOL} {args : List (ValueHOL width)}
    (h : ListRel (fun shape arg => shape = shapeOfHOLExact arg) shapes args)
    {i : Nat} (hi : i < shapes.length) (hj : i < args.length) :
    shapes[i]'hi = shapeOfHOLExact (args[i]'hj) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hhead _ ih =>
      cases i with
      | zero => simpa using hhead
      | succ k =>
          simp only [List.length_cons] at hi hj
          simpa only [List.getElem_cons_succ] using ih (by omega) (by omega)

/-- The `LIST_REL` hypothesis in `getElem?` form (the form the flat-length helper
    consumes). -/
theorem listRelGetElem? {width : Nat} [NeZero width]
    {shapes : List ShapeHOL} {args : List (ValueHOL width)}
    (h : ListRel (fun shape arg => shape = shapeOfHOLExact arg) shapes args) :
    ∀ i, i < shapes.length → shapes[i]? = (args[i]?).map shapeOfHOLExact := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hhead _ ih =>
      intro i hi
      cases i with
      | zero => simp [hhead]
      | succ k =>
          simp only [List.length_cons] at hi
          simpa [List.getElem?_cons_succ] using ih k (by omega)

/-- Flat shape size of an entrywise shape-related pair of lists, in the
    `getElem?` form.  Untagged support for the `_flookup` twin. -/
theorem sizeOfShapeHOLCombEqFlattenHOLLengthOfGetElem {width : Nat} [NeZero width]
    (vshs : List ShapeHOL) (args : List (ValueHOL width))
    (hlen : vshs.length = args.length)
    (hrel : ∀ i, i < args.length → vshs[i]? = (args[i]?).map shapeOfHOLExact)
    (hwf : ∀ arg, arg ∈ args → isWfShapeValueHOLExact [] arg = true) :
    sizeOfShapeHOL (.comb vshs) = (args.map flattenHOL).flatten.length := by
  induction args generalizing vshs with
  | nil =>
      cases vshs with
      | nil => simp [sizeOfShapeHOL, sizeOfShapesHOL]
      | cons shape shapes => simp at hlen
  | cons arg args ih =>
      cases vshs with
      | nil => simp at hlen
      | cons vsh vshs =>
          have hhead : vsh = shapeOfHOLExact arg := by
            have h0 := hrel 0 (by simp)
            simp only [List.getElem?_cons_zero, Option.map_some] at h0
            exact Option.some.inj h0
          have hlenTail : vshs.length = args.length := by simpa using hlen
          have hrelTail : ∀ i, i < args.length →
              vshs[i]? = (args[i]?).map shapeOfHOLExact := by
            intro i hi
            have h := hrel (i + 1) (by simp [hi])
            simpa [List.getElem?_cons_succ] using h
          have hwfTail : ∀ other, other ∈ args →
              isWfShapeValueHOLExact [] other = true :=
            fun other hmem => hwf other (by simp [hmem])
          have hshapeWf : Flapjack.Pancake.PanLang.isWfShapeExactHOL
              ([] : Flapjack.Pancake.PanLang.StructContextExact)
              (shapeOfHOLExact arg) = true := by
            rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl arg]
            exact hwf arg (by simp)
          have hlenHead := flattenHOL_length_eq_sizeOfShapeHOL arg hshapeWf
          simp only [List.map_cons, List.flatten_cons, List.length_append]
          rw [sizeOfShapeHOL_comb_cons, hhead, hlenHead,
            ih vshs hlenTail hrelTail hwfTail]

/-- Exact port of HOL `panProps$list_rel_flatten_with_shape_length`
    (`panPropsScript.sml:549-567`): the `n`-th group of `with_shape sh ns` has
    the same length as `flatten v`, where `v` is the `n`-th argument. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "list_rel_flatten_with_shape_length"
  (words_as_type_indexed_bitvec)]
theorem listRelFlattenWithShapeLengthHOL {α : Type} {width : Nat} [NeZero width]
    (shapes : List ShapeHOL) (names : List α) (args : List (ValueHOL width))
    (value : ValueHOL width) (n : Nat)
    (h : names.length = (args.map flattenHOL).flatten.length ∧
      sizeOfShapeHOL (.comb shapes) = (args.map flattenHOL).flatten.length ∧
      elHOL args n = value ∧ n < args.length ∧ args.length = shapes.length ∧
      ListRel (fun shape arg => shape = shapeOfHOLExact arg) shapes args ∧
      (∀ arg, arg ∈ args → isWfShapeValueHOLExact [] arg = true)) :
    ((withShapeHOL shapes names)[n]'(by
        obtain ⟨-, -, -, hn, hlen, -, -⟩ := h
        rw [withShapeHOLLength]
        omega)).length =
      (flattenHOL value).length := by
  obtain ⟨hnames, hsize, hget, hn, hlen, hrel, hwf⟩ := h
  rw [elHOL_eq_getElem args n hn] at hget
  have hvalues : names.length = sizeOfShapeHOL (.comb shapes) := hnames.trans hsize.symm
  have hnshapes : n < shapes.length := by omega
  have hshape : shapes[n]'hnshapes = shapeOfHOLExact value := by
    have h := listRelGetElem hrel hnshapes hn
    rw [hget] at h
    exact h
  have hwfval : isWfShapeValueHOLExact [] value = true :=
    hwf value (by rw [← hget]; exact List.getElem_mem hn)
  have hshapeWf : Flapjack.Pancake.PanLang.isWfShapeExactHOL
      ([] : Flapjack.Pancake.PanLang.StructContextExact)
      (shapeOfHOLExact value) = true := by
    rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl value]
    exact hwfval
  have hflat := flattenHOL_length_eq_sizeOfShapeHOL value hshapeWf
  rw [withShapeHOLGetElemLength shapes names n hvalues hnshapes, hshape]
  exact hflat.symm

/-- Exact port of HOL `panProps$list_rel_flatten_with_shape_flookup`
    (`panPropsScript.sml:585-613`): the flat list of the arguments, zipped with
    the names, looks up the `n'`-th element of the `n`-th group as the
    corresponding element of `flatten v`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "list_rel_flatten_with_shape_flookup"
  (words_as_type_indexed_bitvec)]
theorem listRelFlattenWithShapeFlookupHOL {α : Type} [DecidableEq α]
    {width : Nat} [NeZero width]
    (shapes : List ShapeHOL) (names : List α) (args : List (ValueHOL width))
    (value : ValueHOL width) (n n' : Nat)
    (h : names.Nodup ∧ names.length = (args.map flattenHOL).flatten.length ∧
      sizeOfShapeHOL (.comb shapes) = (args.map flattenHOL).flatten.length ∧
      elHOL args n = value ∧ n < args.length ∧ args.length = shapes.length ∧
      ListRel (fun shape arg => shape = shapeOfHOLExact arg) shapes args ∧
      (∀ arg, arg ∈ args → isWfShapeValueHOLExact [] arg = true) ∧
      (elHOL (withShapeHOL shapes names) n).length = (flattenHOL value).length ∧
      n' < (elHOL (withShapeHOL shapes names) n).length) :
    (HolFiniteMapExact.empty.updateListEq
        (names.zip (args.map flattenHOL).flatten)).lookup
      (((withShapeHOL shapes names)[n]'(by
          obtain ⟨-, -, -, -, hn, hlen, -, -⟩ := h
          rw [withShapeHOLLength]
          omega))[n']'(by
          obtain ⟨-, hnames, hsize, -, hn, hlen, -, -, hgroup, hn'⟩ := h
          have hvalues : names.length = sizeOfShapeHOL (.comb shapes) :=
            hnames.trans hsize.symm
          have hnshapes : n < shapes.length := by omega
          rw [withShapeHOLGetElemLength shapes names n hvalues hnshapes]
          rw [elHOL_eq_getElem (withShapeHOL shapes names) n (by
            rw [withShapeHOLLength]
            omega)] at hn'
          rw [withShapeHOLGetElemLength shapes names n hvalues hnshapes] at hn'
          exact hn')) =
      some ((flattenHOL value)[n']'(by
          obtain ⟨-, -, -, -, -, -, -, -, hgroup, hn'⟩ := h
          rw [← hgroup]
          exact hn')) := by
  obtain ⟨hdistinct, hnames, hsize, hget, hn, hlen, hrel, hwf, hgroup, hn'⟩ := h
  rw [elHOL_eq_getElem args n hn] at hget
  have hvalues : names.length = sizeOfShapeHOL (.comb shapes) := hnames.trans hsize.symm
  have hnshapes : n < shapes.length := by omega
  have hnBound : n < (withShapeHOL shapes names).length := by
    rw [withShapeHOLLength]
    omega
  rw [elHOL_eq_getElem (withShapeHOL shapes names) n hnBound] at hgroup hn'
  have hgroupSize : sizeOfShapeHOL (shapes[n]'hnshapes) = (flattenHOL value).length :=
    (withShapeHOLGetElemLength shapes names n hvalues hnshapes).symm.trans hgroup
  have hn'val : n' < (flattenHOL value).length := by rw [← hgroup]; exact hn'
  have hrelTake : ∀ i, i < (args.take n).length →
      (shapes.take n)[i]? = ((args.take n)[i]?).map shapeOfHOLExact := by
    intro i hi
    have hin : i < n := Nat.lt_of_lt_of_le hi (List.length_take_le n args)
    have hish : i < shapes.length := by omega
    have hians : i < args.length := by omega
    rw [List.getElem?_take, if_pos hin, List.getElem?_take, if_pos hin,
      List.getElem?_eq_some_iff.mpr ⟨hish, rfl⟩,
      List.getElem?_eq_some_iff.mpr ⟨hians, rfl⟩]
    simp only [Option.map_some]
    rw [listRelGetElem hrel hish hians]
  have hident : sizeOfShapeHOL (.comb (shapes.take n)) =
      ((args.take n).map flattenHOL).flatten.length := by
    apply sizeOfShapeHOLCombEqFlattenHOLLengthOfGetElem (shapes.take n) (args.take n)
    · rw [List.length_take, List.length_take, hlen]
    · exact hrelTake
    · intro arg hmem
      exact hwf arg (List.mem_of_mem_take hmem)
  have hboundSize : sizeOfShapeHOL (.comb (shapes.take n)) + n' <
      sizeOfShapeHOL (.comb shapes) := by
    have hsplit := sizeOfShapeHOL_comb_append (shapes.take n) (shapes.drop n)
    rw [List.take_append_drop] at hsplit
    have hdrop := sizeOfShapeHOLDropHeadSizeLe shapes n hnshapes
    omega
  have hbound : sizeOfShapeHOL (.comb (shapes.take n)) + n' < names.length := by
    rw [hnames, ← hsize]
    exact hboundSize
  have hbound' : sizeOfShapeHOL (.comb (shapes.take n)) + n' <
      (args.map flattenHOL).flatten.length := by
    rw [← hnames]
    exact hbound
  have hwfShapes : ∀ shape, shape ∈ shapes → isWfShapeNilHOL shape = true := by
    intro shape hmem
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hmem
    have hians : i < args.length := by omega
    have hval := hwf (args[i]'hians) (List.getElem_mem hians)
    have hbridge := isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil
      [] rfl (args[i]'hians)
    have hshape := listRelGetElem hrel hi hians
    rw [← hix, hshape]
    simpa [isWfShapeNilHOL] using hbridge.trans hval
  have hgroupElem :
      ((withShapeHOL shapes names)[n]'(by rw [withShapeHOLLength]; omega))[n']'hn' =
        names[sizeOfShapeHOL (.comb (shapes.take n)) + n']'hbound := by
    simp only [elElWithShapeHOL shapes names n n'
      ⟨hvalues, hnshapes, (by
        rw [elHOL_eq_getElem shapes n hnshapes]
        rw [hgroupSize]
        exact hn'val), hwfShapes⟩]
  have hflat? : ((args.map flattenHOL).flatten)[
      sizeOfShapeHOL (.comb (shapes.take n)) + n']? = (flattenHOL value)[n']? := by
    rw [hident, List.length_flatten, List.map_take,
      getElem?_flatten_take_sum (l := args.map flattenHOL) (n := n) (n' := n')
        (by rw [List.length_map]; exact hn)
        (by rw [List.getElem_map, hget]; exact hn'val)]
    rw [List.getElem_map, hget]
  have hflatElem : ((args.map flattenHOL).flatten)[
      sizeOfShapeHOL (.comb (shapes.take n)) + n']'hbound' =
      (flattenHOL value)[n']'(by rw [← hgroup]; exact hn') := by
    have hsome : ((args.map flattenHOL).flatten)[
        sizeOfShapeHOL (.comb (shapes.take n)) + n']? =
        some ((flattenHOL value)[n']'(by rw [← hgroup]; exact hn')) := by
      rw [hflat?, List.getElem?_eq_some_iff.mpr ⟨by rw [← hgroup]; exact hn', rfl⟩]
    obtain ⟨_, hfe⟩ := List.getElem?_eq_some_iff.mp hsome
    exact hfe
  rw [hgroupElem]
  exact (updateEqZipFlookupExactHOL names HolFiniteMapExact.empty
      (args.map flattenHOL).flatten (sizeOfShapeHOL (.comb (shapes.take n)) + n')
      ⟨hdistinct, hnames, hbound⟩).trans (congrArg some hflatElem)

end Flapjack
