import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.DecCallExact

/-!
# `list_rel_length_shape_of_flatten` over the exact value carrier

Exact ports of HOL `panProps$list_rel_length_shape_of_flatten_better[local]` and
`list_rel_length_shape_of_flatten` (`cakeml/pancake/semantics/panPropsScript.sml:244-262`).
HOL `LIST_REL` is the exact `ListRel`, `EVERY is_wf_shape_v_nil` is membership
over `isWfShapeValueHOLExact []`, and `size_of_shape`/`shape_of`/`flatten` are
the tagged `sizeOfShapeHOL`/`shapeOfHOLExact`/`flattenHOL` over `ValueHOL`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL sizeOfShapeHOL sizeOfShapesHOL
  StructContextExact isWfShapeExactHOL)

/-- Exact port of HOL `list_rel_length_shape_of_flatten_better[local]`
    (`panPropsScript.sml:244-253`): `LIST_REL (λvsh arg. vsh = shape_of arg)
    vshs args /\ EVERY is_wf_shape_v_nil args ==>
    size_of_shape (Comb vshs) = LENGTH (FLAT (MAP flatten args))`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "list_rel_length_shape_of_flatten_better"]
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
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "list_rel_length_shape_of_flatten"]
theorem listRelLengthShapeOfFlattenHOL {width : Nat} [NeZero width] :
    ∀ (vshs : List (MlS × ShapeHOL)) (args : List (ValueHOL width)),
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

end Flapjack
