import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
namespace Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
open Flapjack Flapjack.Pancake.PanLang
/-- Full unconditional original flatten preservation, including arbitrary
nested records and named fields; names are erased without reordering values. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "flatten_convert_v"
  (words_as_type_indexed_bitvec)]
theorem flattenConvertV {width : Nat} [NeZero width] (value : ValueHOL width) :
    flattenHOL (convertV value) = flattenHOL value := by
  refine ValueHOL.rec
    (motive_1 := fun value => flattenHOL (convertV value) = flattenHOL value)
    (motive_2 := fun values => values.map (fun value => flattenHOL (convertV value)) = values.map flattenHOL)
    (motive_3 := fun fields => fields.map (fun field => flattenHOL (convertV field.2)) =
      fields.map (fun field => flattenHOL field.2))
    (motive_4 := fun field => flattenHOL (convertV field.2) = flattenHOL field.2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ value
  all_goals intros
  all_goals simp_all [convertV, flattenHOL, List.map_map, Function.comp_def]
  · rename_i fields ih
    apply congrArg List.flatten
    apply List.map_congr_left
    intro entry hmem
    exact ih entry hmem
  · rename_i name fields ih
    apply congrArg List.flatten
    apply List.map_congr_left
    rintro ⟨fieldName, fieldValue⟩ hmem
    exact ih fieldName fieldValue hmem
  · assumption

end Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
