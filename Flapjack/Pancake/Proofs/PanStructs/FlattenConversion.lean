import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
namespace Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
open Flapjack Flapjack.Pancake.PanLang
/-- Full unconditional original flatten preservation, including arbitrary
nested records and named fields; names are erased without reordering values. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "flatten_convert_v"
  (words_as_type_indexed_bitvec)]
theorem flattenConvertV {width : Nat} [NeZero width] (value : ValueHOL width) :
    flattenHOL (convertV value) = flattenHOL value := by
  fun_induction convertV value with
  | case1 => rfl
  | case2 values ih =>
      simp only [flattenHOL, List.map_map, Function.comp_def]
      exact congrArg List.flatten (List.map_congr_left ih)
  | case3 name fields ih =>
      simp only [flattenHOL, List.map_map, Function.comp_def]
      apply congrArg List.flatten
      exact List.map_congr_left (fun (name, value) h => ih (name, value) h)

end Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
