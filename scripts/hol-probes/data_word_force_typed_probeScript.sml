(* Inferred source type and complete thunk-force compilation equation. *)
load "data_to_wordTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "force_thunk_typed="; print_thm data_to_wordTheory.force_thunk_def; print "\n");
val _ = (print "arg4_typed="; print_thm data_to_wordTheory.arg4_def; print "\n");
val _ = (print "set_bool_typed="; print_thm data_to_wordTheory.SetBool_def; print "\n");
val _ = (print "assign_cmp_typed="; print_thm data_to_wordTheory.AssignCmp_def; print "\n");
val _ = (print "assign_string_cmp_typed="; print_thm data_to_wordTheory.assign_StringCmp_def; print "\n");
val _ = (print "assign_bounds_byte_typed="; print_thm data_to_wordTheory.assign_BoundsCheckByte_def; print "\n");
val _ = (print "assign_bounds_array_typed="; print_thm data_to_wordTheory.assign_BoundsCheckArray_def; print "\n");
val _ = (print "assign_bounds_block_typed="; print_thm data_to_wordTheory.assign_BoundsCheckBlock_def; print "\n");
val _ = (print "assign_equal_typed="; print_thm data_to_wordTheory.assign_Equal_def; print "\n");
val _ = (print "assign_less_typed="; print_thm data_to_wordTheory.assign_Less_def; print "\n");
val _ = (print "assign_less_eq_typed="; print_thm data_to_wordTheory.assign_LessEq_def; print "\n");
val _ = (print "assign_len_eq_typed="; print_thm data_to_wordTheory.assign_LenEq_def; print "\n");
val _ = (print "assign_tag_len_eq_typed="; print_thm data_to_wordTheory.assign_TagLenEq_def; print "\n");
val _ = (print "assign_tag_eq_typed="; print_thm data_to_wordTheory.assign_TagEq_def; print "\n");
