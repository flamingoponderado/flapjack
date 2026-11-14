(* Typed source declarations for backendProps (task 148). *)
load "preamble";
load "backendPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble backendPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="backendProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by backendProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of backendProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "oracle_monotonic_shift_seq_typed" "oracle_monotonic_shift_seq";
val _ = emit "oracle_monotonic_DISJOINT_init_typed" "oracle_monotonic_DISJOINT_init";
val _ = emit "is_state_oracle_k_typed" "is_state_oracle_k";
val _ = emit "oracle_monotonic_subset_typed" "oracle_monotonic_subset";
val _ = emit "state_orac_states_inv_typed" "state_orac_states_inv";
val _ = emit "syntax_to_full_oracle_def_typed" "syntax_to_full_oracle_def";
val _ = emit "state_orac_states_def_typed" "state_orac_states_def";
val _ = emit "state_co_progs_def_typed" "state_co_progs_def";
val _ = emit "add_state_co_def_typed" "add_state_co_def";
val _ = emit "state_co_def_typed" "state_co_def";
val _ = emit "oracle_monotonic_def_typed" "oracle_monotonic_def";
val _ = emit "is_state_oracle_def_typed" "is_state_oracle_def";
val _ = emit "oracle_monotonic_state_with_inv_typed" "oracle_monotonic_state_with_inv";
val _ = emit "oracle_monotonic_state_with_inv_init_typed" "oracle_monotonic_state_with_inv_init";
val _ = emit "oracle_monotonic_state_typed" "oracle_monotonic_state";
val _ = emit "oracle_monotonic_state_init_typed" "oracle_monotonic_state_init";
val _ = emit "option_le_SOME_0_typed" "option_le_SOME_0";
val _ = emit "option_add_comm_typed" "option_add_comm";
val _ = emit "option_add_assoc_typed" "option_add_assoc";
val _ = emit "option_le_add_typed" "option_le_add";
val _ = emit "pure_cc_def_typed" "pure_cc_def";
val _ = emit "pure_co_def_typed" "pure_co_def";
val _ = emit "SND_pure_co_typed" "SND_pure_co";
val _ = emit "FST_pure_co_typed" "FST_pure_co";
val _ = emit "pure_co_comb_pure_co_typed" "pure_co_comb_pure_co";
val _ = emit "pure_co_I_typed" "pure_co_I";
val _ = emit "pure_cc_I_typed" "pure_cc_I";
val _ = emit "option_le_def_typed" "option_le_def";
val _ = emit "option_le_max_right_typed" "option_le_max_right";
val _ = emit "option_le_refl_typed" "option_le_refl";
val _ = emit "option_le_trans_typed" "option_le_trans";
val _ = emit "restrict_nonzero_def_typed" "restrict_nonzero_def";
val _ = emit "restrict_nonzero_BIGUNION_typed" "restrict_nonzero_BIGUNION";
val _ = emit "restrict_nonzero_left_union_typed" "restrict_nonzero_left_union";
val _ = emit "restrict_nonzero_mono_typed" "restrict_nonzero_mono";
val _ = emit "restrict_nonzero_right_union_typed" "restrict_nonzero_right_union";
val _ = emit "restrict_nonzero_SUBSET_typed" "restrict_nonzero_SUBSET";
val _ = emit "restrict_nonzero_SUBSET_left_typed" "restrict_nonzero_SUBSET_left";
val _ = emit "restrict_zero_def_typed" "restrict_zero_def";
val _ = emit "option_le_max_typed" "option_le_max";
val _ = emit "option_le_eq_eqns_typed" "option_le_eq_eqns";
val _ = emit "option_map2_max_add_typed" "option_map2_max_add";
val _ = emit "OPTION_MAP2_MAX_COMM_typed" "OPTION_MAP2_MAX_COMM";
val _ = emit "OPTION_MAP2_MAX_ASSOC_typed" "OPTION_MAP2_MAX_ASSOC";
val _ = emit "state_cc_def_typed" "state_cc_def";
val _ = emit "FST_state_co_typed" "FST_state_co";
val _ = emit "SND_state_co_typed" "SND_state_co";
