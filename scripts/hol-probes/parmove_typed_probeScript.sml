(* Typed source declarations for parmove (task 148). *)
load "preamble";
load "parmoveTheory";
open HolKernel Parse boolLib bossLib;
open preamble parmoveTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="parmove",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by parmove")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of parmove")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "fstep_def_typed" "fstep_def";
val _ = emit "parmove_def_typed" "parmove_def";
val _ = emit "pmov_def_typed" "pmov_def";
val _ = emit "ALL_DISTINCT_parmove_typed" "ALL_DISTINCT_parmove";
val _ = emit "ALL_DISTINCT_pmov_typed" "ALL_DISTINCT_pmov";
val _ = emit "ALL_DISTINCT_step_typed" "ALL_DISTINCT_step";
val _ = emit "ALL_DISTINCT_steps_typed" "ALL_DISTINCT_steps";
val _ = emit "parmove_correct_typed" "parmove_correct";
val _ = emit "dstep_cases_typed" "dstep_cases";
val _ = emit "dstep_ind_typed" "dstep_ind";
val _ = emit "dstep_rules_typed" "dstep_rules";
val _ = emit "dsteps_steps_typed" "dsteps_steps";
val _ = emit "MEM_MAP_FST_SND_SND_pmov_typed" "MEM_MAP_FST_SND_SND_pmov";
val _ = emit "MEM_MAP_FST_parmove_typed" "MEM_MAP_FST_parmove";
val _ = emit "parsem_change_env_typed" "parsem_change_env";
val _ = emit "fstep_dstep_typed" "fstep_dstep";
val _ = emit "fstep_MAP_INJ_typed" "fstep_MAP_INJ";
val _ = emit "independence_typed" "independence";
val _ = emit "parsem_nil_typed" "parsem_nil";
val _ = emit "inj_on_state_def_typed" "inj_on_state_def";
val _ = emit "step_inj_on_state_typed" "step_inj_on_state";
val _ = emit "path_def_typed" "path_def";
val _ = emit "path_tail_typed" "path_tail";
val _ = emit "wf_def_typed" "wf_def";
val _ = emit "wf_init_typed" "wf_init";
val _ = emit "path_change_start_typed" "path_change_start";
val _ = emit "windmill_cons_typed" "windmill_cons";
val _ = emit "wf_step_typed" "wf_step";
val _ = emit "wf_steps_typed" "wf_steps";
val _ = emit "parmove_MAP_INJ_typed" "parmove_MAP_INJ";
val _ = emit "pmov_MAP_INJ_typed" "pmov_MAP_INJ";
val _ = emit "steps_inj_on_state_typed" "steps_inj_on_state";
val _ = emit "map_state_def_typed" "map_state_def";
val _ = emit "parsem_NoRead_typed" "parsem_NoRead";
val _ = emit "parsem_MAP_INJ_typed" "parsem_MAP_INJ";
val _ = emit "parsem_perm_typed" "parsem_perm";
val _ = emit "pmov_dsteps_typed" "pmov_dsteps";
val _ = emit "pmov_final_typed" "pmov_final";
val _ = emit "parmove_preserves_moves_typed" "parmove_preserves_moves";
val _ = emit "pmov_preserves_moves_typed" "pmov_preserves_moves";
val _ = emit "step_preserves_moves_typed" "step_preserves_moves";
val _ = emit "steps_preserves_moves_typed" "steps_preserves_moves";
val _ = emit "eqenv_def_typed" "eqenv_def";
val _ = emit "parsem_def_typed" "parsem_def";
val _ = emit "sem_def_typed" "sem_def";
val _ = emit "sem_final_typed" "sem_final";
val _ = emit "sem_init_typed" "sem_init";
val _ = emit "seqsem_def_typed" "seqsem_def";
val _ = emit "seqsem_append_typed" "seqsem_append";
val _ = emit "windmill_def_typed" "windmill_def";
val _ = emit "seqsem_move_unchanged_typed" "seqsem_move_unchanged";
val _ = emit "MEM_MAP_SND_SND_SND_pmov_typed" "MEM_MAP_SND_SND_SND_pmov";
val _ = emit "MEM_MAP_SND_parmove_typed" "MEM_MAP_SND_parmove";
val _ = emit "state_to_list_def_typed" "state_to_list_def";
val _ = emit "step_MAP_INJ_typed" "step_MAP_INJ";
val _ = emit "step_cases_typed" "step_cases";
val _ = emit "step_ind_typed" "step_ind";
val _ = emit "step_rules_typed" "step_rules";
val _ = emit "steps_correct_typed" "steps_correct";
val _ = emit "steps_sem_typed" "steps_sem";
val _ = emit "not_use_temp_before_assign_def_typed" "not_use_temp_before_assign_def";
val _ = emit "not_use_temp_before_assign_append_typed" "not_use_temp_before_assign_append";
val _ = emit "not_use_temp_before_assign_thm_typed" "not_use_temp_before_assign_thm";
val _ = emit "not_use_temp_before_assign_insert_typed" "not_use_temp_before_assign_insert";
val _ = emit "parmove_not_use_temp_before_assign_typed" "parmove_not_use_temp_before_assign";
val _ = emit "pmov_not_use_temp_before_assign_typed" "pmov_not_use_temp_before_assign";
val _ = emit "step_not_use_temp_before_assign_typed" "step_not_use_temp_before_assign";
val _ = emit "steps_not_use_temp_before_assign_typed" "steps_not_use_temp_before_assign";
val _ = emit "parsem_cons_typed" "parsem_cons";
val _ = emit "parsem_untouched_typed" "parsem_untouched";
