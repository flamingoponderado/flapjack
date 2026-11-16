(* Typed source declarations for dataProps (task 148). *)
load "preamble";
load "dataPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble dataPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="dataProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by dataProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of dataProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "pop_env_const_typed" "pop_env_const";
val _ = emit "pop_env_safe_for_space_typed" "pop_env_safe_for_space";
val _ = emit "do_app_io_events_mono_typed" "do_app_io_events_mono";
val _ = emit "do_app_stack_max_typed" "do_app_stack_max";
val _ = emit "do_app_safe_for_space_mono_typed" "do_app_safe_for_space_mono";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_safe_for_space_mono_typed" "evaluate_safe_for_space_mono";
val _ = emit "evaluate_option_le_stack_max_typed" "evaluate_option_le_stack_max";
val _ = emit "do_app_aux_const_typed" "do_app_aux_const";
val _ = emit "do_app_const_typed" "do_app_const";
val _ = emit "do_app_aux_err_typed" "do_app_aux_err";
val _ = emit "do_app_err_typed" "do_app_err";
val _ = emit "EVERY_get_vars_typed" "EVERY_get_vars";
val _ = emit "get_vars_IMP_domain_typed" "get_vars_IMP_domain";
val _ = emit "get_vars_append_typed" "get_vars_append";
val _ = emit "get_vars_reverse_typed" "get_vars_reverse";
val _ = emit "var_corr_def_typed" "var_corr_def";
val _ = emit "get_vars_thm_typed" "get_vars_thm";
val _ = emit "get_code_labels_def_typed" "get_code_labels_def";
val _ = emit "cut_state_opt_with_const_typed" "cut_state_opt_with_const";
val _ = emit "do_app_aux_with_locals_typed" "do_app_aux_with_locals";
val _ = emit "do_app_aux_with_space_typed" "do_app_aux_with_space";
val _ = emit "consume_space_add_space_typed" "consume_space_add_space";
val _ = emit "same_stack_size_def_typed" "same_stack_size_def";
val _ = emit "same_stack_size_size_of_stack_typed" "same_stack_size_size_of_stack";
val _ = emit "s_peak_heap_typed" "s_peak_heap";
val _ = emit "evaluate_smx_safe_peak_swap_aux_typed" "evaluate_smx_safe_peak_swap_aux";
val _ = emit "evaluate_smx_safe_peak_swap_typed" "evaluate_smx_safe_peak_swap";
val _ = emit "evaluate_safe_peak_swap_aux_typed" "evaluate_safe_peak_swap_aux";
val _ = emit "evaluate_safe_peak_swap_typed" "evaluate_safe_peak_swap";
val _ = emit "do_app_safe_peak_swap_typed" "do_app_safe_peak_swap";
val _ = emit "do_app_sm_safe_peak_swap_typed" "do_app_sm_safe_peak_swap";
val _ = emit "do_app_aux_safe_peak_swap_typed" "do_app_aux_safe_peak_swap";
val _ = emit "do_app_aux_sm_safe_peak_swap_typed" "do_app_aux_sm_safe_peak_swap";
val _ = emit "do_app_err_safe_peak_swap_typed" "do_app_err_safe_peak_swap";
val _ = emit "do_app_err_sm_safe_peak_swap_typed" "do_app_err_sm_safe_peak_swap";
val _ = emit "size_of_heap_with_safe_typed" "size_of_heap_with_safe";
val _ = emit "OPTION_MAP2_ADD_SOME_0_typed" "OPTION_MAP2_ADD_SOME_0";
val _ = emit "OPTION_MAP2_MAX_CANCEL_typed" "OPTION_MAP2_MAX_CANCEL";
val _ = emit "OPTION_MAP2_NONE_typed" "OPTION_MAP2_NONE";
val _ = emit "initial_state_simp_typed" "initial_state_simp";
val _ = emit "initial_state_with_simp_typed" "initial_state_with_simp";
val _ = emit "with_same_locals_typed" "with_same_locals";
val _ = emit "do_stack_const_typed" "do_stack_const";
val _ = emit "Seq_Skip_typed" "Seq_Skip";
val _ = emit "do_space_alt_typed" "do_space_alt";
val _ = emit "evaluate_safe_alt_typed" "evaluate_safe_alt";
val _ = emit "evaluate_peak_alt_typed" "evaluate_peak_alt";
val _ = emit "set_var_const_typed" "set_var_const";
val _ = emit "set_var_with_const_typed" "set_var_with_const";
val _ = emit "set_vars_const_typed" "set_vars_const";
val _ = emit "set_vars_with_const_typed" "set_vars_with_const";
val _ = emit "call_env_const_typed" "call_env_const";
val _ = emit "call_env_with_const_typed" "call_env_with_const";
val _ = emit "push_env_const_typed" "push_env_const";
val _ = emit "push_env_with_const_typed" "push_env_with_const";
val _ = emit "dec_clock_const_typed" "dec_clock_const";
val _ = emit "add_space_const_typed" "add_space_const";
val _ = emit "with_clock_ffi_typed" "with_clock_ffi";
val _ = emit "with_same_clock_typed" "with_same_clock";
val _ = emit "cut_state_eq_some_typed" "cut_state_eq_some";
val _ = emit "cut_state_eq_none_typed" "cut_state_eq_none";
val _ = emit "size_of_heap_with_clock_typed" "size_of_heap_with_clock";
val _ = emit "size_of_heap_args_with_clock_typed" "size_of_heap_args_with_clock";
val _ = emit "do_app_Rerr_typed" "do_app_Rerr";
val _ = emit "pop_env_with_const_typed" "pop_env_with_const";
val _ = emit "jump_exc_with_const_typed" "jump_exc_with_const";
val _ = emit "cut_state_opt_const_typed" "cut_state_opt_const";
val _ = emit "Boolv_11_typed" "Boolv_11";
val _ = emit "do_app_with_clock_typed" "do_app_with_clock";
val _ = emit "do_app_change_clock_typed" "do_app_change_clock";
val _ = emit "space_consumed_with_clock_typed" "space_consumed_with_clock";
val _ = emit "do_app_lss_sm_safe_peak_swap_typed" "do_app_lss_sm_safe_peak_swap";
val _ = emit "do_app_aux_lss_sm_safe_peak_swap_typed" "do_app_aux_lss_sm_safe_peak_swap";
val _ = emit "do_app_err_lss_sm_safe_peak_swap_typed" "do_app_err_lss_sm_safe_peak_swap";
val _ = show "do_app_lss_sm_safe_peak_swap_aux_typed"
  (prove(``!op vs s q s' lss smx safe peak. dataSem$do_app op vs s = Rval (q,s') ==>
      ?safe' peak' lss' smx'.
        dataSem$do_app op vs (s with <|locals_size := lss; stack_max := smx; safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q, s' with <|locals_size := lss'; stack_max := smx'; safe_for_space := safe'; peak_heap_length := peak' |>)``,
    metis_tac [dataPropsTheory.do_app_lss_sm_safe_peak_swap]));
val _ = show "do_app_sm_safe_peak_swap_aux_typed"
  (prove(``!op vs s q s' smx safe peak. dataSem$do_app op vs s = Rval (q,s') ==>
      ?safe' peak' smx'.
        dataSem$do_app op vs (s with <|stack_max := smx; safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q, s' with <|stack_max := smx'; safe_for_space := safe'; peak_heap_length := peak' |>)``,
    metis_tac [dataPropsTheory.do_app_sm_safe_peak_swap]));
val _ = emit "do_app_lss_stk_stfrm_swap_typed" "do_app_lss_stk_stfrm_swap";
val _ = emit "do_app_err_lss_stk_stfrm_swap_typed" "do_app_err_lss_stk_stfrm_swap";
val _ = show "do_app_lss_stk_stfrm_swap_aux_typed"
  (prove(``!op vs s q s' lss stk stfrm. dataSem$do_app op vs s = Rval (q,s') ==>
      ?ss pk smx.
        dataSem$do_app op vs (s with <|locals_size := lss; stack := stk; stack_frame_sizes := stfrm |>) =
        Rval (q, s' with <|locals_size := lss; stack := stk;
                           stack_frame_sizes := if op = closLang$Install then LN else stfrm;
                           stack_max := smx; safe_for_space := ss; peak_heap_length := pk|>)``,
    metis_tac [dataPropsTheory.do_app_lss_stk_stfrm_swap]));
val _ = emit "do_app_lim_swap_typed" "do_app_lim_swap";
val _ = emit "do_app_err_lim_swap_typed" "do_app_err_lim_swap";
val _ = show "do_app_lim_swap_aux_typed"
  (prove(``!op vs s q s' lim. dataSem$do_app op vs s = Rval (q,s') ==>
      ?safe peak smx.
        dataSem$do_app op vs (s with limits := lim) =
        Rval (q, s' with <|limits := lim; stack_max := smx;
                           safe_for_space := safe; peak_heap_length := peak |>)``,
    metis_tac [dataPropsTheory.do_app_lim_swap]));
val _ = emit "jump_exc_NONE_typed" "jump_exc_NONE";
val _ = emit "size_of_stack_eq_typed" "size_of_stack_eq";
val _ = emit "locals_ok_IMP_typed" "locals_ok_IMP";
val _ = emit "locals_ok_get_var_typed" "locals_ok_get_var";
val _ = show "locals_ok_insert_typed"
  (prove(``!a b k (v:'a). locals_ok a b ==> locals_ok (insert k v a) (insert k v b)``,
    rw[locals_ok_def, sptreeTheory.lookup_insert] \\ every_case_tac \\ gvs[]));
val _ = emit "find_code_upto_size_typed" "find_code_upto_size";
val _ = emit "stack_frame_size_rel_def_typed" "stack_frame_size_rel_def";
val _ = emit "do_app_stack_eq_typed" "do_app_stack_eq";
val _ = emit "do_app_stack_frame_size_rel_typed" "do_app_stack_frame_size_rel";
val _ = emit "do_app_change_clock_err_typed" "do_app_change_clock_err";
val _ = show "cut_state_opt_with_lim_typed"
  (prove(``!names_opt (s:('a,'b) dataSem$state) (lim:dataSem$limits).
      cut_state_opt names_opt (s with limits := lim) =
      OPTION_MAP (λt. t with limits := lim) (cut_state_opt names_opt s)``,
    Cases_on `names_opt` \\ rw[dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, dataSemTheory.cut_env_def]
    \\ rw[dataSemTheory.state_component_equality]));
val _ = show "cut_state_opt_with_sfs_typed"
  (prove(``!names_opt (s:('a,'b) dataSem$state) (lsz:num option) (xs:stack list)
      (sfs:num sptree$num_map).
      cut_state_opt names_opt
        (s with <|locals_size := lsz; stack := xs; stack_frame_sizes := sfs|>) =
      OPTION_MAP (λt. t with <|locals_size := lsz; stack := xs; stack_frame_sizes := sfs|>)
        (cut_state_opt names_opt s)``,
    Cases_on `names_opt`
    \\ rw[dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, dataSemTheory.cut_env_def]
    \\ rw[dataSemTheory.state_component_equality]));
val _ = show "cut_state_opt_stack_typed"
  (prove(``!names_opt (s:('a,'b) dataSem$state) (s1:('a,'b) dataSem$state).
      cut_state_opt names_opt s = SOME s1 ==> s1.stack = s.stack``,
    Cases_on `names_opt`
    \\ rw[dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def]
    \\ every_case_tac \\ gvs[]));
val _ = show "OPTION_CASE_OPTION_MAP_typed"
  (prove(``!(f:'a -> 'b) (a:'a option) (e:'c) (g:'b -> 'c).
      option_CASE (OPTION_MAP f a) e g = option_CASE a e (g o f)``,
    Cases_on `a` >> fs[]));
val _ = show "cut_state_opt_cc_co_full_typed"
  (prove(``!(t:('b,'ffi)dataSem$state) (s:('a,'ffi)dataSem$state)
      (names_opt:sptree$num_set option).
      t.locals = s.locals ==>
      cut_state_opt names_opt t =
      OPTION_MAP (λu. t with locals := u.locals) (cut_state_opt names_opt s)``,
    strip_tac \\ Cases_on `names_opt`
    \\ rw[dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, dataSemTheory.cut_env_def]
    \\ gvs[dataSemTheory.state_component_equality]));
