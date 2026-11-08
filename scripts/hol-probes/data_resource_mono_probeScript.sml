load "preamble"; load "dataPropsTheory";
open HolKernel Parse bossLib preamble dataPropsTheory;
val _ = new_theory "flapjack_data_resource_mono_probe";
val _ = Globals.linewidth := 1000000;
fun show name th =
  (if null (hyp th) then () else raise Fail ("unexpected hypotheses: " ^ name);
   print (name ^ "=");
   Lib.with_flag (Globals.show_types,true) print_term (concl th);
   print "\n");
val _ = show "do_app_io_events_mono_typed" do_app_io_events_mono;
val _ = show "do_app_safe_for_space_mono_typed" do_app_safe_for_space_mono;
val _ = show "do_app_stack_max_typed" do_app_stack_max;
val _ = show "evaluate_io_events_mono_typed" evaluate_io_events_mono;
val _ = show "evaluate_safe_for_space_mono_typed" evaluate_safe_for_space_mono;
val _ = show "evaluate_option_le_stack_max_typed" evaluate_option_le_stack_max;
val _ = show "evaluate_smx_safe_peak_swap_typed" evaluate_smx_safe_peak_swap;
val _ = show "evaluate_safe_peak_swap_typed" evaluate_safe_peak_swap;
val _ = show "do_app_err_safe_peak_swap_typed" do_app_err_safe_peak_swap;
val _ = show "do_app_err_sm_safe_peak_swap_typed" do_app_err_sm_safe_peak_swap;
val _ = show "do_app_safe_peak_swap_typed" do_app_safe_peak_swap;
val _ = show "do_app_sm_safe_peak_swap_typed" do_app_sm_safe_peak_swap;
val _ = show "size_of_heap_with_safe_typed" size_of_heap_with_safe;
val _ = show "do_app_aux_safe_peak_swap_typed" do_app_aux_safe_peak_swap;
val _ = show "do_app_aux_sm_safe_peak_swap_typed" do_app_aux_sm_safe_peak_swap;
val _ = show "cut_env_typed" dataSemTheory.cut_env_def;
val _ = show "cut_state_typed" dataSemTheory.cut_state_def;
val _ = show "cut_state_opt_typed" dataSemTheory.cut_state_opt_def;
val _ = show "call_env_typed" dataSemTheory.call_env_def;
val _ = show "get_var_typed" dataSemTheory.get_var_def;
val _ = show "get_vars_typed" dataSemTheory.get_vars_def;
val _ = show "set_var_typed" dataSemTheory.set_var_def;
val _ = show "set_vars_typed" dataSemTheory.set_vars_def;
val _ = show "flush_state_typed" dataSemTheory.flush_state_def;
val _ = show "push_env_typed" dataSemTheory.push_env_def;
val _ = show "pop_env_typed" dataSemTheory.pop_env_def;
val _ = show "jump_exc_typed" dataSemTheory.jump_exc_def;
val _ = show "find_code_typed" dataSemTheory.find_code_def;
val _ = show "is_bool_typed" dataSemTheory.isBool_def;
val _ = show "install_sfs_typed" dataSemTheory.install_sfs_def;
val _ = show "initial_state_typed" dataSemTheory.initial_state_def;
val _ = show "add_space_typed" dataSemTheory.add_space_def;
val _ = show "op_requires_names_typed" dataLangTheory.op_requires_names_def;
val _ = show "evaluate_clock_typed" dataSemTheory.evaluate_clock;
val _ = show "fix_clock_evaluate_typed" dataSemTheory.fix_clock_evaluate;
val setVarsClock = prove (``(dataSem$set_vars ns vs s).clock = s.clock``,
  simp [dataSemTheory.set_vars_def]);
val _ = show "set_vars_clock_replay_typed" setVarsClock;
val cutSwap = prove (``dataSem$cut_state_opt names_opt
    (s with <|stack_max := smx; safe_for_space := safe; peak_heap_length := peak|>) =
  OPTION_MAP (λt. t with <|stack_max := smx; safe_for_space := safe;
                           peak_heap_length := peak|>)
             (dataSem$cut_state_opt names_opt s)``,
  Cases_on `names_opt` \\ rw[dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, dataSemTheory.cut_env_def]
  \\ rw[dataSemTheory.state_component_equality]);
val _ = show "cut_state_opt_with_swap_replay_typed" cutSwap;
val cutStackMax = prove (``dataSem$cut_state_opt names_opt s = SOME s2 ⇒ s2.stack_max = s.stack_max``,
  Cases_on `names_opt` \\ rw[dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def]
  \\ every_case_tac \\ gvs[]);
val _ = show "cut_state_opt_stack_max_replay_typed" cutStackMax;
val cutSwapInput = prove (``dataSem$cut_state_opt names_opt s = SOME s2 ⇒
    s2 with <|stack_max := s.stack_max; safe_for_space := safe;
              peak_heap_length := peak|> =
    s2 with <|safe_for_space := safe; peak_heap_length := peak|>``,
  rw[] \\ imp_res_tac cutStackMax \\ rw[dataSemTheory.state_component_equality]);
val _ = show "cut_state_opt_swap_input_replay_typed" cutSwapInput;
