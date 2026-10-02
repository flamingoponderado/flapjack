#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/../.." && pwd)
hol_dir=${HOL4:-/home/zksecurity/HOL}
cake_dir=${CAKEML:-"$repo_dir/cakeml"}

if [[ ! -x "$hol_dir/bin/Holmake" ]]; then
  echo "HOL4 Holmake not found: $hol_dir/bin/Holmake" >&2
  exit 2
fi
if [[ ! -f "$cake_dir/pancake/loop_to_wordScript.sml" ]]; then
  echo "CakeML Pancake source not found: $cake_dir/pancake/loop_to_wordScript.sml" >&2
  exit 2
fi
if [[ ! -f "$cake_dir/pancake/semantics/panSemScript.sml" ]]; then
  echo "CakeML Pancake source not found: $cake_dir/pancake/semantics/panSemScript.sml" >&2
  exit 2
fi
if [[ ! -f "$cake_dir/pancake/semantics/loopSemScript.sml" ]]; then
  echo "CakeML Pancake source not found: $cake_dir/pancake/semantics/loopSemScript.sml" >&2
  exit 2
fi

probe_dir="$repo_dir/scripts/hol-probes"
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

# HOL's `hol run` consumes the already-built CakeML theories; it does not need
# to rebuild an unchanged theory.  Keep the checked-in fixtures incremental as
# well: rerun a probe only when its script or its referenced Pancake source is
# newer than the fixture.  Changes to this driver do not invalidate probe
# results, so ordinary harness maintenance stays incremental.
probe_needs_refresh() {
  local output="$1"
  local probe="$2"
  local source="$3"
  [[ ! -f "$output" || "$probe" -nt "$output" || "$source" -nt "$output" ]]
}

run_probe() {
  local probe_name="$1"
  local output_name="$2"
  shift 2
  if [[ -n "${HOL_PROBE_ONLY:-}" && "$probe_name" != "$HOL_PROBE_ONLY" ]]; then
    return 0
  fi
  local labels=()
  while [[ $# -gt 0 ]]; do
    case "$1" in
      /*|\$*) break ;;
      *) labels+=("$1"); shift ;;
    esac
  done
  local first_label=""
  local last_label=""
  if [[ ${#labels[@]} -gt 0 ]]; then
    first_label="${labels[0]}"
    last_label="${labels[${#labels[@]}-1]}"
  fi
  local source="$1"
  shift
  local workdir="${1:-$cake_dir/pancake}"
  # Run from the theory source directory. HOL resolves sibling `.hol/objs`
  # entries from there; using the object directory itself makes it search a
  # nested `.hol/objs/.hol/objs` and fails to load shared theories such as
  # CakeML's `preamble`.
  local hol_workdir="$workdir"
  local probe="$probe_dir/$probe_name"
  local output="$probe_dir/$output_name"
  if probe_needs_refresh "$output" "$probe" "$source"; then
    (cd "$hol_workdir" && \
      "$hol_dir/bin/hol" run "$probe") >"$tmp"
    if [[ ${#labels[@]} -eq 0 ]]; then
      cp "$tmp" "$output"
    else
      awk -v first="$first_label" -v last="$last_label" '
        BEGIN { started = 0; ended = 0 }
        {
          if (!started) {
            if (index($0, first "=") != 1) next
            started = 1
          } else if (ended && $0 ~ /^[[:alnum:]_]+=/) {
            exit
          }
          if (index($0, last "=") == 1) ended = 1
          print
        }
      ' "$tmp" \
        | sed '/^<<HOL message:/,/^  pattern completion.*>>$/d; /^$/d' > "$output"
    fi
  fi
  # The first and last rows delimit the captured HOL transcript, but every
  # listed row is part of the probe's regression contract. Check middle rows
  # too, so extending a probe cannot silently drop an older sentinel.
  for label in "${labels[@]}"; do
    if ! grep -q "^${label}=" "$output"; then
      echo "Expected HOL probe row '$label' missing from $output_name" >&2
      exit 1
    fi
  done
}

run_probe lab_to_target_encoding_similarity_probeScript.sml lab_to_target_encoding_similarity_probe.out \
  es_line es_line_types es_initial es_initial_types es_again es_again_types es_sections es_sections_types es_initial_value es_again_growth es_again_unchanged es_again_no_growth es_sections_value es_sections_similar \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe lab_to_target_padding_similarity_probeScript.sml lab_to_target_padding_similarity_probe.out \
  ps_add ps_add_types ps_section ps_section_types ps_code ps_code_types ps_add_value ps_section_value ps_empty_nop ps_acc_value ps_label_only ps_code_similar \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe asmprops_arithmetic_preservation_probeScript.sml asmprops_arithmetic_preservation_probe.out \
  ap_upd_pc_simps ap_upd_pc_simps_types ap_binop_upd_consts ap_binop_upd_consts_types ap_arith_upd_consts ap_arith_upd_consts_types ap_add ap_shift_fail ap_div_zero ap_longmul ap_longdiv_zero ap_carry ap_addoverflow ap_suboverflow ap_pc \
  "$cake_dir/compiler/encoders/asm/asmPropsScript.sml" "$cake_dir/compiler/encoders/asm"

run_probe stacksem_fp_case_types_probeScript.sml stacksem_fp_case_types_probe.out \
  fpc_inst fpc_constructor fpc_lookup fpc_update fpc_general_lookup fpc_general_update fpc_all_payloads \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stackprops_expression_clock_probeScript.sml stackprops_expression_clock_probe.out \
  ec_store_statement ec_store_types ec_word_statement ec_word_types ec_assign_statement ec_assign_types ec_const ec_var_word ec_var_loc ec_var_missing ec_lookup_word ec_lookup_loc ec_lookup_missing ec_load_word ec_load_loc ec_load_oob ec_load_bad_address ec_op_empty_and ec_op_add_wrap ec_op_sub_bad_arity ec_op_bad_operand ec_shift_valid ec_shift_oob ec_shift_bad_right ec_assign_success ec_assign_failure ec_store_success ec_store_failure \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stackprops_instruction_constants_probeScript.sml stackprops_instruction_constants_probe.out \
  ic_fields ic_fields_types ic_map ic_map_types ic_clock ic_clock_types ic_ffi ic_ffi_types ic_const_clock ic_const_clock_zero ic_div_failure ic_or_location ic_store_success ic_store_failure ic_fp_abs ic_fp_missing ic_const_ffi ic_none_ffi \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stackprops_clock_support_probeScript.sml stackprops_clock_support_probe.out \
  cp_asm_const_type cp_clock_neutral_type cp_1 cp_1_types cp_2 cp_2_types cp_3 cp_3_types cp_4 cp_4_types cp_5 cp_5_types cp_6 cp_6_types cp_skip64 cp_sqrt1 cp_halt16 cp_loc1 cp_seq_good64 cp_seq_tick16 cp_if_good1 cp_if_bad64 cp_loop_skip64 cp_call_skip1 \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stackprops_state_constants_probeScript.sml stackprops_state_constants_probe.out \
  sc_20 sc_20_types sc_43 sc_43_types sc_49 sc_49_types sc_74 sc_74_types sc_84 sc_84_types sc_90 sc_90_types sc_110 sc_110_types sc_116 sc_116_types sc_125 sc_125_types sc_131 sc_131_types sc_137 sc_137_types sc_144 sc_144_types sc_164 sc_164_types \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_fp_conversion_types_probeScript.sml stacksem_fp_conversion_types_probe.out \
  fp_inst_type fp_get_type fp_set_type fp_sqrt_type fp_to_int_type fp_from_int_type fp_oracle_type \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_copy_ret_no_install_probeScript.sml word_to_stack_copy_ret_no_install_probe.out \
  crni_zero_bad crni_plain_good crni_handler_bad crni_perf_good crni_perf_bad crni_option_tail_handler crni_empty_list_loop crni_exact_count_zero \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_convs_no_install_def_probeScript.sml word_convs_no_install_def_probe.out \
  wcni_01_mt wcni_02_seq wcni_03_loop wcni_04_if wcni_05_call wcni_06_alloc wcni_07_loc wcni_08_share wcni_09_install wcni_10_skip wcni_11_move wcni_12_inst wcni_13_assign wcni_14_get wcni_15_set wcni_16_store wcni_17_consts wcni_18_raise wcni_19_return wcni_20_break wcni_21_continue wcni_22_tick wcni_23_heap wcni_24_code wcni_25_data wcni_26_ffi wcni_call_none_none_width1 wcni_call_return_only_width1 wcni_call_both_present_width1 \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_no_install_helpers_probeScript.sml word_to_stack_no_install_helpers_probe.out \
  ni_moves_empty ni_moves_all_pairs ni_load_install ni_load_skip ni_reg1_direct ni_reg1_spill ni_reg2_direct ni_reg2_spill ni_live_zero ni_live_frame ni_stack_move_install ni_stack_move_zero ni_copy_aux_zero ni_copy_aux_many \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_copy_ret_carriers_probeScript.sml word_to_stack_copy_ret_carriers_probe.out \
  ret_tail_bool_zero ret_tail_bool_plain ret_tail_list_handle ret_tail_list_perf ret_tail_install \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe asmprops_assertions_iteration_probeScript.sml asmprops_assertions_iteration_probe.out \
  assert_theorem_fold assert_theorem_less assert_theorem_weaken assert_theorem_change assert_theorem_first assert_theorem_every \
  "$cake_dir/compiler/encoders/asm/asmPropsScript.sml" "$cake_dir/compiler/encoders/asm"

run_probe asmprops_assertions_probeScript.sml asmprops_assertions_probe.out \
  assert_zero_skip_p assert_zero_runs_next assert_order_ok assert_order_bad assert_count_fold assert_prefixes assert_weaken_bound assert_state_bool assert2_zero assert2_mixed_ok assert2_mixed_bad assert2_changed_above assert2_first_pair assert2_constant_ok assert2_every_pairs assert2_first_bad \
  "$cake_dir/compiler/encoders/asm/asmPropsScript.sml" "$cake_dir/compiler/encoders/asm"

run_probe asmsem_fp_updates_probeScript.sml asmsem_fp_updates_probe.out \
  asm_fp_less_nan asm_fp_less_equal_zero asm_fp_equal_nan asm_fp_equal_zero asm_fp_mov_payload asm_fp_abs_payload asm_fp_neg_zero asm_fp_sqrt_four asm_fp_add_two asm_fp_sub_zero asm_fp_mul_four asm_fp_div_half asm_fp_fma_order asm_fp_to_reg64 asm_fp_to_reg_alias32 asm_fp_from_reg64 asm_fp_from_reg32 asm_fp_from_reg8 asm_fp_to_int_tie_even asm_fp_to_int_negative asm_fp_to_int_overflow_bits asm_fp_to_int_overflow_failed asm_fp_to_int_inf_error asm_fp_to_int_odd32 asm_fp_from_int64 asm_fp_from_int32 asm_fp_from_int8 asm_fp_from_int128 asm_fp_to_int_lower_alias32 asm_fp_to_int_upper_alias32 asm_fp_to_int_overflow32 asm_fp_to_reg8 asm_fp_from_reg128 asm_fp_prior_failure \
  "$cake_dir/compiler/encoders/asm/asmSemScript.sml" "$cake_dir/compiler/encoders/asm"

run_probe asmprops_pc_coverage_probeScript.sml asmprops_pc_coverage_probe.out \
  pcs_empty pcs_byte_wrap pcs_stride_short pcs_stride_exact pcs_stride_tail pcs_stride_twice pcs_stride_extra pcs_dimension_stride pcs_large_stride pcs_width1_duplicates pcs_width1_stride pcs_width32_wrap pcs_width64_wrap \
  "$cake_dir/compiler/encoders/asm/asmPropsScript.sml" "$cake_dir/compiler/encoders/asm"

run_probe lab_to_target_section_lookup_probeScript.sml lab_to_target_section_lookup_probe.out \
  section_entry section_label5 section_label7 section_missing preceding_entry preceding_label5 empty_tail_entry empty_tail_missing \
  "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe target_props_interference_probeScript.sml target_props_interference_probe.out \
  shift_zero shift_three shift_composition shift_ffi_unchanged shift_target_unchanged region_empty region_safe_before_wrap region_wrap_hits_entry \
  "$cake_dir/compiler/backend/semantics/targetPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe asmsem_arithmetic_probeScript.sml asmsem_arithmetic_probe.out \
  asm_binop_add asm_binop_sub asm_binop_and asm_binop_or asm_binop_xor asm_lsl_reg_valid asm_lsl_reg_invalid asm_lsl_imm_past asm_lsr_reg_invalid asm_asr_reg_invalid asm_ror_reg_invalid asm_ror_imm_past asm_shift_alias_count asm_div_ok asm_div_zero_write asm_div_source_alias asm_longmul asm_longmul_alias asm_longdiv_ok asm_longdiv_overflow_write asm_longdiv_zero_write asm_longdiv_alias asm_addcarry asm_addcarry_no_carry asm_addcarry_alias asm_addoverflow asm_addoverflow_no_flag asm_addoverflow_alias asm_suboverflow asm_suboverflow_alias asm_prior_failure asm_width1_carry asm_width32_overflow asm_width64_longmul asm_upd_pc asm_upd_reg asm_upd_reg_other asm_upd_fp_reg asm_upd_mem asm_upd_mem_other asm_assert_false asm_assert_prior asm_reg_imm_reg asm_reg_imm_imm asm_is_test_equal asm_is_test_lower asm_is_test_less asm_is_test_test asm_is_test_notequal asm_is_test_notlower asm_is_test_notless asm_is_test_nottest \
  "$cake_dir/compiler/encoders/asm/asmSemScript.sml" "$cake_dir/compiler/encoders/asm"
run_probe bytes_in_mem_probeScript.sml bytes_in_mem_probe.out \
  empty_ignores_guards nat_wrap excluded_head excluded_tail domain_head domain_tail wrong_value bool_payload update_off_region update_hit_region append_wrapped \
  "$cake_dir/misc/miscScript.sml" "$cake_dir/misc"
run_probe pan_globals_fperm_code_probeScript.sml pan_globals_fperm_code_probe.out \
  swap_f swap_g other missing equal_names \
  "$cake_dir/pancake/proofs/pan_globalsProofScript.sml" "$cake_dir/pancake/proofs"
run_probe stacksem_fpreg_inst_probeScript.sml stacksem_fpreg_inst_probe.out \
  fpreg_mov_nan fpreg_mov_missing fpreg_abs_nan fpreg_abs_zero fpreg_neg_nan fpreg_neg_zero fpreg_abs_missing fpreg_neg_missing fpreg_to64 fpreg_to32 fpreg_to8 fpreg_to32_alias fpreg_to_missing fpreg_from64_ignore fpreg_from64_loc fpreg_from32 fpreg_from8 fpreg_from32_missing fpreg_from32_loc fpreg_from32_alias \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_fp_arith_probeScript.sml stacksem_fp_arith_probe.out \
  fpless_true fpless_false fpless_equal fpless_missing fplessequal_true fplessequal_false fpequal_true fpequal_false fpadd_result fpadd_missing fpsub_result fpmul_result fpdiv_result fpfma_order \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_fp_convert_probeScript.sml stacksem_fp_convert_probe.out \
  fpsqrt_result fpsqrt_missing fptoint_result fptoint_out_of_range fptoint_missing fptoint32_even fptoint32_odd fpfromint_result fpfromint_missing fpfromint32_even fpfromint32_odd \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_store_consts_guard_probeScript.sml stacksem_store_consts_guard_probe.out \
  guard_none guard_missing guard_match guard_wrong_label guard_wrong_first_register guard_wrong_second_register guard_recursive_stub guard_return_nonzero guard_wrong_constructor guard_reversed_sequence \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_store_const_sem_probeScript.sml stacksem_store_const_sem_probe.out \
  guard_duplicate non_word_operand copy_words_none success_use_alloc_true success_use_alloc_false \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_store_consts_probeScript.sml stacksem_store_consts_probe.out \
  store_disabled stub_alloc_disabled guard_failure success_stub_none_use_alloc_true success_stub_none_use_alloc_false success_stub_match_use_alloc_true \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_evaluate_alloc_probeScript.sml stacksem_evaluate_alloc_probe.out \
  evaluate_alloc_disabled evaluate_alloc_missing evaluate_alloc_location evaluate_alloc_word_success evaluate_alloc_gc_failure evaluate_alloc_gc_missing_size evaluate_alloc_gc_bad_space evaluate_alloc_gc_exhausted \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_integer_inst_probeScript.sml stacksem_integer_inst_probe.out \
  skip const or_loc or_missing or_loc_general add shift div div_zero carry carry_alias add_overflow sub_overflow long_mul long_div long_div_overflow load load8 load16 load32 store_loc store8 store16 store32 store8_loc load32_64 store32_64 load32_64_be store32_64_be store8_64_offset store8_64_offset_be load8_no_domain store32_no_domain \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_pattern_copy_probeScript.sml stacksem_pattern_copy_probe.out \
  zero one_bypass even odd multi missing_bitmap missing_domain later_domain address_wrap value_wrap stride16 stride4 \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_copy_words_probeScript.sml stacksem_copy_words_probe.out \
  normal_continue stops_early zero_pattern out_of_range \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_register_transfers_probeScript.sml stacksem_register_transfers_probe.out \
  get_word get_loc get_missing get_disabled set_word set_loc set_missing set_disabled op_add op_sub op_loc op_missing op_disabled \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_leaf_transfers_probeScript.sml stacksem_leaf_transfers_probe.out \
  skip halt_word halt_loc halt_missing tick_zero tick_one return_loc return_word return_missing raise_loc raise_word raise_missing break_zero break_three continue_zero continue_three \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_loop_control_probeScript.sml stacksem_loop_control_probe.out \
  reg_word reg_loc reg_missing immediate cont_none cont_continue_zero cont_continue_three cont_break_zero cont_break_one cont_break_three cont_result cont_exception cont_halt cont_timeout cont_error cont_final exit_none exit_continue_zero exit_continue_three exit_break_zero exit_break_one exit_break_three exit_result exit_exception exit_halt exit_timeout exit_error exit_final \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_control_probeScript.sml stacksem_control_probe.out \
  seq_normal seq_fallthrough seq_tick_clamp if_true if_false if_cmp_none if_operand_missing loop_recurse loop_timeout loop_exit_break loop_exit_continue \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_jumplower_probeScript.sml stacksem_jumplower_probe.out \
  jump_lower_success jump_lower_timeout jump_lower_code_missing \
  jump_lower_comparison_false jump_lower_loc_operand jump_lower_break_sub \
  jump_lower_continue_sub jump_lower_none_sub \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_rawcall_probeScript.sml stacksem_rawcall_probe.out \
  raw_call_success raw_call_timeout raw_call_code_missing raw_call_non_seq \
  raw_call_break_sub raw_call_continue_sub raw_call_none_sub \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_call_probeScript.sml stacksem_call_probe.out \
  call_tail_success call_tail_handler_error call_tail_code_missing call_tail_timeout \
  call_return_success call_return_success_handler call_return_wrong_loc \
  call_return_code_missing call_return_timeout call_exception_handled \
  call_exception_unhandled call_exception_wrong_loc call_return_break call_return_continue \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_call_indirect_probeScript.sml stacksem_call_indirect_probe.out \
  indirect_tail indirect_return indirect_link_alias indirect_tail_alias indirect_nonzero \
  indirect_word indirect_missing indirect_code_missing indirect_timeout indirect_wrong_return \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_loop_recursive_probeScript.sml stacksem_loop_recursive_probe.out \
  continue_three skip_three tick_three tick_zero break_zero break_two continue_two \
  return_location return_word_error raise_location halt_word \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_buffer_write_probeScript.sml stacksem_buffer_write_probe.out \
  code_write_success code_write_mismatch data_write_success data_write_mismatch data_write_disabled \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_sh_mem_probeScript.sml stacksem_sh_mem_probe.out \
  store load store8 load8 store16 load16 store32 load32 load_outside store8_outside load_word_unaligned store_word_unaligned load_final store_final store_loc \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_sh_mem_op_probeScript.sml stacksem_sh_mem_op_probe.out \
  sh_mem_op_success sh_mem_op_word_exp_none sh_mem_op_missing_register sh_mem_op_timeout \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_ffi_probeScript.sml stacksem_ffi_probe.out \
  ffi_return ffi_final ffi_read_failure ffi_non_word_length \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_install_probeScript.sml stacksem_install_probe.out \
  install_success install_bytes_mismatch install_progs_empty install_compile_none \
  install_use_stack_false install_non_word_operand \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_expression_probeScript.sml stacksem_expression_probe.out \
  const var_word var_loc var_missing lookup_word lookup_loc lookup_missing load_word load_loc load_oob load_bad_address op_empty_and op_add_wrap op_sub_bad_arity op_bad_operand shift_valid shift_oob shift_bad_right assign_success assign_failure \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_allocation_probeScript.sml stacksem_allocation_probe.out \
  space_true space_false space_wrap space_loc space_missing space_next_loc \
  gc_short gc_bad_stack gc_none gc_decode_fail gc_success space_mixed type_space alloc_success alloc_halt alloc_gc_failure alloc_missing alloc_bad_amount alloc_bad_space \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_stack_codec_probeScript.sml stacksem_stack_codec_probe.out \
  full_zero full_one full_two full_oob full_loc enc_empty enc_zero enc_zero_extra enc_loc enc_true enc_false enc_two enc_short enc_missing_sentinel enc_bad_continuation dec_empty dec_zero dec_true dec_false dec_short_roots dec_extra_roots dec_two dec_zero_extra full_mixed enc_mixed dec_mixed type_full type_enc type_dec \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

run_probe stacksem_word_bitmap_probeScript.sml stacksem_word_bitmap_probe.out \
  length_zero length_one length_high bitmap_empty bitmap_zero bitmap_one bitmap_order \
  bitmap_trailing bitmap_missing_continuation bitmap_continuation bitmap_width_one \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

run_probe stacksem_labels_probeScript.sml stacksem_labels_probe.out \
  locvalue_label seq_left seq_right if_right loop_body call_return_direct \
  call_return_nested call_handler_direct call_handler_nested call_empty \
  call_handler_without_return halt_empty \
  loccheck_zero_present loccheck_zero_absent loccheck_label_present loccheck_label_absent \
  loccheck_label_witness \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# Run from the local HOL object directory when Holmake has populated it, so
# HOL's ordinary theory loader finds compiled CakeML theories. Fall back to
# the source directory for checkouts whose Holmake places objects there.
run_probe word_alloc_pair_keys_probeScript.sml word_alloc_pair_keys_probe.out \
  heterogeneous collision empty "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_sem_cut_names_type_probeScript.sml word_sem_cut_names_type_probe.out \
  cut_names_type cut_envs_type cut_env_type "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"
run_probe word_alloc_remove_dead_inst_probeScript.sml word_alloc_remove_dead_inst_probe.out \
  skip const_dead const_live load16 store16 store32 load8 carry_live carry_dead longmul_live to32 to64 "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_live_inst_probeScript.sml word_alloc_live_inst_probe.out \
  load16 load8 store32 carry overflow to64 to32 from64 from32 "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_live_exp_probeScript.sml word_alloc_live_exp_probe.out \
  nested duplicate empty shift constant lookup \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_colour_inst_probeScript.sml word_alloc_colour_inst_probe.out \
  load16 store16 load8 store32 carry fp_move "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_colour_exp_probeScript.sml word_alloc_colour_exp_probe.out \
  nested duplicate empty "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_reads_exp_probeScript.sml word_alloc_reads_exp_probe.out \
  var_single load_var op_nested shift_order const_empty lookup_empty mixed_nested \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_add_carry_probeScript.sml word_add_carry_probe.out \
  ordinary carry_overflow "$cake_dir/compiler/backend/backend_commonScript.sml" \
  "$cake_dir/compiler/backend"
run_probe backend_common_word_shift_probeScript.sml backend_common_word_shift_probe.out \
  ws1 ws4 ws8 ws16 ws32 ws64 ws128 \
  "$cake_dir/compiler/backend/backend_commonScript.sml" \
  "$cake_dir/compiler/backend"
run_probe riscv_word_extract_6_probeScript.sml riscv_word_extract_6_probe.out \
  word_extract_6_zero word_extract_6_63 word_extract_6_64_premise \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"
run_probe riscv_encode_length_probeScript.sml riscv_encode_length_probe.out \
  riscv_encode_length_addi riscv_encode_length_add riscv_encode_length_branch \
  riscv_encode_bytes_addi riscv_encode_bytes_add riscv_encode_bytes_beq \
  riscv_encode_bytes_ld \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"
run_probe pan_crep_primop_probeScript.sml pan_crep_primop_probe.out \
  pan_valid crep_primop_done "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_structs_opt_mmap_probeScript.sml pan_structs_opt_mmap_probe.out \
  success pointwise "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_compile_correct_probeScript.sml pan_structs_compile_correct_probe.out \
  convert_named_record compile_correct_skip_source compile_correct_skip_converted \
  convert_s_finite_maps \
  compile_correct_tick_zero_source compile_correct_tick_zero_converted \
  compile_correct_tick_positive_source compile_correct_tick_positive_converted \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_res_convert_probeScript.sml pan_structs_res_convert_probe.out \
  convert_res_break convert_res_return_val convert_res_exception convert_res_none \
  convert_res_error convert_res_timeout convert_res_continue convert_res_final_ffi \
  is_cont_res_none is_cont_res_break is_cont_res_continue is_cont_res_error \
  is_cont_res_timeout is_cont_res_return res_vs_return res_vs_exception \
  res_vs_break res_vs_none res_vs_continue \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_compile_exp_correct_probeScript.sml pan_structs_compile_exp_correct_probe.out \
  compile_exp_correct_local_var compile_exp_correct_global_var compile_exp_correct_const \
  compile_exp_correct_mmap_nonempty compile_exp_correct_rstruct \
  compile_exp_correct_rstruct_eval \
  compile_exp_correct_nstruct compile_exp_correct_nfield \
  compile_exp_correct_rfield compile_exp_correct_op compile_exp_correct_load \
  compile_exp_correct_load_out_of_domain \
  compile_exp_correct_load_nested_named \
  compile_exp_correct_load32_le_success \
  compile_exp_correct_load_byte_out_of_domain \
  compile_exp_correct_panop_mul \
  compile_exp_correct_cmp_equal \
  size_of_compile_shape_comb \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"

run_probe semantics_props_implements_probeScript.sml semantics_props_implements_probe.out \
  implements_prime_trans \
  "$cake_dir/semantics/proofs/semanticsPropsScript.sml" \
  "$cake_dir/semantics/proofs"
run_probe pan_structs_mem_load_conversion_probeScript.sml pan_structs_mem_load_conversion_probe.out \
  mem_load_conversion_one mem_load_conversion_comb_multiword \
  mem_load_conversion_named_nested_struct_infos_ok \
  mem_load_conversion_named_nested \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_shape_context_drop_probeScript.sml pan_structs_shape_context_drop_probe.out \
  size_sh_with_ctxt_drop_one size_sh_with_ctxt_drop_named \
  size_sh_with_ctxt_drop_nested_comb \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_value_validity_probeScript.sml pan_structs_value_validity_probe.out \
  v_flds_ok_word v_flds_ok_named_match v_flds_ok_named_mismatch \
  v_flds_ok_named_missing v_flds_ok_duplicate_first \
  is_wf_shape_v_word is_wf_shape_v_named_match \
  is_wf_shape_v_named_missing v_flds_ok_append_nonempty_prefix_named \
  value_validity_done \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_map_probeScript.sml pan_structs_afindi_map_probe.out \
  hit_preserves_key_index missing_key_stays_missing \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_length_probeScript.sml pan_structs_afindi_length_probe.out \
  first_match_strictly_below_length last_match_strictly_below_length \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_el_probeScript.sml pan_structs_afindi_el_probe.out \
  first_match_fst middle_match_fst last_match_fst \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_alookup_afindi_probeScript.sml pan_structs_alookup_afindi_probe.out \
  present_lookup_projection missing_lookup_projection duplicate_key_first_value \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_append_probeScript.sml pan_structs_afindi_append_probe.out \
  prefix_hit_keeps_first_index suffix_hit_adds_prefix_length missing_key_stays_none \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_dropwhile_afindi_probeScript.sml pan_structs_dropwhile_afindi_probe.out \
  first_hit_drop later_hit_drop missing_hit_drop \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_to_word_probeScript.sml loop_to_word_probe.out \
  find_var_empty find_reg_imm_ctxt "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_defs_probeScript.sml loop_to_word_defs_probe.out \
  lt_find_var_hit lt_find_var_miss lt_find_reg_imm_imm lt_find_reg_imm_reg \
  lt_to_num_set_lookup0 lt_to_num_set_lookup2 lt_to_num_set_lookup3 \
  lt_from_num_set lt_mk_new_cutset_lookup0 lt_mk_new_cutset_lookup5 \
  lt_mk_new_cutset_absent "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_locals_rel_probeScript.sml loop_to_word_locals_rel_probe.out \
  lt_locals_rel_good_with_extra_target lt_locals_rel_odd_register \
  lt_locals_rel_zero_register lt_locals_rel_noninjective \
  lt_locals_rel_missing_context lt_locals_rel_wrong_value \
  lt_locals_rel_insert_mapped lt_locals_rel_insert_unmapped \
  lt_locals_rel_insert_unmapped_collision locals_rel_get_var_statement \
  locals_rel_get_vars_statement loop_get_vars_hit loop_get_vars_miss \
  word_get_vars_hit word_get_vars_miss \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" \
  "$cake_dir/pancake/proofs"
# The compile_correct case probe rebuilds HOL's specialised evaluate_ind for
# loop_to_word compile_correct and prints each ported case conjunct, together
# with the rebound wordSem evaluate_ind/evaluate_def (beads
# flapjack-pxn.18.5.9.21/.24, flapjack-h29l.9.2).
run_probe loop_to_word_compile_correct_cases_probeScript.sml \
  loop_to_word_compile_correct_cases_probe.out \
  cc_ind_thm_conclusion_is_compile_correct cc_case_Skip cc_case_Fail cc_case_Mark cc_case_Seq \
  cc_case_Break cc_case_Continue cc_case_Raise cc_case_Return cc_case_Tick \
  ws_evaluate_ind ws_evaluate_def ws_end \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_to_word_comp_exp_probeScript.sml loop_to_word_comp_exp_probe.out \
  comp_exp_const comp_exp_var comp_exp_var_miss comp_exp_lookup \
  comp_exp_base_addr comp_exp_top_addr comp_exp_load comp_exp_shift \
  comp_exp_op "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_comp_probeScript.sml loop_to_word_comp_probe.out \
  comp_skip comp_assign comp_addcarry_valid comp_addcarry_bad_dest_arity \
  comp_addcarry_bad_argument_arity comp_longmul comp_longdiv comp_div \
  comp_store comp_setglobal comp_load32 comp_loadbyte comp_store32 comp_storebyte \
  comp_break comp_continue comp_raise comp_return comp_tick comp_fail \
  comp_locValue comp_ffi comp_shMem \
  "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_comp_recursive_probeScript.sml loop_to_word_comp_recursive_probe.out \
  comp_seq comp_if comp_loop comp_mark \
  "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_globals_rel_probeScript.sml loop_to_word_globals_rel_probe.out \
  globals_rel_match globals_rel_value_mismatch globals_rel_temp_mismatch globals_rel_empty_source \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_to_word_comp_call_probeScript.sml loop_to_word_comp_call_probe.out \
  comp_call_tail comp_call_no_handler comp_call_handler \
  "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_comp_func_probeScript.sml loop_to_word_comp_func_probe.out \
  comp_func_skip comp_func_param_assign comp_func_new_temp \
  compile_prog_code compile_code \
  "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe loop_to_word_take_word_to_bytes_probeScript.sml \
  loop_to_word_take_word_to_bytes_probe.out \
  take1_statement twb32_0 twb32_1 twb32_hi gb32_0 gb32_1 gb32_hi \
  twb64_0 twb64_1 twb64_hi gb64_0 gb64_1 gb64_hi \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_to_word_acc_vars_acc_prime_probeScript.sml \
  loop_to_word_acc_vars_acc_prime_probe.out \
  assign_lhs_key assign_q_key assign_absent_key \
  seq_p_first seq_p_second seq_q_key \
  if_then_key if_else_key if_absent_key \
  loop_p_key loop_q_key \
  call_return_first call_return_second call_q_key \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" \
  "$cake_dir/pancake/proofs"
# The get_stack_only probe observes the allocator driver's stack-only
# analysis over wordLang programs (backend word_alloc).
run_probe get_stack_only_probeScript.sml get_stack_only_probe.out \
  skip assign_leaf "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe pan_mem_load_probeScript.sml pan_mem_load_probe.out \
  one_hit recursive_mem_loads_two_words recursive_comb_two_words \
  recursive_named_two_fields "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_state_eval_probeScript.sml pan_sem_state_eval_probe.out \
  word_load_hit eval_nested_load_shape pan_sem_state_eval_done \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_mem_domain_probeScript.sml pan_sem_mem_domain_probe.out \
  domain_load_hit domain_load_miss_present domain_store_then_load_hit \
  domain_store_miss domain_mem_stores_load_roundtrip pan_sem_mem_domain_done \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_shape_of_probeScript.sml pan_shape_of_probe.out \
  word nstruct "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_evaluate_decls_probeScript.sml pan_evaluate_decls_probe.out \
  empty exn_bad_shape_failure "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_clock_program_route_probeScript.sml pan_clock_program_route_probe.out \
  duplicate_function_front_update duplicate_function_front_update_changed_metadata \
  nested_callee_return_shape_rejected \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_word_helpers_probeScript.sml pan_word_helpers_probe.out \
  is_word the_val_word "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_op_probeScript.sml pan_op_probe.out \
  mul_two mul_three "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fixed_load_probeScript.sml pan_fixed_load_probe.out \
  mem_load_byte_definition load32_width24_address4 \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_fixed_store_probeScript.sml pan_fixed_store_probe.out \
  byte_store_hit store32_unaligned "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_store32_endian_probeScript.sml pan_store32_endian_probe.out \
  store32_le_low store32_le_high store32_be_low store32_be_high store32_be_w2w \
  store32_be_unaligned store32_be_outside "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sh_mem_store_bytes_probeScript.sml pan_sh_mem_store_bytes_probe.out \
  store_w_payload store_8_payload store_16_payload store_32_payload \
  store_16_result store_16_miss store_16_final_unchanged \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_word_boundary_probeScript.sml crep_runtime_word_boundary_probe.out \
  bytes64 store32_outside "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_ffi_boundary_probeScript.sml crep_runtime_ffi_boundary_probe.out \
  bytes64 set_byte_0_roundtrip "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_shared_domain_probeScript.sml crep_runtime_shared_domain_probe.out \
  valid_zero_mem align_16 "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_arith_dest_const_probeScript.sml crep_arith_dest_const_probe.out \
  constant dimindex_pos "$cake_dir/pancake/crep_arithScript.sml"
run_probe crep_state_mapc_probeScript.sml crep_state_mapc_probe.out \
  fmap_map2_keyed_lookup \
  "$hol_dir/src/finite_maps/finite_mapScript.sml" \
  "$hol_dir/src/finite_maps"
run_probe crep_arith_lookup_code_probeScript.sml crep_arith_lookup_code_probe.out \
  simp_prog_after_lookup \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_arith_eval_mul_const_probeScript.sml crep_arith_eval_mul_const_probe.out \
  input_word multiply_general "$cake_dir/pancake/proofs/crep_arithProofScript.sml"
run_probe crep_exps_of_probeScript.sml crep_exps_of_probe.out \
  dec_seq if_store while call_tail call_ret call_ret_hdl stores empty \
  "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_read_bytes_probeScript.sml crep_runtime_read_bytes_probe.out \
  read_bytes_zero read_bytes_out_of_domain "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_write_bytes_probeScript.sml crep_runtime_write_bytes_probe.out \
  write_head write_fallback_discards_tail "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_ext_call_probeScript.sml crep_runtime_ext_call_probe.out \
  empty_name_identity oracle_diverged "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_shared_mem_probeScript.sml crep_runtime_shared_mem_probe.out \
  load_returned store_final "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_every_exp_probeScript.sml crep_every_exp_probe.out \
  const_hit always_op_nested "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_assigned_vars_probeScript.sml crep_assigned_vars_probe.out \
  afv_prog nested_afv "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_dec_clock_simp_probeScript.sml crep_dec_clock_simp_probe.out \
  dec_clock_clock empty_locals_memory "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_to_loop_state_rel_probeScript.sml crep_to_loop_state_rel_probe.out \
  memaddrs_mdomain_mem clock_mismatch "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_ctxt_fc_probeScript.sml crep_to_loop_ctxt_fc_probe.out \
  vars_zip done "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_globals_rel_probeScript.sml crep_to_loop_globals_rel_probe.out \
  wlab_wloc_word globals_lookup_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_primop_loop_primop_probeScript.sml crep_primop_loop_primop_probe.out \
  crep_valid loop_valid_mapped preserve_valid crep_overflow loop_overflow_mapped \
  preserve_overflow crep_nonzero_carry loop_nonzero_carry_mapped \
  preserve_nonzero_carry crep_invalid_two preserve_invalid_two crep_invalid_four \
  preserve_invalid_four "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_mem_rel_probeScript.sml crep_to_loop_mem_rel_probe.out \
  mem_rel_match mem_rel_dom_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_distinct_funcs_probeScript.sml crep_to_loop_distinct_funcs_probe.out \
  distinct_funcs_sep distinct_funcs_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_distinct_vars_probeScript.sml crep_to_loop_distinct_vars_probe.out \
  distinct_vars_sep distinct_vars_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_ctxt_max_probeScript.sml crep_to_loop_ctxt_max_probe.out \
  ctxt_max_within ctxt_max_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_locals_rel_probeScript.sml crep_to_loop_locals_rel_probe.out \
  ctxt_vars_lookup ctxt_max_component set_domain_mem map_lookup \
  subset_domain_component cutset_set_lookup cutset_target_lookup \
  locals_rel_true locals_rel_domain_false \
  locals_rel_value_false locals_rel_cutset_second_true \
  locals_rel_cutset_after_true locals_rel_insert_after_true \
  insert_gt_vmax_lookup_unchanged \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_locals_insert_probeScript.sml crep_to_loop_locals_insert_probe.out \
  insert_same subset_preserved \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_locals_cutset_probeScript.sml crep_to_loop_locals_cutset_probe.out \
  cutset_sub_0 cutset_domain_trans \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_mem_lookup_probeScript.sml crep_to_loop_mem_lookup_probe.out \
  ml_hit ml_distinct \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_list_insert_probeScript.sml crep_to_loop_list_insert_probe.out \
  li_mem_3 li_snoc_agrees \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_insert_insert_probeScript.sml crep_to_loop_insert_insert_probe.out \
  iie_hit iie_agrees_deep \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_list_insert2_probeScript.sml crep_to_loop_list_insert2_probe.out \
  lii_ty_nonmember lia_absent \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_assigned_vars_mapidx_probeScript.sml crep_to_loop_assigned_vars_mapidx_probe.out \
  avma_nil avma_offset_zero \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_survives_mapi_assign_probeScript.sml \
  crep_to_loop_survives_mapi_assign_probe.out \
  survives_mapi_assign_nil survives_mapi_assign_one \
  survives_mapi_assign_three survives_mapi_assign_zero_offset \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_props_assigned_vars_probeScript.sml loop_props_assigned_vars_probe.out \
  avs_seq_split avs_nested_assign_three \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe loop_props_cut_sets_probeScript.sml loop_props_cut_sets_probe.out \
  cut_sets_skip cut_sets_locvalue cut_sets_assign cut_sets_load32 \
  cut_sets_loadbyte cut_sets_seq cut_sets_if cut_sets_longdiv \
  cut_sets_longmul cut_sets_div cut_sets_catch_all \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_to_loop_context_defs_probeScript.sml crep_to_loop_context_defs_probe.out \
  find_var_hit find_lab_miss "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_mk_ctxt_probeScript.sml crep_to_loop_mk_ctxt_probe.out \
  mk_ctxt_vars make_vmap_empty_miss "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_make_vmap_dup_probeScript.sml crep_to_loop_make_vmap_dup_probe.out \
  mvd_single_hit mvd_dup_last_wins "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_rt_vars_distinct_probeScript.sml crep_to_loop_rt_vars_distinct_probe.out \
  acd_distinct acd_missing "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_map_map2_fst_probeScript.sml crep_to_loop_map_map2_fst_probe.out \
  mm2_pair_eq mm2_empty "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_alookup_el_probeScript.sml crep_to_loop_alookup_el_probe.out \
  ael_shape_0 ael_result "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_make_funcs_probeScript.sml crep_to_loop_make_funcs_probe.out \
  mkf_f mkf_dup_first "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_helpers_probeScript.sml crep_to_loop_helpers_probe.out \
  gen_temps_3 rt_vars_absent "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake"
run_probe fm_empty_zip_alist_probeScript.sml fm_empty_zip_alist_probe.out \
  fold_flookup_eq zip_lookup_witness "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_common_props_no_overlap_probeScript.sml pan_common_props_no_overlap_probe.out \
  slot_nodup_x nested_zip_lookup "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_common_distinct_lists_probeScript.sml pan_common_distinct_lists_probe.out \
  distinct_true distinct_eq_disjoint genlist_vmax_bound genlist_vmax_hit \
  genlist_vmax_disjoint "$cake_dir/pancake/pan_commonScript.sml" \
  "$cake_dir/pancake"
run_probe word_to_stack_bits_to_word_probeScript.sml word_to_stack_bits_to_word_probe.out \
  bits_empty wordlist_chunk "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_word_list_probeScript.sml word_to_stack_word_list_probe.out \
  wl_empty_d3 wl_twostep "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_chunk_to_bits_probeScript.sml word_to_stack_chunk_to_bits_probe.out \
  cb_empty cb_ignores_word "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_chunk_to_bitmap_probeScript.sml word_to_stack_chunk_to_bitmap_probe.out \
  cbm_empty cwb_split8 "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_write_bitmap_probeScript.sml word_to_stack_write_bitmap_probe.out \
  wb_empty wb_single wb_two wb_offset wb_boundary wb_order_a wb_order_b wb_order_eq wb_payload_nat wb_payload_bool "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_insert_bitmap_probeScript.sml word_to_stack_insert_bitmap_probe.out \
  ib_empty ib_new_len "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_stack_slots_probeScript.sml word_to_stack_stack_slots_probe.out \
  ss_num_stack_ret_pair ss_stack_free_inl "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_perf_slots_probeScript.sml word_to_stack_perf_slots_probe.out \
  ps_perf_rsp ps_handler_slots_false "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_reg_format_probeScript.sml word_to_stack_reg_format_probe.out \
  rf_reg1_high wma_two "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe stack_lang_prog_combinators_probeScript.sml stack_lang_prog_combinators_probe.out \
  lc_empty wss_two "$cake_dir/compiler/backend/stackLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe stack_lang_store_name_probeScript.sml stack_lang_store_name_probe.out \
  sn_count sn_temp_word_bits "$cake_dir/compiler/backend/stackLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe asm_inst_fragment_probeScript.sml asm_inst_fragment_probe.out \
  ar_reg as_loc "$cake_dir/compiler/encoders/asm/asmScript.sml" \
  "$cake_dir/compiler/encoders/asm"
run_probe pan_props_alist_probeScript.sml pan_props_alist_probe.out \
  alist_a_nodup alist_duplicate_first "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_props_alist_ctxt_max_probeScript.sml pan_props_alist_ctxt_max_probe.out \
  ctxt_a_bound ctxt_duplicate_first_bound "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_props_list_rel_probeScript.sml pan_props_list_rel_probe.out \
  len0 flookup0 "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_inline_code_inl_probeScript.sml crep_inline_code_inl_probe.out \
  flookup_f skip_identity "$cake_dir/pancake/crep_inlineScript.sml" \
  "$cake_dir/pancake"
run_probe crep_inline_alist_map_probeScript.sml crep_inline_alist_map_probe.out \
  alist_duplicate_first input_rows_order "$cake_dir/pancake/crep_inlineScript.sml" \
  "$cake_dir/pancake"
run_probe crep_inline_helper_probeScript.sml crep_inline_helper_probe.out \
  var_prog_call_handler_extcall unreach_p \
  "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_structural_probeScript.sml crep_inline_structural_probe.out \
  inline_prog_empty_dec inline_prog_empty_while \
  "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_transform_eoc_probeScript.sml crep_inline_transform_eoc_probe.out \
  transform_eoc_return_zip transform_eoc_call_none transform_eoc_call_returns \
  transform_eoc_call_handler transform_eoc_call_handler_value \
  transform_eoc_dec transform_eoc_while transform_eoc_seq transform_eoc_if \
  transform_eoc_default \
  "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_transform_branch_probeScript.sml crep_inline_transform_branch_probe.out \
  transform_branch_return transform_branch_call_none transform_branch_call_returns \
  transform_branch_call_handler transform_branch_dec transform_branch_while \
  transform_branch_seq transform_branch_if transform_branch_default \
  "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_nontail_probeScript.sml crep_inline_nontail_probe.out \
  inline_nontail_scalar inline_nontail_map2_truncates \
  inline_nontail_arg_shape_mismatch \
  "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_has_return_probeScript.sml crep_inline_has_return_probe.out \
  has_return_return has_return_call_none has_return_call_dest \
  has_return_call_handler has_return_dec has_return_seq has_return_if \
  has_return_while has_return_default \
  "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_cont_res_probeScript.sml crep_inline_cont_res_probe.out \
  cont_res_none cont_res_done "$cake_dir/pancake/proofs/crep_inlineProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_inline_eval_probeScript.sml crep_inline_eval_probe.out \
  src_main_is_call continue_eval "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_inline_relations_probeScript.sml crep_inline_relations_probe.out \
  locals_rel_extension state_rel_dec_clock \
  "$cake_dir/pancake/proofs/crep_inlineProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_flat_store_probeScript.sml pan_flat_store_probe.out \
  store_hit stores_blocked "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_flatten_probeScript.sml pan_flatten_probe.out \
  word named "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_lang_nested_seq_probeScript.sml pan_lang_nested_seq_probe.out \
  empty assign_seq "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_exp_ids_probeScript.sml pan_lang_exp_ids_probe.out \
  empty fallback "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_with_shape_probeScript.sml pan_lang_with_shape_probe.out \
  empty_shapes short_input "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_wf_fields_context_probeScript.sml pan_lang_wf_fields_context_probe.out \
  empty_fields self_reference_context "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_wf_shape_probeScript.sml pan_lang_wf_shape_probe.out \
  one nested_unknown "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_size_of_sh_with_ctxt_probeScript.sml pan_lang_size_of_sh_with_ctxt_probe.out \
  one known_named missing_named nested_comb nested_named_size_drop \
  "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_size_of_shape_probeScript.sml pan_lang_size_of_shape_probe.out \
  one empty_comb named nested_comb "$cake_dir/pancake/panLangScript.sml"
# The size probe observes the HOL-generated shape_size/exp_size equations from
# the real panLangTheory (not a local datatype replica), plus concrete EVAL rows.
run_probe pan_lang_size_probeScript.sml pan_lang_size_probe.out \
  mlstring_size_def shape_size_def exp_size_def MEM_IMP_shape_size \
  MEM_IMP_exp_size exp_size_base \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"
run_probe crep_inline_prog_size_type_probeScript.sml crep_inline_prog_size_type_probe.out \
  prog_size_type exp_size_type unreach_elim_prog_size_typed \
  "$cake_dir/pancake/proofs/crep_inlineProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_lang_size_probeScript.sml crep_lang_size_probe.out \
  exp_size_def prog_size_def prog_size_seq prog_size_call prog_size_dec prog_size_ext prog_size_raise \
  "$cake_dir/pancake/crepLangScript.sml" \
  "$cake_dir/pancake"
run_probe pan_lang_decl_predicates_probeScript.sml pan_lang_decl_predicates_probe.out \
  is_decl_decl is_decl_exception is_exn_decl_exception is_exn_decl_decl \
  is_name_name is_name_decl size_of_eids_empty size_of_eids_mixed \
  "$cake_dir/pancake/panLangScript.sml"
run_probe compile_shape_probeScript.sml compile_shape_probe.out \
  one compile_shapes_map compiled_shape_wf compiled_shapes_wf \
  "$cake_dir/pancake/pan_structsScript.sml"
run_probe pan_lang_var_exp_probeScript.sml pan_lang_var_exp_probe.out \
  local_var global_var nested nested_global \
  global_var_exp_def global_var_exp_def_primitive \
  "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_load_store_op_probeScript.sml pan_lang_load_store_op_probe.out \
  load_op8 load_op16 load_opw load_op32 store_op8 store_op16 store_opw store_op32 \
  "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_is_function_probeScript.sml pan_lang_is_function_probe.out \
  function global "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_functions_probeScript.sml pan_lang_functions_probe.out \
  empty function global "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_exceptions_probeScript.sml pan_lang_exceptions_probe.out \
  empty exception "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_fun_ids_probeScript.sml pan_lang_fun_ids_probe.out \
  empty call handler dec_call "$cake_dir/pancake/panLangScript.sml"
run_probe word_to_stack_retained_frame_probeScript.sml word_to_stack_retained_frame_probe.out \
  retained_frame_empty retained_frame_register_edge retained_frame_first_spill \
  retained_frame_second_spill retained_frame_args_dominate retained_frame_equal_demand \
  retained_frame_zero_registers retained_frame_large_name \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_allocator_stages_probeScript.sml word_to_stack_allocator_stages_probe.out \
  allocator_stages_skip allocator_stages_tick allocator_stages_raise allocator_stages_tail_call \
  "$cake_dir/compiler/backend/word_to_wordScript.sml" "$cake_dir/compiler/backend"
run_probe word_simp_duplicate_if_source_probeScript.sml word_simp_duplicate_if_source_probe.out \
  duplicate_roundtrip duplicate_must duplicate_loop duplicate_call_return duplicate_call_handler \
  duplicate_call_both duplicate_if duplicate_no_hoist duplicate_zero_bound duplicate_non_simple \
  duplicate_move_simple duplicate_raise_other duplicate_raise_zero duplicate_raise_three \
  "$cake_dir/compiler/backend/word_simpScript.sml" "$cake_dir/compiler/backend"
run_probe word_simp_seq_assoc_source_probeScript.sml word_simp_seq_assoc_source_probe.out \
  assoc_skip assoc_prefix_skip assoc_trailing_skip assoc_interior_skip assoc_all_skip \
  assoc_middle_skip assoc_right_spine assoc_if assoc_loop assoc_must assoc_tail_handler \
  assoc_return assoc_both assoc_prefix_unchanged assoc_inst assoc_pre_ssa \
  "$cake_dir/compiler/backend/word_simpScript.sml" "$cake_dir/compiler/backend"
run_probe word_simp_constant_domain_probeScript.sml word_simp_constant_domain_probe.out \
  constant_program_skip constant_program_assign constant_program_selected constant_program_unknown \
  constant_program_tail constant_program_return constant_program_both constant_program_alloc \
  constant_program_install constant_program_ffi constant_program_loop constant_program_must constant_program_trailing_skip \
  "$cake_dir/compiler/backend/word_simpScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_selector_domain_probeScript.sml word_to_stack_selector_domain_probe.out \
  selector_program_skip selector_program_seq selector_program_set selector_program_load \
  selector_program_store selector_program_store_offset selector_program_share selector_program_if \
  selector_program_loop selector_program_must selector_program_tail_handler selector_program_return selector_program_both \
  "$cake_dir/compiler/backend/word_instScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_selector_prelude_probeScript.sml word_to_stack_selector_prelude_probe.out \
  selector_prelude_const selector_prelude_var selector_prelude_lookup selector_prelude_load \
  selector_prelude_add selector_prelude_shift selector_prelude_shift_oob selector_prelude_heap \
  selector_prelude_load_offset selector_prelude_load_large_offset \
  "$cake_dir/compiler/backend/word_instScript.sml" "$cake_dir/compiler/backend"
run_probe word_stack_frame_probeScript.sml word_stack_frame_probe.out \
  maxvar_skip limit_seq later_pair_f later_pair_alloc later_pair_slot_44 \
  later_pair_slot_46 later_pair_bounded \
  "$cake_dir/compiler/backend/word_to_stackScript.sml"
run_probe word_stack_max_var_probeScript.sml word_stack_max_var_probe.out \
  maxvar_inst_mem maxvar_return "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_cost_probeScript.sml word_alloc_cost_probe.out \
  spill_zero spill_c1 spill_lr1 spill_lm1 spill_rr1 spill_rm1 spill_all1 \
  spill_all1_tail coal_empty coal_x_in coal_y_in coal_both_in coal_pri2_both_in \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe pan_lang_free_var_ids_probeScript.sml pan_lang_free_var_ids_probe.out \
  empty global_in_handler "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_inlinable_probeScript.sml pan_lang_inlinable_probe.out \
  inline_true non_function "$cake_dir/pancake/panLangScript.sml"
run_probe get_forced_probeScript.sml get_forced_probe.out \
  add_carry nested "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
# The mk_bij probe observes the clash-tree-to-node bijection used to number
# allocator nodes (reads before writes, seq right-first, branch live sets).
run_probe mk_bij_probeScript.sml mk_bij_probe.out \
  delta_basic composite "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe reg_alloc_dec_deg_probeScript.sml reg_alloc_dec_deg_probe.out \
  dec_deg_in_bounds_result update_degrees_out_of_bounds_result \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend/reg_alloc"
run_probe stack_alloc_next_lab_probeScript.sml stack_alloc_next_lab_probe.out \
  next_lab_skip next_lab_both_continuations \
  "$cake_dir/compiler/backend/stack_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe stack_to_lab_flatten_probeScript.sml stack_to_lab_flatten_probe.out \
  flat_skip flat_tick flat_inst flat_halt flat_seq_tail flat_seq_not_tail \
  flat_if_both_skip flat_if_then_skip flat_if_else_skip \
  flat_if_then_terminates flat_if_else_terminates flat_if_both_live \
  flat_loop_if flat_raise flat_return flat_break flat_continue flat_raw_call \
  flat_call_none_label flat_call_none_reg flat_call_return flat_call_handler \
  flat_jump_lower flat_ffi flat_loc_value flat_install flat_shared_memory \
  flat_code_buffer_write flat_default section_skip section_seq section_if \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"
run_probe lab_props_preconditions_probeScript.sml lab_props_preconditions_probe.out \
  pre_label pre_labasm pre_asmi_skip pre_cbw_to_asm pre_share_to_asm \
  pre_empty_sections pre_label_section pre_skip_asm_section \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"
run_probe word_alloc_setup_colour_probeScript.sml word_alloc_setup_colour_probe.out \
  total_colour_mapped_1 setup0_next "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_live_colour_noalias_probeScript.sml \
  word_alloc_live_colour_noalias_probe.out \
  colour_ok_distinct_write_live colour_ok_alias_write_live \
  colour_ok_distinct_write_live_after colour_ok_alias_write_live_after \
  "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe apply_colour_probeScript.sml apply_colour_probe.out \
  total_colour_alloc apply_colour_alias_assign apply_colour_alias_const \
  "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
# The legacy allocator-map probe checks the existing WordBijection path too.
run_probe reg_alloc_mk_bij_probeScript.sml reg_alloc_mk_bij_probe.out \
  empty_to seq_next "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe cake_ssa_temp_probeScript.sml cake_ssa_temp_probe.out \
  limit_skip full_skip "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
# The reg_alloc probe observes the full IRC colouring (do_reg_alloc via
# reg_alloc_aux/run_ira_state) on tiny clash trees: alloc vars get colours
# 0..k-1, stack-only vars land at >= k, physical vars keep their register
# index.
run_probe reg_alloc_probeScript.sml reg_alloc_probe.out \
  ra_delta_pair moves_to_sp_resort ra_spill_cost \
  node_list_empty_length node_list_first node_list_last \
  node_list_last_in_range node_list_out_of_range \
  node_list_lupdate_same node_list_lupdate_other node_list_lupdate_length \
  node_list_lupdate_outside \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe sort_moves_probeScript.sml sort_moves_probe.out \
  sm_ties_two sm_ties_three sm_desc ra_moves_stemp ra_moves_stemp_hi \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe pan_lang_shape_val_probeScript.sml pan_lang_shape_val_probe.out \
  one named "$cake_dir/pancake/panLangScript.sml"
run_probe shape_to_str_probeScript.sml shape_to_str_probe.out \
  one named "$cake_dir/pancake/panLangScript.sml"
run_probe pan_res_var_probeScript.sml pan_res_var_probe.out \
  delete_hit update_hit "$cake_dir/pancake/semantics/panSemScript.sml"
# The pan_primop probe prints numeric w2n values of the returned RStruct.
run_probe pan_sem_pan_primop_probeScript.sml pan_sem_pan_primop_probe.out \
  pan_primop_basic pan_primop_non_word "$cake_dir/pancake/semantics/panSemScript.sml"
# The set_var probe checks local override, unrelated locals, globals, and clock.
run_probe pan_sem_set_var_probeScript.sml pan_sem_set_var_probe.out \
  set_var_new set_var_done "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_dec_clock_probeScript.sml pan_dec_clock_probe.out \
  pan_dec_clock_five pan_dec_clock_zero \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The dec_clock artifact fixture probe evaluates `tick; return 7` directly.
run_probe pan_sem_dec_clock_e2e_probeScript.sml pan_sem_dec_clock_e2e_probe.out \
  dec_clock_tick_return dec_clock_tick_return_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Tick probe observes both the zero-clock timeout and positive-clock branches.
run_probe pan_sem_tick_e2e_probeScript.sml pan_sem_tick_e2e_probe.out \
  tick_zero_result tick_succ_locals_preserved \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Skip probe observes the normal result with state carried verbatim.
run_probe pan_sem_skip_e2e_probeScript.sml pan_sem_skip_e2e_probe.out \
  skip_result skip_locals_preserved \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_break_continue_e2e_probeScript.sml pan_sem_break_continue_e2e_probe.out \
  break_result continue_locals_preserved \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Assign probe observes the accepted, fresh-destination, and
# source-evaluation-failure branches, including the unchanged post-state on the
# two Error branches.
run_probe pan_sem_assign_e2e_probeScript.sml pan_sem_assign_e2e_probe.out \
  assign_local_ok_result assign_eval_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Dec probe observes the accepted declaration with local restoration, the
# shape-mismatch rejection, and the initialiser-evaluation-failure rejection,
# including the unchanged post-state of both rejection branches.
# The Primitive-error probe observes `pan_primop` failure (wrong arity) and a
# destination shape mismatch, both yielding `SOME Error` with unchanged state.
run_probe pan_sem_primitive_error_probeScript.sml pan_sem_primitive_error_probe.out \
  prim_wrong_arity_result prim_shape_mismatch_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"

run_probe pan_sem_dec_e2e_probeScript.sml pan_sem_dec_e2e_probe.out \
  dec_ok_result dec_eval_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Primitive probe observes the accepted AddCarry update, the
# fresh-destination rejection, and the argument-evaluation-failure rejection,
# including the unchanged post-state of both rejection branches.
run_probe pan_sem_primitive_e2e_probeScript.sml pan_sem_primitive_e2e_probe.out \
  prim_ok_result prim_arg_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Error-propagation probe nests a rejected Dec inside Seq and While and
# observes that the explicit `SOME Error` result propagates.
run_probe pan_sem_error_prop_e2e_probeScript.sml pan_sem_error_prop_e2e_probe.out \
  seq_error_result while_error_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Store/ShMem/If probe observes successful execution and the explicit
# `SOME Error` results with unchanged state for the store, shared-memory, and
# condition rejection branches.
run_probe pan_sem_store_error_probeScript.sml pan_sem_store_error_probe.out \
  if_ok_result shmemstore_domain_result \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The While probe observes the explicit `SOME Error` for a non-word condition,
# the same-clock normal exit for a zero condition, clock-exhaustion timeout,
# and a one-iteration exit that clears the condition.
run_probe pan_sem_while_error_probeScript.sml pan_sem_while_error_probe.out \
  while_bad_result while_one_iter_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Seq probe observes the normal continuation, the `Break`/`Continue`
# short-circuit (second command not run), the rejected first command, and the
# `fix_clock` clamp after a `Tick`.
run_probe pan_sem_seq_e2e_probeScript.sml pan_sem_seq_e2e_probe.out \
  seq_normal_result seq_tick_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The If probe observes the then/else branches, non-word and failed conditions,
# plus Const, Var Local, and operator-expression branch selection in the
# restricted total evaluators.
run_probe pan_sem_ite_e2e_probeScript.sml pan_sem_ite_e2e_probe.out \
  if_true_result exact_if_failed_local \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The measure-driven total fragment probe observes Assign/Return/Raise result
# and state branches, plus their interaction with If selection and Seq stopping,
# including an If whose condition is the non-word value `RStruct []`.
run_probe pan_sem_total_fragment_stmt_probeScript.sml pan_sem_total_fragment_stmt_probe.out \
  total_assign_ok_result total_assign_ok_local \
  total_assign_bad_result total_assign_bad_local \
  total_return_ok_result total_return_ok_local \
  total_return_bad_result total_return_bad_local \
  total_return_oversize_result total_return_oversize_local \
  total_raise_ok_result total_raise_ok_local \
  total_raise_bad_result total_raise_bad_local \
  total_raise_shape_mismatch_result total_raise_shape_mismatch_local \
  total_raise_missing_shape_result total_raise_oversize_result \
  total_raise_oversize_local total_if_assign_true_result \
  total_if_assign_true_local total_if_assign_false_result \
  total_if_assign_false_local total_if_assign_nonword_result \
  total_if_assign_nonword_local total_seq_assign_return_result \
  total_seq_assign_return_local total_seq_raise_stop_result \
  total_seq_raise_stop_local \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The If memory probe observes a memory-reading condition: a nonzero cell
# selecting the then branch, a zero cell selecting the else branch, an address
# outside `memaddrs` rejected with Error, and the same cell selecting different
# branches under little- versus big-endian byte reads.
run_probe pan_sem_ite_memory_probeScript.sml pan_sem_ite_memory_probe.out \
  if_mem_nonzero_result if_mem_byte_be_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Assign memory probe observes a memory-reading source: a present word cell
# written to the destination local, an address outside `memaddrs` rejected with
# Error and the locals/clock unchanged, and `be` driving the byte read.
run_probe pan_sem_assign_memory_probeScript.sml pan_sem_assign_memory_probe.out \
  assign_mem_load_result assign_mem_byte_be_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The DecCall probe observes the successful continuation, the wrong-shape
# rejection, the failing-callee rejection, and the unknown-function rejection.
run_probe pan_sem_deccall_error_probeScript.sml pan_sem_deccall_error_probe.out \
  deccall_ok_result nested_deccall_bad_shape_state_exact \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The Call argument probe observes that a failing argument rejects the call
# with `SOME Error` before callee lookup, preserving clock and locals.
run_probe pan_sem_call_arg_error_probeScript.sml pan_sem_call_arg_error_probe.out \
  call_arg_fail_result call_arg_fail_missing_result \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call error-state probe observes that a memory-reading argument is gated by
# the source `memaddrs` (an address outside the domain rejects the call even
# when the raw memory function holds a cell), and that an unknown callee is
# rejected, both with `SOME Error` and the unchanged state.
run_probe pan_sem_call_error_state_probeScript.sml pan_sem_call_error_state_probe.out \
  call_error_load_result call_error_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call arity probe observes that a parameter-shape/arity mismatch rejects the
# call with `SOME Error` and the unchanged caller state, while a matching
# argument yields the callee's `Return` result.
run_probe pan_sem_call_arity_probeScript.sml pan_sem_call_arity_probe.out \
  call_arity_miss_result call_arity_shape_miss_result \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call callee-fallthrough probe observes that a callee whose body terminates
# normally (HOL `NONE`) rejects the call with `SOME Error`, preserving the
# callee's bound parameter locals and the decremented clock.
run_probe pan_sem_call_callee_normal_probeScript.sml pan_sem_call_callee_normal_probe.out \
  call_normal_result call_normal_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call callee-terminal probe observes that a callee whose body finishes with
# `Break` or `Continue` rejects the call with `SOME Error`, preserving the
# callee's bound parameter locals and the decremented clock.
run_probe pan_sem_call_callee_terminal_probeScript.sml pan_sem_call_callee_terminal_probe.out \
  call_break_result call_continue_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call callee-error probe observes that a callee whose body finishes with
# `SOME Error` propagates `SOME Error` through the catch-all `empty_locals st`,
# clearing the caller-visible locals while keeping the decremented clock.
run_probe pan_sem_call_callee_error_probeScript.sml pan_sem_call_callee_error_probe.out \
  call_error_result call_error_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call return-invalid probe observes that a callee returning a value whose
# shape does not match the declared return shape rejects the call with
# `SOME Error` at the decremented callee clock.
run_probe pan_sem_call_return_invalid_probeScript.sml pan_sem_call_return_invalid_probe.out \
  call_retinvalid_result call_retinvalid_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Return/Raise probe observes evaluation failure and shape/size rejection
# with `SOME Error` and the unchanged state, plus the successful results with
# cleared locals.
run_probe pan_sem_return_raise_error_probeScript.sml pan_sem_return_raise_error_probe.out \
  ret_eval_fail_result raise_ok_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Return/Raise memory probe observes a memory-reading payload: a domain
# miss rejected with Error and unchanged state for both `Return` and `Raise`, a
# shape mismatch rejected with unchanged state, and the successful
# memory-reading results with cleared locals.
run_probe pan_sem_return_raise_memory_probeScript.sml pan_sem_return_raise_memory_probe.out \
  ret_mem_fail_result raise_mem_ok_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The ExtCall error probe observes the argument-evaluation failure, the
# non-word argument and failing byte-read rejections, each returning
# `SOME Error` with unchanged state.
run_probe pan_sem_extcall_error_probeScript.sml pan_sem_extcall_error_probe.out \
  ext_nonword_result ext_argfail_done \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_call_terminal_probeScript.sml pan_sem_call_terminal_probe.out \
  call_terminal_skip_result call_terminal_continue_param_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fix_clock_probeScript.sml pan_fix_clock_probe.out \
  pan_fix_clock_clamps pan_fix_clock_keeps_lower \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_upd_locals_probeScript.sml pan_upd_locals_probe.out \
  pan_upd_locals_hit pan_upd_locals_empty \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_lookup_code_probeScript.sml pan_sem_lookup_code_probe.out \
  lookup_code_nonempty_success lookup_code_wf_shape_invariant_step_success \
  lookup_code_missing_function \
  lookup_code_wrong_arity lookup_code_wrong_shape lookup_code_duplicate_formals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_e2e_probeScript.sml pan_sem_e2e_probe.out \
  return_41 call_code_map_7 recursive_call_code_map_7 deccall_code_map_7 \
  recursive_call_timeout recursive_deccall_timeout pan_sem_e2e_done \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe crep_clock_leaf_eval_probeScript.sml crep_clock_leaf_eval_probe.out \
  skip_eval break_eval continue_eval tick_zero_eval tick_positive_eval \
  if_true_eval if_false_eval if_error_eval if_nested_eval \
  seq_skip_break_eval seq_break_stops_eval seq_tick_skip_eval seq_tick_zero_eval \
  seq_fix_clock_upper_clamp_eval return_word_eval return_empty_eval \
  return_missing_eval raise_eval dec_shadow_eval dec_new_local_eval dec_error_eval \
  while_false_eval while_error_eval while_timeout_eval while_normal_recursion_eval \
  while_break_zero_eval while_break_label_eval while_continue_label_eval \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_total_call_eval_probeScript.sml crep_total_call_eval_probe.out \
  call_total_return_success call_total_return_destination call_total_missing_code \
  call_total_wrong_arity call_total_timeout call_total_callee_normal \
  call_total_callee_break call_total_callee_continue call_total_callee_exception \
  call_total_return_arity_error call_total_duplicate_destinations \
  call_total_missing_destination \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_evaluate_def_arms_probeScript.sml crep_evaluate_def_arms_probe.out \
  primitive_add_carry primitive_duplicate_lhs primitive_missing_lhs \
  primitive_wrong_arity primitive_missing_rhs call_handler_catch \
  call_handler_mismatch call_handler_absent call_handler_duplicate_rts \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_assign_eval_probeScript.sml crep_assign_eval_probe.out \
  assign_overwrite_eval assign_missing_destination_eval assign_expression_error_eval \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_store_eval_probeScript.sml crep_store_eval_probe.out \
  store_success store_address_error store_value_error store_domain_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_ext_call_eval_probeScript.sml crep_ext_call_eval_probe.out \
  extcall_return_eval extcall_final_eval extcall_missing_local_eval \
  extcall_read_error_eval \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_shmem_eval_probeScript.sml crep_shmem_eval_probe.out \
  shmem_load_success shmem_store_success shmem_load8_success shmem_store8_success \
  shmem_load_domain_error \
  shmem_missing_local_error shmem_load_final \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe pan_sem_call_return_shape_probeScript.sml pan_sem_call_return_shape_probe.out \
  call_good_return_shape_result call_bad_return_shape_result call_bad_return_shape_param_local \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_e2e_add_probeScript.sml pan_sem_e2e_add_probe.out \
  return_add_6_7 return_add_6_7 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_call_e2e_probeScript.sml pan_sem_call_e2e_probe.out \
  call_id_7 call_id_7 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_global_e2e_probeScript.sml pan_sem_global_e2e_probe.out \
  global_g_7 global_g_7 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_memory_e2e_probeScript.sml pan_sem_memory_e2e_probe.out \
  memory_load_37 memory_load_37 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_ffi_e2e_probeScript.sml pan_sem_ffi_e2e_probe.out \
  ffi_foo_event ffi_foo_event "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_itree_comp_ffi_probeScript.sml pan_itree_comp_ffi_probe.out \
  ret tau return length_failure final div_ret div_tau \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe ffi_call_probeScript.sml ffi_call_probe.out \
  oracle_return extcall_name_len "$cake_dir/semantics/ffi/ffiScript.sml"
run_probe pan_itree_trace_prefix_probeScript.sml pan_itree_trace_prefix_probe.out \
  ret final "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_trace_prefix0_probeScript.sml pan_itree_trace_prefix0_probe.out \
  ret final "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_ltree_probeScript.sml pan_itree_ltree_probe.out \
  ret final "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_sh_mem_store_probeScript.sml \
  pan_itree_h_prog_sh_mem_store_probe.out \
  store_zero_width store_final_state \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_probeScript.sml pan_itree_h_prog_probe.out \
  h_prog_skip h_prog_tick "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_sh_mem_load_probeScript.sml \
  pan_itree_h_prog_sh_mem_load_probe.out \
  load_zero_width load_final_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_return_probeScript.sml pan_itree_h_prog_return_probe.out \
  return_valid_locals return_invalid "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_raise_probeScript.sml pan_itree_h_prog_raise_probe.out \
  raise_valid_locals raise_invalid "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_ext_call_probeScript.sml pan_itree_h_prog_ext_call_probe.out \
  ext_call_event ext_call_final_locals "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_store_byte_probeScript.sml \
  pan_itree_h_prog_store_byte_probe.out \
  store_byte_success store_byte_domain_error \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_store_32_probeScript.sml \
  pan_itree_h_prog_store_32_probe.out \
  store_32_success store_32_domain_error \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_primitive_probeScript.sml \
  pan_itree_h_prog_primitive_probe.out \
  primitive_success primitive_shape_error \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_set_global_probeScript.sml pan_set_global_probe.out \
  set_global_insert set_global_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_sem_set_global_probeScript.sml pan_sem_set_global_probe.out \
  set_global_insert set_global_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_set_kvar_probeScript.sml pan_sem_set_kvar_probe.out \
  set_kvar_local set_kvar_global_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_lookup_kvar_probeScript.sml pan_sem_lookup_kvar_probe.out \
  lookup_kvar_local lookup_kvar_missing \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_is_valid_value_probeScript.sml pan_sem_is_valid_value_probe.out \
  is_valid_value_local_shape is_valid_value_missing \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_write_bytearray_probeScript.sml pan_sem_write_bytearray_probe.out \
  write_empty write_miss \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe crep_to_loop_write_bytearray_mem_rel_probeScript.sml \
  crep_to_loop_write_bytearray_mem_rel_probe.out \
  le_full_8_pan le_part_8_word \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml"
run_probe pan_sem_mem_store_byte_probeScript.sml pan_sem_mem_store_byte_probe.out \
  store_byte_hit_some write_bytearray_out_of_domain \
  "$cake_dir/pancake/semantics/panSemScript.sml" "$cake_dir/pancake/semantics"
run_probe pan_sem_evaluate_fixed_load_probeScript.sml \
  pan_sem_evaluate_fixed_load_probe.out \
  eval_byte_hit eval_load32_alignment_failure \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_evaluate_fixed_store_probeScript.sml \
  pan_sem_evaluate_fixed_store_probe.out \
  evaluate_store_word_hit evaluate_store_byte_domain_failure \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_itree_evaluate_probeScript.sml pan_itree_evaluate_probe.out \
  itree_evaluate_skip itree_evaluate_tick \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_ext_probeScript.sml pan_ext_probe.out \
  ext_ffi ext_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_set_kvar_probeScript.sml pan_set_kvar_probe.out \
  set_kvar_local set_kvar_global_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_lookup_kvar_probeScript.sml pan_lookup_kvar_probe.out \
  lookup_kvar_local lookup_kvar_missing \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_is_valid_value_probeScript.sml pan_is_valid_value_probe.out \
  is_valid_value_local is_valid_value_mismatch \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_nb_op_probeScript.sml pan_nb_op_probe.out \
  op8 op32 \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sh_mem_load_probeScript.sml pan_sh_mem_load_probe.out \
  zero_width_domain_error nonzero_width_domain_error \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sh_mem_store_probeScript.sml pan_sh_mem_store_probe.out \
  zero_width_domain_error nonzero_width_domain_error \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_eval_probeScript.sml pan_eval_probe.out \
  eval_const eval_probe_done \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_mrec_probeScript.sml pan_mrec_probe.out \
  mrec_ret mrec_external \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_call_probeScript.sml \
  pan_itree_h_prog_call_probe.out \
  call_eval_failure call_success \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_bst_probeScript.sml pan_bst_probe.out \
  bst_locals bst_clock_ffi_irrelevant \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_set_var_probeScript.sml pan_itree_set_var_probe.out \
  set_var_new set_var_globals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_empty_locals_probeScript.sml pan_itree_empty_locals_probe.out \
  empty_locals_local empty_locals_base_addr \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe crep_primop_probeScript.sml crep_primop_probe.out \
  crep_basic crep_wrong_length \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_load_shape_probeScript.sml crep_load_shape_probe.out \
  empty nonzero_two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_load_shape64_probeScript.sml crep_load_shape64_probe.out \
  empty64 nonzero_two64 "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_to_loop_cutset_probeScript.sml crep_to_loop_cutset_probe.out \
  cut_set_const_args handler_original_live "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_nested_seq_probeScript.sml crep_nested_seq_probe.out \
  empty assign_seq "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_assigned_free_vars_probeScript.sml crep_assigned_free_vars_probe.out \
  skip shmem_fallback "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_stores_probeScript.sml crep_stores_probe.out \
  empty nonzero_two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_nested_decs_probeScript.sml crep_nested_decs_probe.out \
  empty values_empty "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_store_globals_probeScript.sml crep_store_globals_probe.out \
  empty two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_load_globals_probeScript.sml crep_load_globals_probe.out \
  empty three "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_assign_ret_probeScript.sml crep_assign_ret_probe.out \
  empty two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_var_cexp_probeScript.sml crep_var_cexp_probe.out \
  const base_top "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_exps_probeScript.sml crep_exps_probe.out \
  leaves loads ops "$cake_dir/pancake/crepLangScript.sml"
run_probe cexp_heads_probeScript.sml cexp_heads_probe.out \
  empty heads empty_head empty_tail inferred_type "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe comp_field_probeScript.sml comp_field_probe.out \
  first short "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_panop_probeScript.sml compile_panop_probe.out \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_exp_probeScript.sml compile_exp_probe.out \
  leaves missing_local bytes_in_word nstruct nfield load_one load_two struct_field \
  struct_fallbacks loads_ops cmp_shift shape_fallbacks heads_fallbacks \
  binary_fallbacks finite_map_shadow finite_map_load32_local \
  finite_map_load_byte_local loadbyte_recursive_address \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe exp_hdl_probeScript.sml exp_hdl_probe.out \
  missing known dup_update dup_list "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe ret_var_probeScript.sml ret_var_probe.out \
  one_empty named "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe ret_hdl_probeScript.sml ret_hdl_probe.out \
  one named "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe wrap_rt_probeScript.sml wrap_rt_probe.out \
  none named "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_def_probeScript.sml compile_def_probe.out \
  return multi_return store32_clause store32_fallback store_byte_clause store_byte_fallback \
  if_clause if_fallback while_clause while_fallback \
  global_assign_fallback global_shmem_load_fallback \
  local_assign_direct local_assign_overlap_temporaries local_assign_missing_destination \
  local_assign_length_fallback \
  primitive_destination_present primitive_destination_missing \
  store_one_word store_multiword store_address_fallback store_shape_length_fallback \
  raise_one_word raise_multiword raise_missing_eid raise_shape_length_fallback \
  shmem_store_clause shmem_store_value_fallback shmem_store_address_fallback \
  shmem_load_local_clause shmem_load_missing_destination shmem_load_address_fallback \
  dec_one_word dec_multiword dec_declared_shape_ignored dec_shape_length_fallback \
  struct_skip struct_break struct_continue struct_tick struct_annot struct_seq \
  missing_global empty_one_global extra_names_global missing_names_global \
  missing_local empty_one_local extra_names_local missing_names_local valid_local \
  empty_struct_return finite_map_shadow_return deccall_one_word deccall_multiword \
  extcall_high_tail \
  extcall_shared_high_tail extcall_constants extcall_shape_fallback \
  pair_load pair_store fixed_stride64 \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe eval_nested_assign_distinct_eq_probeScript.sml eval_nested_assign_distinct_eq_probe.out \
  assign_list_success duplicate_names_all_distinct expression_interference_distinct_lists \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe eval_nested_decs_seq_res_var_eq_probeScript.sml \
  eval_nested_decs_seq_res_var_eq_probe.out \
  nested_decs_restore_absent_local nested_decs_restore_existing_local \
  nested_decs_length_mismatch_skip valid_declaration_premises \
  duplicate_names_rejected expression_interference_rejected length_premise_rejected \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe eval_nested_decs_load_globals_probeScript.sml \
  eval_nested_decs_load_globals_probe.out \
  word_lookup_and_nested_decs_theorem struct_lookup_and_nested_decs_theorem \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe compile_to_crep_probeScript.sml compile_to_crep_probe.out \
  empty raise_const raise_pair raise_pair_later raise_pair_later_64 handled_pair done \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe pan_to_crep_comp_func_probeScript.sml pan_to_crep_comp_func_probe.out \
  comp_func_skip comp_func_one_parameter_return comp_func_pair_parameter_return \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_alookup_compile_probeScript.sml crep_alookup_compile_probe.out \
  source_names_distinct alookup_param_entry "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_el_compile_probeScript.sml crep_el_compile_probe.out \
  source_el_f compiled_el_f "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_make_funcs_probeScript.sml crep_make_funcs_probe.out \
  make_funcs_empty_params make_funcs_duplicate_first_wins "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_get_eids_probeScript.sml crep_get_eids_probe.out \
  eids_present eids_codes_distinct "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_vmap_ctxtfc_probeScript.sml crep_vmap_ctxtfc_probe.out \
  vmap_x vmap_eq_ctxt "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe dup_exn_eids_probeScript.sml dup_exn_eids_probe.out \
  dup_eids_lookup mixed_eids_lookup_a mixed_eids_lookup_e dup_compile done \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_prog_probeScript.sml compile_prog_probe.out \
  empty inline_call global_dest handled_missing_dest done \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe excp_rel_probeScript.sml excp_rel_probe.out \
  empty_maps noninjective_compiler_codes \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_to_crep_state_rel_carrier_probeScript.sml pan_to_crep_state_rel_carrier_probe.out \
  state_rel_matching_fields state_rel_rejects_nonempty_structs \
  state_rel_globals_equation_unreduced state_rel_nonempty_globals_lookup \
  state_rel_empty_globals_lookup state_rel_named_struct_carrier \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_to_crep_slc_tlc_probeScript.sml pan_to_crep_slc_tlc_probe.out \
  slc_tlc_slc_x slc_tlc_slc_y slc_tlc_slc_absent slc_tlc_tlc_0 slc_tlc_tlc_1 \
  slc_tlc_tlc_absent slc_tlc_rw_slc_holds slc_tlc_rw_tlc_holds \
  slc_tlc_slc_rhs_lookup slc_tlc_tlc_rhs_lookup \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_to_crep_ret_inst2_probeScript.sml pan_to_crep_ret_inst2_probe.out \
  ret_inst2_args ret_inst2_lookup ret_inst2_body_run ret_inst2_state_rel \
  ret_inst2_locals_rel ret_inst2_five_premise_return ret_inst2_return_result \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe ctxt_fc_probeScript.sml ctxt_fc_probe.out \
  shaped_slots empty_maximum functions_projection vmax_nonempty_list vmax_empty_list \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe code_rel_probeScript.sml code_rel_probe.out \
  code_rel_type compiled_return localised_return localised_global_assignment \
  function_signature_lookup target_function_lookup code_rel_generated_initial \
  code_rel_generated_initial_proved \
  code_rel_rejects_unlocalised_source \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe globals_lookup_probeScript.sml globals_lookup_probe.out \
  lookup_success lookup_missing lookup_struct \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_globals_compile_probeScript.sml pan_globals_compile_probe.out \
  local_assign global_destination_handler_flag global_destination_handler_local_arg \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

run_probe pan_globals_compile_top_probeScript.sml pan_globals_compile_top_probe.out \
  missing_start global_present present_start top_missing top_function top_global_exception compile_top_probe_done "$cake_dir/pancake/pan_globalsScript.sml"
run_probe pan_globals_compile_decs_probeScript.sml pan_globals_compile_decs_probe.out \
  empty compile_decs_probe_done "$cake_dir/pancake/pan_globalsScript.sml"
run_probe smart_seq_probeScript.sml smart_seq_probe.out \
  skip_skip skip_tick tick_skip tick_tick "$cake_dir/pancake/pan_simpScript.sml"
run_probe seq_assoc_probeScript.sml seq_assoc_probe.out \
  skip_skip tick_skip tick_seq_skip_tick tick_return \
  "$cake_dir/pancake/pan_simpScript.sml"
run_probe seq_call_ret_probeScript.sml seq_call_ret_probe.out \
  matching_return mismatching_return fallback \
  "$cake_dir/pancake/pan_simpScript.sml"
run_probe ret_to_tail_probeScript.sml ret_to_tail_probe.out \
  skip tail_call mismatching_return handler_seq \
  "$cake_dir/pancake/pan_simpScript.sml"
run_probe pan_simp_compile_probeScript.sml pan_simp_compile_probe.out \
  skip seq_skip_tick tail_call "$cake_dir/pancake/pan_simpScript.sml"
run_probe crep_exit_loop_probeScript.sml crep_exit_loop_probe.out \
  exit_loop_break exit_loop_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_evaluate_probeScript.sml crep_evaluate_probe.out \
  evaluate_skip evaluate_tick_timeout \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_fix_clock_probeScript.sml crep_fix_clock_probe.out \
  fix_clock_clamps fix_clock_keeps_lower \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_local_updates_probeScript.sml crep_local_updates_probe.out \
  set_var_hit empty_locals_fields_preserved \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_sh_mem_load_probeScript.sml crep_sh_mem_load_probe.out \
  sh_mem_load_zero_width_domain_error sh_mem_load_nonzero_domain_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_sh_mem_op_probeScript.sml crep_sh_mem_op_probe.out \
  sh_mem_op_load sh_mem_op_store \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_sh_mem_store_probeScript.sml crep_sh_mem_store_probe.out \
  sh_mem_store_missing_local sh_mem_store_nonzero_domain_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_clock_helpers_probeScript.sml crep_clock_helpers_probe.out \
  clock_eq_simp_set_var clock_eq_simp_empty_locals clock_eq_simp_set_globals \
  sh_mem_load_clock sh_mem_load_clock_nonzero \
  sh_mem_store_clock sh_mem_store_clock_nonzero \
  sh_mem_op_clock_load sh_mem_op_clock_store8 \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_mem_load_probeScript.sml crep_mem_load_probe.out \
  mem_load_hit mem_load_miss \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_op_probeScript.sml crep_op_probe.out \
  op_mul_two op_mul_empty \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_eval_probeScript.sml crep_eval_probe.out \
  eval_const eval_base_top \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_dest_2exp_probeScript.sml crep_dest_2exp_probe.out \
  zero highest_shift_conclusion bound_eight \
  "$cake_dir/pancake/crep_arithScript.sml"
run_probe hol_fcp_index_n2w_probeScript.sml hol_fcp_index_n2w_probe.out \
  n2w_zero_word bit_high6 "$hol_dir/src/n-bit/wordsScript.sml" \
  "$hol_dir/src/n-bit"
run_probe hol_word_arithmetic_probeScript.sml hol_word_arithmetic_probe.out \
  word_add_definition sub_3_5_8 "$hol_dir/src/n-bit/wordsScript.sml" \
  "$hol_dir/src/n-bit"
run_probe word_op_finite_probeScript.sml word_op_finite_probe.out \
  word_op_definition word_op_finite_done \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_sh_finite_probeScript.sml word_sh_finite_probe.out \
  word_sh_definition lsl_above_width \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe crep_mul_const_probeScript.sml crep_mul_const_probe.out \
  zero eight "$cake_dir/pancake/crep_arithScript.sml"
run_probe crep_simp_exp_probeScript.sml crep_simp_exp_probe.out \
  const_mul eval_simp_after "$cake_dir/pancake/crep_arithScript.sml"
run_probe crep_simp_prog_probeScript.sml crep_simp_prog_probe.out \
  assign unchanged "$cake_dir/pancake/crep_arithScript.sml"
run_probe afindi_probeScript.sml afindi_probe.out \
  empty duplicate_first wf_shape_drop dropWhile_MAP_helper UNCURRY_EQ_o_SND_pair \
  map_uncurry_zip_again struct_infos_ok_drop struct_infos_ok_append \
  struct_infos_ok_cons alookup_map_structs_ok fields_in_order_reorder_noop \
  opt_mmap_eq_every alookup_drop_helper map_fst_eq_alookup \
  map_fst_eq_alookup_different_value_types map_fst_eq_alookup_inferred_types \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml"
run_probe pan_structs_compile_decls_probeScript.sml pan_structs_compile_decls_probe.out \
  empty decs names top shadow "$cake_dir/pancake/pan_structsScript.sml"
run_probe pan_structs_compile_prog_probeScript.sml pan_structs_compile_prog_probe.out \
  dec deccall handler callnone callnohandler fallback "$cake_dir/pancake/pan_structsScript.sml"
run_probe pan_structs_compile_exp_probeScript.sml pan_structs_compile_exp_probe.out \
  rstruct old_shapes_map "$cake_dir/pancake/pan_structsScript.sml"
run_probe crep_semantics_probeScript.sml crep_semantics_probe.out \
  semantics_timeout_is_nonterminal semantics_break_is_nonterminal \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_res_var_probeScript.sml crep_res_var_probe.out \
  res_var_delete_hit res_var_update_hit \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_lookup_code_probeScript.sml crep_lookup_code_probe.out \
  lookup_code_valid lookup_code_duplicate \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
# The store_global probe observes StoreGlob insert/update/error on globals.
run_probe crep_store_global_probeScript.sml crep_store_global_probe.out \
  set_globals_direct store_global_then_load \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
# The locals_wordlab probe observes varname |-> word_lab cell retention,
# Var-read flattening and overwrite behaviour.
run_probe crep_locals_wordlab_probeScript.sml crep_locals_wordlab_probe.out \
  locals_set_var_cell locals_set_var_overwrite \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_replicate_const_probeScript.sml crep_replicate_const_probe.out \
  replicate_const_one replicate_const_nonzero \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The mem_load probe observes the total word -> word_lab memory function and the
# memaddrs guard on both mem_load and eval (Load ...).
run_probe crep_mem_load_probeScript.sml crep_mem_load_probe.out \
  mem_load_valid eval_load_invalid \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_mem_store_probeScript.sml crep_mem_store_probe.out \
  mem_store_valid_lookup mem_store_invalid \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval LoadByte probe observes the fixed RV64 get_byte/byte_align path:
# little-endian byte extraction from a total word -> word_lab memory, plus the
# memaddrs guard and the underlying mem_load_byte.
run_probe crep_eval_load_byte_probeScript.sml crep_eval_load_byte_probe.out \
  eval_loadbyte_addr8 eval_loadbyte_w24_be_addr5 \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Load32 probe observes the fixed RV64 aligned four-byte read:
# little-endian and big-endian byte order, alignment failure, and the memaddrs
# domain failure over a total word -> word_lab memory.
run_probe crep_eval_load_32_probeScript.sml crep_eval_load_32_probe.out \
  eval_load32_le_addr8 eval_load32_w24_addr4 \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Load (word cell) probe observes the fixed RV64 total word -> word_lab
# memory cell read: a live cell and the memaddrs domain failure.
run_probe crep_eval_load_rv64_probeScript.sml crep_eval_load_rv64_probe.out \
  mem_load_valid eval_load_outside_domain eval_load_one_load_one \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval StoreByte probe observes HOL set_byte at a nonzero byte offset: the
# cell updated at address 8 and at address 9, plus the memaddrs domain failure.
run_probe crep_eval_store_byte_offset_probeScript.sml \
  crep_eval_store_byte_offset_probe.out \
  storebyte_offset9_result storebyte_outside_domain_mem8 \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Store32 high-bits probe observes HOL `mem_store_32`'s up-front `w2w`
# truncation: storing 0xDEADBEEF11223344 and 0x11223344 leave the same cell.
run_probe crep_eval_store_32_highbits_probeScript.sml \
  crep_eval_store_32_highbits_probe.out \
  w2w_highbits store32_unaligned_result \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Op probe observes HOL word_op folding over constant operands for the
# RV64 target (Add/Sub/And, plus the empty-Add neutral and the Sub arity failure).
run_probe crep_eval_op_rv64_probeScript.sml crep_eval_op_rv64_probe.out \
  eval_op_add_const eval_op_sub_arity \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Cmp probe observes HOL word_cmp over constant operands for the RV64
# target (Equal/Lower/Test true and false).
run_probe crep_eval_cmp_rv64_probeScript.sml crep_eval_cmp_rv64_probe.out \
  eval_cmp_equal_true eval_cmp_not_test_overlap \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Shift probe observes HOL word_sh over constant operands for the RV64
# target (Lsl/Lsr/Asr/Ror, amount zero, and the invalid width-sized amount).
run_probe crep_eval_shift_rv64_probeScript.sml crep_eval_shift_rv64_probe.out \
  eval_shift_lsl_const eval_shift_amount_width \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The Crepop Mul probe observes HOL crep_op over constant operands (product and
# the arity failures for three, one, and zero operands).
run_probe crep_eval_crepop_mul_rv64_probeScript.sml crep_eval_crepop_mul_rv64_probe.out \
  eval_crepop_mul_const eval_crepop_mul_empty \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe prog_if_probeScript.sml prog_if_probe.out \
  prog_if_basic prog_if_basic prog_if_wrong_result prog_if_wrong_result \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_to_loop_compile_exp_probeScript.sml crep_to_loop_compile_exp_probe.out \
  prog_if base var_hit load32 op_nary crepop_mul cmp shift compile_exps \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_to_loop_comp_func_probeScript.sml crep_to_loop_comp_func_probe.out \
  comp_func_skip comp_func_return_var comp_func_two_params done \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe loop_props_comp_syntax_probeScript.sml loop_props_comp_syntax_probe.out \
  comp_syntax_loop_positive comp_syntax_if_negative \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_to_loop_list_to_num_set_probeScript.sml crep_to_loop_list_to_num_set_probe.out \
  ltns_nil_0 ltns_cons_shape done \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_to_loop_compile_probeScript.sml crep_to_loop_compile_probe.out \
  loop_nested_seq_empty compile_ext_call \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_to_loop_compile_prog_probeScript.sml crep_to_loop_compile_prog_probe.out \
  cp_fnums cp_params cp_body cp_length cp_call_fnums cp_call_params cp_call_body done \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_to_loop_ocompile_probeScript.sml crep_to_loop_ocompile_probe.out \
  ocompile_skip ocompile_call \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_to_loop_code_rel_probeScript.sml crep_to_loop_code_rel_probe.out \
  code_rel_funcs_lookup code_rel_lookup_pair \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" "$cake_dir/pancake/proofs"
run_probe crep_to_loop_evaluate_io_mono_type_probeScript.sml \
  crep_to_loop_evaluate_io_mono_type_probe.out \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" "$cake_dir/pancake/proofs"
run_probe compile_crepop_probeScript.sml compile_crepop_probe.out \
  compile_crepop_mul_riscv compile_crepop_mul_armv7 \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe pan_empty_locals_probeScript.sml pan_empty_locals_probe.out \
  empty_locals empty_locals_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_itree_h_prog_dec_probeScript.sml pan_itree_h_prog_dec_probe.out \
  dec_valid_event dec_failed_response "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_seq_probeScript.sml pan_itree_h_prog_seq_probe.out \
  seq_second_event seq_second_normal "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_cond_probeScript.sml pan_itree_h_prog_cond_probe.out \
  cond_true_branch cond_failed_source "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_store_probeScript.sml pan_itree_h_prog_store_probe.out \
  store_success store_invalid_value "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_assign_probeScript.sml pan_itree_h_prog_assign_probe.out \
  assign_valid assign_failed_eval "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_while_probeScript.sml pan_itree_h_prog_while_probe.out \
  while_zero_guard while_invalid_guard "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe loop_sem_get_vars_probeScript.sml loop_sem_get_vars_probe.out \
  get_vars_hit get_vars_loc "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_get_var_imm_probeScript.sml \
  loop_sem_get_var_imm_probe.out \
  reg_hit reg_loc "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_props_get_vars_probeScript.sml \
  loop_props_get_vars_probe.out \
  get_vars_two get_var_imm_add_clk_eq \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe loop_props_survives_probeScript.sml \
  loop_props_survives_probe.out \
  if_hit if_miss loop_hit loop_miss_out call_hit call_miss \
  call_handler_hit call_handler_miss_post ffi_hit ffi_miss mark_seq \
  call_default assign_default \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe loop_props_every_prog_probeScript.sml \
  loop_props_every_prog_probe.out \
  ep_skip ep_assign ep_seq ep_seq_loop ep_loop ep_if ep_if_loop \
  ep_mark ep_mark_loop ep_call_none ep_call_handler ep_call_handler_fst \
  ep_call_handler_snd \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe loop_sem_call_env_probeScript.sml \
  loop_sem_call_env_probe.out \
  arg_zero arg_missing "$cake_dir/pancake/semantics/loopSemScript.sml"
# The locals_touched probe observes the structural Loop expression analysis.
run_probe loop_lang_locals_touched_probeScript.sml \
  loop_lang_locals_touched_probe.out \
  const base_addr "$cake_dir/pancake/loopLangScript.sml"
run_probe vars_of_exp_probeScript.sml vars_of_exp_probe.out \
  var shift_nested "$cake_dir/pancake/loop_liveScript.sml"
run_probe arith_vars_probeScript.sml arith_vars_probe.out \
  long_mul long_div "$cake_dir/pancake/loop_liveScript.sml"
run_probe shrink_leaf_probeScript.sml shrink_leaf_probe.out \
  skip load32 "$cake_dir/pancake/loop_liveScript.sml"
run_probe mark_all_probeScript.sml mark_all_probe.out \
  seq_mark call_handler "$cake_dir/pancake/loop_liveScript.sml"
run_probe loop_live_comp_probeScript.sml loop_live_comp_probe.out \
  skip return "$cake_dir/pancake/loop_liveScript.sml"
run_probe loop_live_optimise_probeScript.sml loop_live_optimise_probe.out \
  skip shrink_loop_fixedpoint "$cake_dir/pancake/loop_liveScript.sml"
run_probe loop_live_domain_list_delete_probeScript.sml \
  loop_live_domain_list_delete_probe.out \
  dld_kept dld_absent \
  "$cake_dir/pancake/proofs/loop_liveProofScript.sml" "$cake_dir/pancake/proofs"
run_probe ocompile_probeScript.sml ocompile_probe.out \
  skip ffi "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe loop_lang_assigned_vars_probeScript.sml \
  loop_lang_assigned_vars_probe.out \
  skip load_byte "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_lang_acc_vars_probeScript.sml \
  loop_lang_acc_vars_probe.out \
  skip call_none "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_lang_nested_seq_probeScript.sml \
  loop_lang_nested_seq_probe.out \
  empty assign_load "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_call_is_load_probeScript.sml \
  loop_call_is_load_probe.out \
  load store32 "$cake_dir/pancake/loop_callScript.sml"
run_probe loop_call_comp_probeScript.sml \
  loop_call_comp_probe.out \
  skip fallback_keeps "$cake_dir/pancake/loop_callScript.sml"
# The set_globals probe observes FLOOKUP after the original map update.
run_probe loop_sem_set_globals_probeScript.sml loop_sem_set_globals_probe.out \
  set_globals_new set_globals_sibling "$cake_dir/pancake/semantics/loopSemScript.sml"
# The set_vars probe observes sptree lookups after the original alist_insert.
run_probe loop_sem_set_vars_probeScript.sml loop_sem_set_vars_probe.out \
  set_vars_basic set_vars_clock "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_set_var_probeScript.sml loop_sem_set_var_probe.out \
  set_var_new set_var_missing "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_dec_clock_probeScript.sml loop_sem_dec_clock_probe.out \
  dec_clock_five dec_clock_local "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_fix_clock_probeScript.sml loop_sem_fix_clock_probe.out \
  fix_clock_lower_new fix_clock_zero "$cake_dir/pancake/semantics/loopSemScript.sml"

# The find_code probe observes the returned parameter map via sptree lookups.
run_probe loop_sem_find_code_probeScript.sml loop_sem_find_code_probe.out \
  find_code_label_first find_code_dup_first "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_primop_probeScript.sml loop_sem_primop_probe.out \
  valid_no_carry invalid_nonword "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_store_narrow_probeScript.sml loop_sem_store_narrow_probe.out \
  store32_narrow store32_big store32_upper store32_unaligned store32_domain store32_memory_loc store32_address_loc store32_value_loc store32_other storeByte_narrow storeByte_big storeByte_domain storeByte_memory_loc storeByte_address_loc storeByte_value_loc storeByte_clock \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_mem_store_probeScript.sml loop_sem_mem_store_probe.out \
  mem_store_hit mem_store_other "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_mem_load_probeScript.sml loop_sem_mem_load_probe.out \
  mem_load_hit mem_load_miss "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_eval_probeScript.sml loop_sem_eval_probe.out \
  const top_addr "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_evaluate_probeScript.sml loop_sem_evaluate_probe.out \
  skip tick_timeout "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_evaluate_control_probeScript.sml loop_sem_evaluate_control_probe.out \
  if_true if_false if_cut_error if_nonword_left_error if_nonword_right_error \
  loop_break0 loop_return loop_timeout \
  loop_continue0_timeout loop_break_outer call_return call_return_handler \
  call_exception_handler call_exception_no_handler call_arity_error \
  tail_call_return raise primitive_add_carry loc_value loc_value_missing \
  ffi_empty_name "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_semantics_probeScript.sml loop_semantics_probe.out \
  return_clock_zero return_clock_one "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_lprefix_lub_probeScript.sml loop_sem_lprefix_lub_probe.out \
  empty_lub_0 singleton_lub_0 singleton_lub_1 \
  prefix_chain_lub_0 prefix_chain_lub_1 \
  conflicting_prefixes_lub_0 conflicting_prefixes_lub_1 \
  conflicting_suffixes_lub_0 conflicting_suffixes_lub_1 \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe lprefix_lub_llist_shorter_probeScript.sml lprefix_lub_llist_shorter_probe.out \
  llist_shorter_shorter llist_shorter_equal_length llist_shorter_longer \
  llist_shorter_two_empty llist_shorter_nil_nonempty llist_shorter_nonempty_nil \
  llist_shorter_reverse_longer llist_shorter_equal_nonempty \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_cut_state_probeScript.sml loop_sem_cut_state_probe.out \
  hit_first loc_preserved "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_cut_res_probeScript.sml loop_sem_cut_res_probe.out \
  result_short_circuit clock_decrement_and_cut \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_cut_zero_probeScript.sml loop_sem_cut_zero_probe.out \
  cut0_success_lookup cut0_missing cut0_empty_live cut0_res_short_circuit \
  cut0_res_missing_error cut0_res_timeout cut0_res_decrement \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_sh_mem_load_probeScript.sml loop_sem_sh_mem_load_probe.out \
  return_zero_width aligned_domain_original_payload \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_sh_mem_store_probeScript.sml loop_sem_sh_mem_store_probe.out \
  store_zero_width aligned_domain_original_payload \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_sh_mem_op_probeScript.sml loop_sem_sh_mem_op_probe.out \
  load store32 "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_ffi_probeScript.sml loop_sem_ffi_probe.out \
  extcall_returned extcall_missing_local \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_ffi_rv64_probeScript.sml loop_sem_ffi_rv64_probe.out \
  rv64_lookups rv64_extcall_live_absent \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe byte_align_probeScript.sml byte_align_probe.out \
  ba24_5 ba8_7 "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_exit_loop_probeScript.sml loop_sem_exit_loop_probe.out \
  exit_loop_break exit_loop_error "$cake_dir/pancake/semantics/loopSemScript.sml"
# The loop_arith probe prints numeric word values to avoid raw-literal ambiguity.
run_probe pan_itree_h_handle_call_ret_probeScript.sml \
  pan_itree_h_handle_call_ret_probe.out \
  failed_caller uncaught_exception \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_handle_deccall_ret_probeScript.sml \
  pan_itree_h_handle_deccall_ret_probe.out \
  failed_caller raised_clears_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe loop_sem_loop_arith_probeScript.sml loop_sem_loop_arith_probe.out \
  loop_arith_div loop_arith_signed_8 "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe longdiv_code_probeScript.sml longdiv_code_probe.out \
  longdiv_code_software riscv_longdiv_encoding \
  "$cake_dir/compiler/backend/data_to_wordScript.sml"
run_probe pan_itree_h_prog_deccall_probeScript.sml \
  pan_itree_h_prog_deccall_probe.out \
  argument_failure lookup_failure \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_call_probeScript.sml \
  pan_itree_h_prog_call_probe.out \
  argument_failure lookup_failure \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe word_byte_memory_probeScript.sml word_byte_memory_probe.out \
  byte_index_definition set_byte_width12_preserves_high_numeric \
  "$hol_dir/src/n-bit/byteScript.sml" "$hol_dir/src/n-bit"
# `labels_rel` is the wordConvs label-preservation relation; the fixture
# simplifies under `labels_rel_def` because `EVAL` leaves `set ... SUBSET ...`.
run_probe word_convs_labels_rel_probeScript.sml word_convs_labels_rel_probe.out \
  labels_rel_refl_ok labels_rel_pair_ok \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"
# `extract_labels` collects the Call handler label pairs (and descends into
# return/handler/Seq/Loop/If bodies); with no Call return metadata it is empty
# even when a handler is present.
run_probe word_convs_extract_labels_probeScript.sml word_convs_extract_labels_probe.out \
  el_inst el_nested \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The instruction-predicate probe observes the `distinct_tar_reg` and
# `two_reg_inst` arithmetic cases, and `every_inst` descending through the
# program's structural positions (including the `Call` return-metadata
# nesting).
run_probe word_convs_inst_preds_probeScript.sml word_convs_inst_preds_probe.out \
  dtr_binop_same ei_alloc \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The flat-exp probe observes the expression-shape restrictions of
# `flat_exp_conventions` and its descent through composition and `Call`.
run_probe word_convs_flat_exp_probeScript.sml word_convs_flat_exp_probe.out \
  fl_assign fl_inst \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The asm_config probe observes each HOL assembler validity predicate and
# configuration projection used by `stackProps$stack_asm_ok`, plus `asm_ok`
# over the full `asm` datatype (Inst/Jump/JumpCmp/Call/JumpReg/Loc).
run_probe asm_config_checks_probeScript.sml asm_config_checks_probe.out \
  aligned0 asmOkLoc \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# Direct HOL fixture for wordConvs$inst_ok_less, the weaker per-instruction
# well-formedness predicate consumed by compile_to_word_conventions2.
run_probe word_convs_inst_ok_less_probeScript.sml word_convs_inst_ok_less_probe.out \
  iol_binop_imm iol_movfromreg_fp_out_of_range \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The full_inst_ok_less probe observes `exp_to_addr` and the lifted
# `wordConvs$full_inst_ok_less` predicate over the backend wordLang syntax.
run_probe word_convs_full_inst_ok_less_probeScript.sml word_convs_full_inst_ok_less_probe.out \
  eta_var fiol_alloc \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The call_arg_convention probe observes `wordConvs$inst_arg_convention` and
# `wordConvs$call_arg_convention` over the backend wordLang syntax.
run_probe word_convs_call_arg_probeScript.sml word_convs_call_arg_probe.out \
  inst_addcarry_ok call_seq_bad \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The register-allocation partition probe observes the three predicates and
# the partition lemma on representative residues.
run_probe reg_alloc_var_partition_probeScript.sml reg_alloc_var_partition_probe.out \
  is_phy_6 part_none_0 \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend/reg_alloc"

# The not-created-subprograms probe observes the four no_* specialisations on
# their own constants and on nesting/handler cases.
run_probe word_convs_not_created_probeScript.sml word_convs_not_created_probe.out \
  nac_skip nac_install_empty \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The every_var family probe observes the wordLang expression/immediate/
# instruction revisors on even/odd registers and the width-dependent FP moves.
run_probe word_lang_every_var_probeScript.sml word_lang_every_var_probe.out \
  evar_var einst_skip \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem carrier probe observes buffer_flush/buffer_write/stack_size for
# the exact carrier port (bead flapjack-h29l.1).
run_probe word_sem_carriers_probeScript.sml word_sem_carriers_probe.out \
  buffer_flush_hit stack_size_unbounded \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem accessor probe observes word_cmp, is_fwd_ptr, word_exp and the
# state accessors over record updates of a free state (bead flapjack-h29l.2).
run_probe word_sem_accessors_probeScript.sml word_sem_accessors_probe.out \
  cmp_equal exp_op fix_clock var_imm_reg the_word_word1 the_word_word64 get_word_word32 get_word_word80 \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem env/stack probe observes key_val_compare, list_rearrange (with
# its BIJ guard decided over the finite count set), fromList2, mllist$sort,
# env_to_list, call_env, push_env/pop_env, jump_exc and the cut_* helpers
# (bead flapjack-h29l.4).
run_probe word_sem_env_probeScript.sml word_sem_env_probe.out \
  kvc_loc_loc rearrange_rev env_to_list push_env_some jump_exc cut_state_opt_none \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem call-helper probe observes add_ret_loc, bad_dest_args,
# const_addresses/const_writes, STOP, bad_fun_return, cont_loop, exit_loop and
# the [nocompute] MustTerminate_limit unfolded at width 1 (bead flapjack-h29l.7).
run_probe word_sem_call_helpers_probeScript.sml word_sem_call_helpers_probe.out \
  add_ret_loc_none const_writes exit_loop_break0 must_terminate_limit_1 \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem code/GC/alloc probe observes find_code, enc_stack/dec_stack, gc
# with a supplied gc_fun, has_space, alloc (success, NotEnoughSpace, cut and gc
# failure) and assign (bead flapjack-h29l.5).
run_probe word_sem_alloc_probeScript.sml word_sem_alloc_probe.out \
  find_code_some dec_stack_hit gc_rev alloc_ok assign_fail \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem shared-memory probe observes share_inst for every memop (through
# sh_mem_store*/sh_mem_load* and sh_mem_set_var) with a byte-incrementing and a
# diverging FFI oracle, recording configuration and payload bytes via
# io_events (bead flapjack-h29l.3).
run_probe word_sem_sh_mem_probeScript.sml word_sem_sh_mem_probe.out \
  store store_final load8 load_final sh_mem_set_var_none \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The machine_ieee fp64 probe observes fp64_lessThan/lessEqual/equal/abs/negate
# on +-0, subnormals, the least normal, the largest finite value, infinities
# and quiet/signalling NaNs; binary_ieeeLib extends EVAL with the IEEE
# conversions (bead flapjack-h29l.6.1).
run_probe machine_ieee_fp64_compare_probeScript.sml machine_ieee_fp64_compare_probe.out \
  lt_one_two le_pz_nz eq_pz_nz abs_negone neg_sub1 \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The fpSem ``fp_cmp`` probe observes the ast$opb comparison selector of
# ``fp_cmp_def`` at binary64 values (bead flapjack-h29l.6.2.7).
run_probe fp_sem_fp_cmp_probeScript.sml fp_sem_fp_cmp_probe.out \
  fp_cmp_lt_one_two fp_cmp_leq_two_one fp_cmp_gt_two_one \
  fp_cmp_geq_one_one fp_cmp_lt_qnan_one fp_cmp_gt_pinf_one \
  "$cake_dir/semantics/fpSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The binary_ieee rounding-constant probe observes largest and threshold at
# binary64 and float_top's value (bead flapjack-h29l.6.2.1).
run_probe binary_ieee_round_constants_probeScript.sml binary_ieee_round_constants_probe.out \
  largest_fp64 threshold_fp64 top_is_largest \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The binary64 arithmetic special-case probe observes the infinity and
# zero-divisor branches of fp64_add/sub/mul/div and the tagged fpSem fpfma
# (bead flapjack-h29l.6.2.2).
run_probe machine_ieee_fp64_arith_special_probeScript.sml machine_ieee_fp64_arith_special_probe.out \
  add_pinf_one div_one_pz fma_order_inf \
  "$cake_dir/semantics/fpSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The binary64 rounding probe observes float_round roundTiesToEven on ties,
# subnormal ties, the overflow threshold, negative inputs and zero signs
# (bead flapjack-h29l.6.2.3).
run_probe binary_ieee_round_fp64_probeScript.sml binary_ieee_round_fp64_probe.out \
  third tie_up_even sub_three_half at_threshold big_odd \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The binary64 rounded-arithmetic probe observes finite results of
# fp64_add/sub/mul/div and the tagged fpSem fpfma, including zero signs,
# overflow and subnormal ties (bead flapjack-h29l.6.2.4).
run_probe machine_ieee_fp64_arith_round_probeScript.sml machine_ieee_fp64_arith_round_probe.out \
  add_tenth_fifth mul_max_two div_sub1_two fma_cancel \
  "$cake_dir/semantics/fpSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The NaN probe prints a kernel-proved float_some_qnan classification theorem
# and exact HOL EVAL operation branches.  Payloads are unspecified and flags
# are not compared.
run_probe machine_ieee_fp64_arith_nan_probeScript.sml machine_ieee_fp64_arith_nan_probe.out \
  source_qnan_classification add_qnan_input sub_qnan_input mul_qnan_input \
  div_qnan_input fma_qnan_input \
  add_invalid_infinities sub_invalid_infinities mul_invalid_inf_zero \
  div_invalid_zero_zero div_invalid_inf_inf fma_invalid_inf_zero \
  fma_invalid_opposed_infinities \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$hol_dir/src/floating-point"

# The binary64 conversion probe observes fp64_to_int in all four modes (ties,
# NaN/infinity to NONE) and int_to_fp64 roundTiesToEven (ties, overflow,
# negative) (bead flapjack-h29l.6.3.1).
run_probe machine_ieee_fp64_convert_probeScript.sml machine_ieee_fp64_convert_probe.out \
  to_int_2_5 to_int_nan to_int_rtn_neg_2_1 from_int_2p53_1 from_int_neg_big \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The binary64 sqrt special-case probe observes the choice-free fp64_sqrt
# branches (+inf, -0) (bead flapjack-h29l.6.3.2.1).
run_probe machine_ieee_fp64_sqrt_special_probeScript.sml machine_ieee_fp64_sqrt_special_probe.out \
  sqrt_pinf sqrt_nz \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The binary64 exact-square sqrt probe observes fp64_sqrt roundTiesToEven on
# exact squares, whose sqrt isqrtLib proves (bead flapjack-h29l.6.3.2.2).
run_probe machine_ieee_fp64_sqrt_exact_probeScript.sml machine_ieee_fp64_sqrt_exact_probe.out \
  sqrt_four sqrt_min_sub sqrt_2p1022 \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# Signed word quotient operator in original wordSem Div (.18.5.10.1).
run_probe word_sem_div_signed_probeScript.sml word_sem_div_signed_probe.out \
  positive negative_small negative_dividend negative_divisor both_negative \
  min_overflow min_half positive_minus_one zero_divisor zero_dividend \
  alias_dividend alias_divisor same_source missing_dividend location_divisor \
  min64_overflow min1_overflow \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem inst_def probe observes integer arithmetic, memory and
# floating-point instructions over record updates of a free state (bead
# flapjack-h29l.6).
run_probe word_sem_inst_probeScript.sml word_sem_inst_probe.out \
  div long_div load32 store8 fp_fma fp_to_int fp_missing \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem evaluate prerequisite probe observes misc$shift_seq and the
# sptree domain set conditions of the Call clause (bead flapjack-h29l.8.1).
run_probe word_sem_eval_prereq_probeScript.sml word_sem_eval_prereq_probe.out \
  shift_seq dom_empty_one dom_union_eq dom_union_missing \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The wordSem evaluate probe observes evaluate_def on straight-line, control,
# loop, raise/return, MustTerminate, Move/Get/Set/LocValue/StoreConsts, Alloc,
# Store, OpCurrHeap, ShareInst, CodeBufferWrite, DataBufferWrite, Install, tail
# and returning calls (including the caught-handler exception path), and FFI
# over record updates of a free state (bead flapjack-h29l.8.2).
run_probe word_sem_evaluate_probeScript.sml word_sem_evaluate_probe.out \
  skip loop_timeout raise_handler must_terminate call_ret ffi_ok \
  alloc_ok store_ok op_curr_heap share_inst_load code_buffer_write \
  data_buffer_write install_ok call_handler_exception \
  "$cake_dir/compiler/backend/semantics/wordSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The good_handlers probe observes the structural handler-label predicate,
# including the NONE-ret case (handler ignored) and nested bad handlers.
run_probe word_convs_good_handlers_probeScript.sml word_convs_good_handlers_probe.out \
  gh_call_none gh_other \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The num_set audit probe observes HOL misc$num_set = unit spt behaviour via
# sptree$toAList: canonical insertion-order-independent enumeration, duplicate
# collapse, wf for LN/insert/union, order-insensitive EVERY, and left-bias of
# union / last-write of insert for non-unit maps.
run_probe num_set_audit_probeScript.sml num_set_audit_probe.out \
  ns_empty nsmap_insert_last \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# Direct original observations of misc$lookup_any (an spt lookup with a default
# on a missing key) and misc$find_index (first-match search with a starting
# offset): hit / hit at key 0 / miss-default / empty for lookup_any, and
# hit-at-0 / later-hit / miss / earlier-duplicate for find_index (bead
# flapjack-pxn.18.5.15.10.10).
run_probe misc_lookup_any_find_index_probeScript.sml misc_lookup_any_find_index_probe.out \
  lu_hit lu_hit_zero lu_miss_default lu_empty_default \
  fi_zero fi_middle fi_absent fi_duplicate \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# Every name/var/stack-var predicates (num_set domain model): the probe also
# shows every_stack_var ignores the scalar FFI registers (only every_name / body).
run_probe word_lang_every_name_probeScript.sml word_lang_every_name_probe.out \
  en_empty esv_seq_bad \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# `pre_alloc_conventions` / `post_alloc_conventions`: stack/phy predicates,
# the `2*k` bound, and the call-argument convention.
run_probe word_convs_alloc_conventions_probeScript.sml word_convs_alloc_conventions_probe.out \
  pre_ok_ffi post_ok_ret \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The labProps probe pins `line_ok_pre`/`all_enc_ok_pre` and the concrete
# `cbw_to_asm` mapping at an 8-bit configuration.
run_probe lab_props_line_ok_pre_probeScript.sml lab_props_line_ok_pre_probe.out \
  line_ok_asm_skip all_enc_ok_empty \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The stack_to_lab flatten-ops probe observes the config-independent embedded
# constructors (negate table and compile_jump).
run_probe stack_to_lab_flatten_ops_probeScript.sml stack_to_lab_flatten_ops_probe.out \
  negate_less compile_jump_reg \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"

# The flatten base probe observes the non-recursive flatten constructors.
run_probe stack_to_lab_flatten_base_probeScript.sml stack_to_lab_flatten_base_probe.out \
  flatten_tick flatten_halt \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"

# The RISC-V configuration probe observes the exact `riscv_config` field
# values at 64-bit (register file, offsets, immediates) used by the stack
# assembler checks.
run_probe riscv_config_probeScript.sml riscv_config_probe.out \
  cfg_isa valid_imm_add_max12p1 \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"

# The misc app_list probe observes HOL `append_aux`/`append` flattening the
# `app_list` concatenation tree used by the stack_to_lab flatten statement.
run_probe misc_app_list_probeScript.sml misc_app_list_probe.out \
  append_aux_list append_aux_suffix \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# The flatten app_list probe observes `misc$append` flattening the HOL
# `stack_to_lab$flatten` app_list output to the production flat list.
run_probe stack_to_lab_flatten_app_list_probeScript.sml stack_to_lab_flatten_app_list_probe.out \
  flatten_app_tick flatten_app_ite_tick \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"

# The labProps sec_ends_with_label probe observes the `is_Label` classifier and
# the `¬NULL ls ∧ is_Label (LAST ls)` section test used by
# `EVERY_sec_ends_with_label_MAP_prog_to_section`.
run_probe lab_props_sec_ends_label_probeScript.sml lab_props_sec_ends_label_probe.out \
  is_label_label sec_empty \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The stack_names probe observes the pure register-renaming transformation
# (ri_find_name / inst_find_name / dest_find_name / comp / prog_comp /
# compile / names_ok) against a small renaming map.
run_probe stack_names_ports_probeScript.sml stack_names_ports_probe.out \
  ri_reg compile_map_fst_src \
  "$cake_dir/compiler/backend/stack_namesScript.sml" \
  "$cake_dir/compiler/backend"

# The stack_remove make_init probe observes the state-free prerequisites used by
# init_reduce / init_prop: is_SOME_Word, read_mem (and its LENGTH) and the
# addresses set with its membership characterization.
run_probe stack_remove_init_probeScript.sml stack_remove_init_probe.out \
  is_word_some in_addr_out \
  "$cake_dir/compiler/backend/proofs/stack_removeProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

# The word_loc probe pins the exact width-indexed HOL stackLang word_loc
# datatype (Word ('a word) | Loc num num) used by StackRemove.
run_probe word_lang_word_loc_probeScript.sml word_lang_word_loc_probe.out \
  wl_word wl_match \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend"

# The stack_remove value-helper probe pins max_stack_alloc, word_offset (8/64),
# store_list (length/head/last), store_length and stack_err_lab from the
# stack_remove compiler script.
run_probe stack_remove_helpers_probeScript.sml stack_remove_helpers_probe.out \
  max_stack_alloc stack_err_lab \
  "$cake_dir/compiler/backend/stack_removeScript.sml" \
  "$cake_dir/compiler/backend"

# The stackLang instruction-overload probe pins left_shift_inst,
# right_shift_inst, const_inst, load_inst, store_inst (stackLangScript.sml:80-84)
# and halt_inst (stack_removeScript.sml:58) against explicit constructor terms.
run_probe stack_lang_inst_overloads_probeScript.sml stack_lang_inst_overloads_probe.out \
  left_shift_inst_2_3 halt_inst_0 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" \
  "$cake_dir/compiler/backend"

# The mlstring carrier probe pins the exact HOL `mlstring = implode string`
# datatype (string = char list, char the 256-element type) needed by the
# stackLang/stack_names program FFI field.
run_probe mlstring_carrier_probeScript.sml mlstring_carrier_probe.out \
  ml_strlen ml_concat_len \
  "$cake_dir/basis/pure/mlstringScript.sml" \
  "$cake_dir/basis/pure"

# The loopSem state-carrier probe pins the exact field shapes of a concrete
# (8,'ffi) loopSem$state: num_map locals/code, total memory, set domain, clock, be.
run_probe loop_sem_state_carrier_probeScript.sml loop_sem_state_carrier_probe.out \
  locals_0 base_self \
  "$cake_dir/pancake/semantics/loopSemScript.sml" \
  "$cake_dir/pancake/semantics"

# The stackLang prog-carrier probe pins the exact `prog` datatype FFI field
# (mlstring) and representative constructor shapes at word type 64.
run_probe stack_lang_prog_carrier_probeScript.sml stack_lang_prog_carrier_probe.out \
  pg_skip pg_ffi_eq \
  "$cake_dir/compiler/backend/stackLangScript.sml" \
  "$cake_dir/compiler/backend"

# The panLang shape probe pins the exact `panLang$shape` name field as
# `mlstring` via `shape_to_str` (Named nm returns nm), plus constructor
# equality and arity.
run_probe pan_lang_shape_probeScript.sml pan_lang_shape_probe.out \
  shp_one_str shp_comb_len \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The loopLang exp/loop_arith probe pins the exact constructor and field shapes
# of the faithful width-indexed carriers HolLoopExp/LoopArith.
run_probe loop_lang_exp_probeScript.sml loop_lang_exp_probe.out \
  exp_const arith_div \
  "$cake_dir/pancake/loopLangScript.sml" \
  "$cake_dir/pancake"

# The loopLang prog probe records HOL constructor outputs for comparison with
# the untagged finite-map approximation (which is not an exact num_set port).
run_probe loop_lang_prog_probeScript.sml loop_lang_prog_probe.out \
  prog_skip prog_ffi \
  "$cake_dir/pancake/loopLangScript.sml" \
  "$cake_dir/pancake"

# The panLang exp probe pins the `exp` word payload (`Const`), its `mlstring`
# identifier fields, and representative constructor arities at word type 64.
run_probe pan_lang_exp_probeScript.sml pan_lang_exp_probe.out \
  ex_const ex_nstruct_fields ex_bytesinword \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"
run_probe sptree_set_ops_probeScript.sml sptree_set_ops_probe.out \
  union_keys oel_miss \
  "$cake_dir/compiler/backend/backend_commonScript.sml" \
  "$cake_dir/compiler/backend"
run_probe sptree_difference_probeScript.sml sptree_difference_probe.out \
  difference_ln_bs difference_bs_bs_collapse \
  "$hol_dir/src/finite_maps/sptreeScript.sml" \
  "$hol_dir/src/finite_maps"
# Mixed-payload oracle for the heterogeneous HOL sptree$inter used by loopSem
# cut_state (flapjack-pxgp.2.1): the result keeps the left operand's values.
run_probe sptree_inter_mixed_probeScript.sml sptree_inter_mixed_probe.out \
  inter_mixed_keys inter_mixed_disjoint \
  "$cake_dir/pancake/loop_liveScript.sml" \
  "$cake_dir/pancake"
# The num_set/spt probe observes the exact HOL sptree lookup/insert/wf/isEmpty
# behaviour for the unit-spt carrier used as num_set.
run_probe num_set_spt_probeScript.sml num_set_spt_probe.out \
  lookup_ln insert_ovw \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# The panLang prog probe pins the `prog` constructor arities, the `mlstring`
# identifier fields, and the word-indexed exp payloads at word type 64.
run_probe pan_lang_prog_probeScript.sml pan_lang_prog_probe.out \
  pg_skip pg_annot_len \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The num_set toAList probe observes the exact HOL sptree enumeration order
# (mixed order, but deterministic).
run_probe num_set_to_alist_probeScript.sml num_set_to_alist_probe.out \
  toalist_ln toalist_four \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"
# The panLang decl probe pins the `fun_decl` / `decl` / `struct_info` field
# shapes (mlstring names, bool flags, param lists, record size) at word type 64.
run_probe pan_lang_decl_probeScript.sml pan_lang_decl_probe.out \
  fd_name_len si_size \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The word_to_stack copy_ret_aux/copy_ret probe pins the return-slot copy
# fragments (list_Seq of StackLoad/StackStore, SeqStackFree) at word type 64.
run_probe word_to_stack_copy_ret_probeScript.sml word_to_stack_copy_ret_probe.out \
  cra_zero cr_handle \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

# The panLexer byte probe observes the original lexer's ASCII-only identifier
# predicates (HOL char is 8-bit; bytes >= 128 are not alpha/digit).
run_probe pan_lexer_bytes_probeScript.sml pan_lexer_bytes_probe.out \
  plx_alpha_206 plx_ascii_then_high \
  "$cake_dir/pancake/parser/panLexerScript.sml" \
  "$cake_dir/pancake/parser"
# The get_keyword probe pins the original keyword table for every entry plus
# the empty / foreign / plain-identifier fallbacks.
run_probe pan_lexer_get_keyword_probeScript.sml pan_lexer_get_keyword_probe.out \
  gk_skip gk_done \
  "$cake_dir/pancake/parser/panLexerScript.sml" \
  "$cake_dir/pancake/parser"
# The ffi_state carrier probe observes the exact HOL ffi datatype shapes,
# initial_ffi_state and the call_FFI cases (identity, success, length
# failure, oracle final).
run_probe ffi_state_carrier_probeScript.sml ffi_state_carrier_probe.out \
  ffi_outcome_failed call_shmem_final_event \
  "$cake_dir/semantics/ffi/ffiScript.sml" \
  "$cake_dir/semantics/ffi"

# The crepLang exp probe observes the exact width-indexed Crepe expression
# carrier (word payloads and fixed 5-word LoadGlob width).
run_probe crep_lang_exp_probeScript.sml crep_lang_exp_probe.out \
  cexp_const cexp_topaddr \
  "$cake_dir/pancake/crepLangScript.sml" \
  "$cake_dir/pancake"

# The crepLang prog probe observes the exact width-indexed Crepe program
# carrier (MlString Call/ExtCall names, word payloads, fixed 5-word StoreGlob).
run_probe crep_lang_prog_probeScript.sml crep_lang_prog_probe.out \
  prg_skip prg_tick \
  "$cake_dir/pancake/crepLangScript.sml" \
  "$cake_dir/pancake"

run_probe pan_lang_size_of_sh_with_ctxt_probeScript.sml pan_lang_size_of_sh_with_ctxt_probe.out \
  sswc_one sswc_comb_miss \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The mem_load probe observes the exact HOL mem_load over the faithful carriers.
run_probe pan_sem_mem_load_exact_probeScript.sml pan_sem_mem_load_exact_probe.out \
  ml_one_hit ml_comb_offset \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The size_of_shape probe observes the exact context-free HOL size_of_shape.
run_probe pan_lang_size_of_shape_probeScript.sml pan_lang_size_of_shape_probe.out \
  ss_one ss_eq \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The is_wf_shape probe observes is_wf_shape/is_wf_flds/is_wf_ctxt over the
# exact MlString-keyed context, including the duplicate-name and missing-field
# rejections.
run_probe pan_lang_is_wf_shape_probeScript.sml pan_lang_is_wf_shape_probe.out \
  iwf_one iwf_ctxt_field_miss \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The shape_of probe observes the total HOL shape_of over panSem$v.
run_probe pan_sem_shape_of_probeScript.sml pan_sem_shape_of_probe.out \
  so_valword so_wordlab \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The isValWord probe observes the exact boolean `panSem$isValWord` on
# Val/RStruct/NStruct and on the raw Word payload.
run_probe pan_sem_is_val_word_probeScript.sml pan_sem_is_val_word_probe.out \
  is_valword_val is_valword_wordlab \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The empty_locals probe observes the exact `panSem$empty_locals` state update:
# the locals map is cleared while other fields are preserved.
run_probe pan_sem_empty_locals_probeScript.sml pan_sem_empty_locals_probe.out \
  el_lookup el_globals \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The mem_store_32 probe observes the exact four-byte replacement (little and
# big endian), plus the unaligned and out-of-domain NONE cases.
run_probe pan_sem_mem_store_32_probeScript.sml pan_sem_mem_store_32_probe.out \
  ms32_aligned ms32_other_cell \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The result probe observes the exact panSem result constructor shapes.
run_probe pan_sem_result_probeScript.sml pan_sem_result_probe.out \
  res_error res_distinct \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The panSem mem_store/mem_stores probe observes in-domain replacement, pointwise
# preservation of other cells, out-of-domain failure, the bytes_in_word stride (8w
# for 64-bit words), the empty list, and a later-list store failure.
run_probe pan_sem_mem_store_probeScript.sml pan_sem_mem_store_probe.out \
  ms_hit_lookup mss_second_miss \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The shared-memory probe observes panSem `sh_mem_load`/`sh_mem_store`:
# nb = 0 in/out of `sh_memaddrs`, byte-aligned nb = 1, an FFI_final outcome
# clearing locals, and the FFI_return event/state update for both primitives.
run_probe pan_sem_sh_mem_probeScript.sml pan_sem_sh_mem_probe.out \
  l_load_hit_local l_store_final_unchanged \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The declaration-context probe observes panSem `decs_stcnames`: the empty
# context, a well-formed structure, its computed size, duplicate names,
# duplicate field names, an unknown `Named` shape, and skipped decl forms.
run_probe pan_sem_decs_stcnames_probeScript.sml pan_sem_decs_stcnames_probe.out \
  dsc_empty dsc_skip_len \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The panProps shape_of_val / res_var FLOOKUP probe observes the exact HOL
# shape_of on the Val (word_lab) constructor and the res_var finite-map
# update/delete semantics (panPropsScript.sml:14, :220, :228, :236).
run_probe pan_props_shape_res_var_probeScript.sml pan_props_shape_res_var_probe.out \
  spv_one rv_some \
  "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_commonProps zip/fupdate and disjoint take/drop probe observes the
# finite-map update-not-mem and list-disjointness lemmas
# (pan_commonPropsScript.sml:289, :399, :413).
run_probe pan_common_props_zip_disjoint_probeScript.sml pan_common_props_zip_disjoint_probe.out \
  fzn_notmem ddt_disjoint \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The crepProps assigned_vars / var_cexp probe observes the nested_decs append,
# stores emptiness, and load_shape EXACT lemmas
# (crepPropsScript.sml:390, :400, :429, :439, :215).
run_probe crep_props_assigned_vars_probeScript.sml crep_props_assigned_vars_probe.out \
  avnda vels \
  "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_commonProps fm_update_diff_vars probe observes that updating a finite
# map at `a`, then a distinct `b`, then `a`, then `b` collapses to one update
# at each key (pan_commonPropsScript.sml:780).
run_probe pan_common_props_fm_update_diff_vars_probeScript.sml pan_common_props_fm_update_diff_vars_probe.out \
  fmdv_eq_1 fmdv_lhs_absent \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The panProps size_of_sh_with_ctxt_eq probe observes that a context-free
# well-formed shape has the same with-context size as its plain size_of_shape
# size (panPropsScript.sml:184, using panLang size_of_sh_with_ctxt/size_of_shape).
run_probe pan_props_size_with_ctxt_probeScript.sml pan_props_size_with_ctxt_probe.out \
  ssc_one ssc_eq_nested \
  "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The panSem vshapes_args_rel_imp_eq_len_MAP probe observes the exact
# LIST_REL (λvshape arg. SND vshape = shape_of arg) vshapes args relation and
# its LENGTH / MAP SND / MAP shape_of consequences (panSemScript.sml:740).
run_probe pan_sem_vshapes_args_rel_probeScript.sml pan_sem_vshapes_args_rel_probe.out \
  vra_one vra_map_two \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_commonProps take/drop disjoint, EL disjoint, and empty zip lookup
# probe observes pan_commonPropsScript.sml:534, :606, and :575.
run_probe pan_common_props_take_drop_el_zip_probeScript.sml pan_common_props_take_drop_el_zip_probe.out \
  atdd_disjoint nmfz_hit \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The panProps length_flatten_eq_size_of_shape probe observes that under the
# empty-constructor context the flattened length of a well-formed value equals
# its shape size (panPropsScript.sml:171).
run_probe pan_props_length_flatten_probeScript.sml pan_props_length_flatten_probe.out \
  lfs_val lfs_wf_nested \
  "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_to_crep is_wf_shape_nil_length_flatten probe observes the exact
# flatten/size_of_shape relationship under the empty constructor context
# (pan_to_crepProofScript.sml:2469).
run_probe pan_to_crep_is_wf_shape_nil_probeScript.sml pan_to_crep_is_wf_shape_nil_probe.out \
  iwf_val iwf_wf_struct \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"

# The pan_globals fresh_name probe observes that the source-shaped fresh-name
# search only ever appends apostrophes (pan_globalsScript.sml:55).
run_probe pan_globals_fresh_name_probeScript.sml pan_globals_fresh_name_probe.out \
  empty absent \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals new_main_name probe observes the synthesized entry-point name
# for representative declaration lists (pan_globalsScript.sml:224).
run_probe pan_globals_new_main_name_probeScript.sml pan_globals_new_main_name_probe.out \
  empty absent \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals fperm_name probe observes the source-shape name permutation
# `fperm_name f g h` (pan_globalsScript.sml:185-188) for unchanged and
# colliding keys, including names that already carry apostrophes.
run_probe pan_globals_fperm_name_probeScript.sml pan_globals_fperm_name_probe.out \
  source_collision fperm_name_done \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

run_probe wordlang_max_var_probeScript.sml wordlang_max_var_probe.out \
  mv_skip mv_move mv_move_empty mv_inst64 mv_inst32 mv_assign mv_get mv_store mv_tail_ignored mv_tail_empty mv_call_body mv_call_cutset mv_call_values mv_handler_value mv_handler_body mv_seq mv_must mv_if_reg mv_if_imm mv_alloc mv_consts mv_install mv_codewrite mv_datawrite mv_ffi mv_raise mv_heap mv_return mv_return_empty mv_tick mv_loc mv_set mv_share mv_loop_exit mv_loop_body mv_break mv_continue \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe wordlang_cutsets_max_probeScript.sml wordlang_cutsets_max_probe.out \
  cm_empty cm_left cm_right cm_both cm_zero cm_nonwf cm_raw cm_deep \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe wordlang_max_var_inst_probeScript.sml wordlang_max_var_inst_probe.out \
  mi_skip mi_const mi_binop_reg mi_binop_imm mi_shift_reg mi_shift_imm mi_div mi_addCarry mi_addOverflow mi_subOverflow mi_longMul mi_longdiv mi_load mi_store mi_load32 mi_store32 mi_load8 mi_store8 mi_fpLess mi_fpLessEqual mi_fpEqual mi_toreg64 mi_fromreg64 mi_toreg32 mi_fromreg32 mi_fpdefault \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_comp_native_probeScript.sml word_to_stack_comp_native_probe.out \
  comp_skip comp_must comp_seq comp_loop comp_return comp_raise comp_set_bitmap comp_set_bad comp_assign_fallback comp_install comp_tailcall comp_share_bad comp_if_valid comp_if_materialize comp_returning comp_handler comp_seq_bitmaps comp_if_bitmaps comp_call_bitmaps \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_handler_probeScript.sml word_to_stack_handler_probe.out \
  shaF pop_eq "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

run_probe word_to_stack_call_dest_probeScript.sml word_to_stack_call_dest_probe.out \
  cd_some wl_store "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
# The pan_globals fperm probe observes the source-shape program permutation
# `fperm f g p` (pan_globalsScript.sml:191-214) for the recursive control
# constructs, the Call handler case, the DecCall case and the catch-all.
run_probe pan_globals_fperm_probeScript.sml pan_globals_fperm_probe.out \
  recursive_control fperm_done \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals fperm_decs probe observes the source-shape declaration-list
# permutation `fperm_decs f g ds` (pan_globalsScript.sml:216-221) for a mixed
# declaration list and the empty list.
run_probe pan_globals_fperm_decs_probeScript.sml pan_globals_fperm_decs_probe.out \
  mixed singleton_nonfunction \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals resort_decls probe observes the declaration regrouping
# `resort_decls ds` (pan_globalsScript.sml:179-182) for a mixed list, an
# already-grouped list, and the empty list.
run_probe pan_globals_resort_decls_probeScript.sml pan_globals_resort_decls_probe.out \
  mixed empty \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals dec_shapes probe observes the shape projection
# `dec_shapes ds` (pan_globalsScript.sml:228-233) for the empty list, a mixed
# list, and a function-only list.
run_probe pan_globals_dec_shapes_probeScript.sml pan_globals_dec_shapes_probe.out \
  empty functions_only \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals MEM_functions probe observes the source-shape membership
# projection described by the local theorem MEM_functions
# (pan_globalsProofScript.sml:2380-2387).  Since `[local]` theorems are not
# exported to the theory database, the probe records the direct EVAL rows for
# `functions` and the membership instance the theorem characterizes.
run_probe pan_globals_mem_functions_probeScript.sml pan_globals_mem_functions_probe.out \
  functions_empty mem_function_entry \
  "$cake_dir/pancake/proofs/pan_globalsProofScript.sml" \
  "$cake_dir/pancake/proofs"

run_probe word_to_stack_stub_probeScript.sml word_to_stack_stub_probe.out \
  pcp_eq pcp_top "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

# The word_to_stack wShareInst probe observes the shared-memory instruction
# helper `wShareInst` (word_to_stackScript.sml:186-224) for all eight memop
# forms at word type 64.
run_probe word_to_stack_wshareinst_probeScript.sml word_to_stack_wshareinst_probe.out \
  ws_load ws_store32 "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

# The pan_commonProps genlist probe observes `mem_genlist_add_suc_val`
# (pan_commonPropsScript.sml:234): membership in `GENLIST (fun x. SUC x + k) n`
# implies the value lies in `(k, n + k]`.
run_probe pan_common_props_genlist_probeScript.sml pan_common_props_genlist_probe.out \
  genlist_mem_3 genlist_mem_0 genlist_mem_6 genlist_done \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The external HOL finite_map theory theorem used in pc_compile_correct.
# Unlike CakeML sources, this is deliberately rooted at the separate HOL
# checkout; check-hol-refs.py currently cannot encode such a path.
run_probe fupdate_list_append_commutes_probeScript.sml fupdate_list_append_commutes_probe.out \
  source_theorem overlap_lookup_equal \
  "$hol_dir/src/finite_maps/finite_mapScript.sml" \
  "$hol_dir/src/finite_maps"

# The crepSem evaluate_ind statement is auto-generated by HOL's tdefn (not
# textually present in crepSemScript.sml), so its exact shape is captured here
# for the faithful Lean port (bead flapjack-2de.1.1 / flapjack-2de.1.1.1).
run_probe crep_sem_evaluate_ind_probeScript.sml crep_sem_evaluate_ind_probe.out \
  evaluate_ind "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"

# The proof-script-local crep_arith `sh_mem_op_code` (crep_arithProofScript.sml
# :173-180) commutes the local `mapc` code rewrite with `sh_mem_op`; `mapc` is
# a proof-script `[local]` Overload, so the probe inlines it.  Rows pin the
# shared-memory domain to the empty set so the domain checks decide.
run_probe crep_arith_sh_mem_op_code_probeScript.sml crep_arith_sh_mem_op_code_probe.out \
  sh_mem_op_code_code sh_mem_op_code_load_err sh_mem_op_code_store_err \
  sh_mem_op_code_load8_err sh_mem_op_code_store8_err sh_mem_op_code_load16_err \
  sh_mem_op_code_store16_err sh_mem_op_code_load32_err sh_mem_op_code_store32_err \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" "$cake_dir/pancake/proofs"

# The StoreGlob case of crep_arithProofScript.sml:184-212 `simp_prog_correct`.
# HOL `simp_prog (StoreGlob g exp) = StoreGlob g (simp_exp exp)` and
# `evaluate (StoreGlob dst src, s)` evaluate only `src` into
# `(NONE, set_globals dst w s)` (or `(SOME Error, s)`); the local `mapc`
# overload is inlined, and `storeglob_mapc_commute` pins the code-only `mapc`
# commutation with `set_globals`.
run_probe crep_arith_store_glob_probeScript.sml crep_arith_store_glob_probe.out \
  simp_prog_storeglob evaluate_storeglob_const evaluate_storeglob_mapc \
  storeglob_mapc_commute evaluate_storeglob_missing_var \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" "$cake_dir/pancake/proofs"

# The Store32 case of crep_arithProofScript.sml:184-212 `simp_prog_correct`.
# HOL `simp_prog (Store32 exp1 exp2) = Store32 (simp_exp exp1) (simp_exp exp2)`
# and `evaluate (Store32 dst src, s)` evaluate both operands into
# `(NONE, s with memory := m)` through `mem_store_32` (or `(SOME Error, s)`);
# the local `mapc` overload is inlined, and `store32_mapc_commute` pins the
# code-only `mapc` commutation with the `memory` update.  The domain, alignment
# and failed-operand rows pin the non-`Error` premise's failure branches.
run_probe crep_arith_store_32_probeScript.sml crep_arith_store_32_probe.out \
  simp_prog_store32 evaluate_store32_const evaluate_store32_mapc \
  store32_mapc_commute evaluate_store32_domain_error \
  evaluate_store32_unaligned_error evaluate_store32_missing_var \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" "$cake_dir/pancake/proofs"

# The If case of crep_arithProofScript.sml:184-212 `simp_prog_correct`.
# HOL `simp_prog (If exp c1 c2) = If (simp_exp exp) (simp_prog c1)
# (simp_prog c2)` and `evaluate (If e c1 c2,s)` selects `c1`/`c2` from the
# condition word (`(SOME (Word w), if w <> 0w ...)`) or errors; the local
# `mapc` overload is inlined, and `if_mapc_commute` pins the code-only `mapc`
# commutation with the selected branch update.  Both guard values and the
# error branch are exercised.
run_probe crep_arith_if_probeScript.sml crep_arith_if_probe.out \
  simp_prog_if evaluate_if_true evaluate_if_true_state evaluate_if_false \
  evaluate_if_false_state evaluate_if_error if_mapc_true if_mapc_commute \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" "$cake_dir/pancake/proofs"

# The StoreByte case of crep_arithProofScript.sml:184-212 `simp_prog_correct`.
# HOL `simp_prog (StoreByte dst src) = StoreByte (simp_exp dst) (simp_exp src)`
# and `evaluate (StoreByte dst src, s)` evaluates both operands and stores the
# low byte through `mem_store_byte` (`(NONE, s with memory := m)`, or
# `(SOME Error, s)`); the local `mapc` overload is inlined.
run_probe crep_arith_store_byte_probeScript.sml crep_arith_store_byte_probe.out \
  simp_prog_storebyte evaluate_storebyte_success_result \
  evaluate_storebyte_mapc_success_result evaluate_storebyte_error_domain \
  evaluate_storebyte_mapc_error_domain evaluate_storebyte_missing_var \
  storebyte_memory_mapc \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" "$cake_dir/pancake/proofs"

# The ExtCall case of crep_arithProofScript.sml:184-212 `simp_prog_correct`.
# HOL `simp_prog` leaves an `ExtCall` unchanged (catch-all), and
# `evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s)` reads four locals and
# calls `call_FFI` (crepSemScript.sml:367-379); the missing-locals branch is
# `(SOME Error, s)`.  The local `mapc` overload is inlined.
run_probe crep_arith_ext_call_probeScript.sml crep_arith_ext_call_probe.out \
  simp_prog_extcall extcall_mapcs_code \
  evaluate_extcall_missing_locals evaluate_extcall_mapc_missing_locals \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" "$cake_dir/pancake/proofs"

# The loopSem evaluate_ind statement (rebound through fix_clock_evaluate at
# loopSemScript.sml:497) is likewise tdefn-generated; capture it for the exact
# Lean port used by loop_liveProof compile_correct's `recInduct evaluate_ind`.
run_probe loop_sem_evaluate_ind_probeScript.sml loop_sem_evaluate_ind_probe.out \
  evaluate_ind "$cake_dir/pancake/semantics/loopSemScript.sml"

# The PanSem evaluate_ind Call conjunct is generated by HOL's tdefn. Capture
# its exact recursive IH binders and side conditions for source review.
run_probe pan_sem_evaluate_ind_probeScript.sml pan_sem_evaluate_ind_probe.out \
  evaluate_ind "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"

# The expression-level panSem eval_ind principle is tdefn-generated; capture its
# exact recursive IH binders (e.g. the Load shape-wf guard) for source review.
run_probe pan_sem_eval_ind_probeScript.sml pan_sem_eval_ind_probe.out \
  eval_ind "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"

run_probe word_alloc_key_map_probeScript.sml word_alloc_key_map_probe.out \
  key_map_mixed key_map_collision key_map_done \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

# HOL's byte decoder `word_of_bytes` (HOL/src/n-bit/byteScript.sml:197) is the
# function installed by the exact shared-memory loads (panSemScript.sml:517/524,
# crepSemScript.sml) as `word_of_bytes F 0w new_bytes`, with no length premise
# on the FFI-returned `new_bytes`.  The first list byte is written outermost at
# address 0. At widths >= 8 only the first `dimindex DIV 8` bytes survive; for
# sub-byte widths the initial write retains the available low bits. Like the
# fupdate_list_append_commutes_probe, this
# is rooted at the separate HOL checkout; byteTheory is a standard HOL theory.
run_probe pan_word_of_bytes_overlong_probeScript.sml pan_word_of_bytes_overlong_probe.out \
  source_def w8_overlong_three w8_overlong_take_one w16_overlong_three \
  w16_overlong_sum w16_overlong_take_two w64_overlong_ten \
  w64_overlong_take_eight w64_discarded_bytes_irrelevant \
  w9_overlong_two w9_overlong_three w9_overlong_take_one w12_overlong_four \
  w1_overlong_three w7_overlong_three w7_first_byte_truncates done \
  "$hol_dir/src/n-bit/byteScript.sml" \
  "$hol_dir/src/n-bit"

run_probe stack_props_fixed_names_probeScript.sml stack_props_fixed_names_probe.out \
  x86_good x86_empty x86_bad_zero riscv_empty "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe pan_globals_block_alignment_probeScript.sml pan_globals_block_alignment_probe.out \
  block32 wrap32 zero32 unaligned32 block64 wrap64 zero64 unaligned64 \
  "$hol_dir/src/n-bit/alignmentScript.sml" "$cake_dir/pancake"

run_probe stacksem_loc_value_probeScript.sml stacksem_loc_value_probe.out \
  loc_zero_present loc_zero_absent loc_nonzero_present loc_handler_present loc_handler_no_return loc_disabled_stack \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stacksem_dynamic_stack_probeScript.sml stacksem_dynamic_stack_probe.out \
  any_load_disabled any_load_loc any_load_alias any_load_missing any_load_offset_loc any_load_unaligned any_load_boundary any_load_space any_store_loc any_store_alias any_store_missing any_store_offset_missing any_store_offset_loc any_store_unaligned any_store_boundary any_store_disabled any_load_width32 any_load_width64 any_load_width1_zero any_load_width1_nonzero \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stacksem_size_bitmap_probeScript.sml stacksem_size_bitmap_probe.out \
  size_disabled size_success size_boundary size_loc size_missing bitmap_disabled bitmap_success bitmap_boundary bitmap_loc bitmap_missing bitmap_alias \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" \
  "$cake_dir/compiler/backend/semantics"

run_probe stacksem_fixed_stack_probeScript.sml stacksem_fixed_stack_probe.out \
  stack_alloc_disabled stack_alloc_success stack_alloc_boundary stack_alloc_exhausted stack_free_boundary stack_free_excess stack_free_disabled stack_load_loc stack_load_boundary stack_load_disabled stack_store_loc stack_store_missing stack_store_boundary stack_store_disabled stack_size_modular stack_size_disabled stack_size_unsigned \
  "$cake_dir/compiler/backend/semantics/stackSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stack_names_operand_probeScript.sml stack_names_operand_probe.out \
  reg_present reg_missing imm dest_present dest_missing dest_label "$cake_dir/compiler/backend/stack_namesScript.sml" "$cake_dir/compiler/backend"

run_probe stack_names_instruction_probeScript.sml stack_names_instruction_probe.out \
  skip const binop shift div longmul longdiv addcarry addoverflow suboverflow mem fpless fplesseq fpeq fptoreg fpfromreg fpdefault \
  "$cake_dir/compiler/backend/stack_namesScript.sml" "$cake_dir/compiler/backend"

run_probe stack_names_program_probeScript.sml stack_names_program_probe.out \
  seq if loop call_none call_ret call_exc call_both install shared buffer jump loc continue default compile "$cake_dir/compiler/backend/stack_namesScript.sml" "$cake_dir/compiler/backend"

run_probe riscv_names_tlookup_probeScript.sml riscv_names_tlookup_probe.out \
  names "$cake_dir/compiler/backend/riscv/riscv_configScript.sml" "$cake_dir/compiler/backend/riscv"

run_probe stack_props_arith_name_probeScript.sml stack_props_arith_name_probe.out \
  or_exception or_wrong binop_two binop_same imm_valid shift_zero_lsl shift_zero_lsr shift_width shift_x86_4 shift_x86_1 div_riscv div_x86 mul_x86_3 mul_x86_2 mul_arm_alias mul_riscv_alias longdiv_3 longdiv_2 carry_good carry_alias addoverflow_right_alias suboverflow_left_alias "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_addr_name_probeScript.sml stack_props_addr_name_probe.out \
  word_min word_max word_low word_high half_min half_max half_high half_ag32 byte_zero byte_high reg_last reg_bound "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_fp_name_probeScript.sml stack_props_fp_name_probe.out \
  fpLess fpLessEqual fpEqual fpAbs fpAbs_alias fpNeg fpNeg_alias fpSqrt fpMov fpToInt fpFromInt fpAdd fpSub fpMul fpDiv binary_mismatch binary_three_reg fma_arm fma_riscv fma_count2 fpMovToReg_32 fpMovFromReg_32 move32_alias move32_bound move64_ignored fp_bound logical_bound "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_inst_name_probeScript.sml stack_props_inst_name_probe.out \
  skip const_last const_bound mem_good mem_destination mem_base arith_good arith_bad fp_good fp_alias "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe word_simp_smartseq_probeScript.sml word_simp_smartseq_probe.out \
  skip_left skip_right labels_skip_left labels_call_left labels_both labels_seq "$cake_dir/compiler/backend/word_simpScript.sml" "$cake_dir/compiler/backend"

run_probe stack_props_remove_name_probeScript.sml stack_props_remove_name_probe.out \
  get_last get_bound set store_ignored_second store_first_bad load_ignored_second load_first_bad get_size set_size_bad heap store_any_bad load_any bitmap_bad consts seq_bad if_ignored_condition loop_bad call_none_ignored call_body_bad call_handler_bad call_both_good inst_ignored "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_alloc_arg_probeScript.sml stack_props_alloc_arg_probe.out \
  one zero two seq_good seq_bad if_good if_bad loop_good loop_bad call_none call_none_handler_bad call_return_bad call_handler_bad call_good inst_default \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_program_name_probeScript.sml stack_props_program_name_probe.out \
  inst_good inst_bad heap_alias heap_distinct code_good code_bad data_bad seq_bad if_ignored loop_bad raise_good return_bad call_direct call_indirect_bad call_none_handler_ignored call_body_bad call_handler_bad call_good alloc_default shared_good shared_register_bad shared_base_bad shared_offset_bad "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_program_validity_probeScript.sml stack_props_program_validity_probe.out \
  inst_good inst_avoided inst_bound code_good code_avoided code_bound data_default heap_default seq_bad if_ignored loop_bad raise_good return_bad call_direct call_indirect_avoided call_indirect_bound call_handler_ignored call_body_bad call_handler_bad call_good shared_good shared_register_bad shared_base_bad shared_offset_bad "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_alloc_get_live_probeScript.sml word_alloc_get_live_probe.out \
  get_live_store_consts get_live_break_outside get_live_return \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
# The word_to_stack wInst probe observes the instruction helper `wInst`
# (word_to_stackScript.sml:88-175), including the width-64 FP move clauses and
# the Load16/Store16 Skip catch-all.
run_probe word_to_stack_winst_probeScript.sml word_to_stack_winst_probe.out \
  wi_const wi_binop_imm wi_binop_reg wi_div wi_addcarry wi_longmul wi_longdiv \
  wi_load16_skip wi_store wi_fpless wi_fpmovtoreg wi_fpmovfromreg wi_fpadd wi_skip \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

run_probe parmove_fstep_probeScript.sml parmove_fstep_probe.out \
  fs_final fs_self fs_start fs_first fs_single fs_chain fs_cycle fs_cycle_long fs_temp_match fs_temp_self \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"


run_probe word_alloc_get_writes_inst_probeScript.sml word_alloc_get_writes_inst_probe.out \
  writes_const writes_add_carry writes_long_div writes_load16_catchall writes_fp_move64 writes_fp_move32 writes_fp_from_reg_catchall \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_get_delta_inst_probeScript.sml word_alloc_get_delta_inst_probe.out \
  gdi_skip gdi_const gdi_binop_reg gdi_binop_imm gdi_shift_reg gdi_shift_imm gdi_div gdi_addcarry gdi_addoverflow gdi_suboverflow gdi_longmul gdi_longdiv gdi_load gdi_store gdi_load32 gdi_store32 gdi_load8 gdi_store8 gdi_fpless gdi_fpmovtoreg64 gdi_fpmovtoreg32 gdi_fpmovfromreg64 gdi_fpmovfromreg32 gdi_fpneg_catchall \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_get_clash_tree_probeScript.sml word_alloc_get_clash_tree_probe.out \
  gct_skip gct_move gct_inst gct_assign gct_get gct_store gct_seq gct_if_reg gct_if_imm gct_mustterminate gct_alloc gct_install gct_codebufferwrite gct_databufferwrite gct_ffi gct_raise gct_return gct_tick gct_locvalue gct_set gct_opcurrheap gct_storeconsts gct_shareinst_store gct_shareinst_other gct_loop gct_break_none gct_break_some gct_continue_none gct_continue_some gct_call_none gct_call_ret gct_call_ret_handler \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_get_writes_probeScript.sml word_alloc_get_writes_probe.out \
  writes_move writes_store_consts writes_inst_load16 writes_shared_load16 writes_shared_store16 writes_seq_catchall writes_install \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_stack_size_rel_probeScript.sml word_to_stack_stack_size_rel_probe.out \
  ss_none ss_some ss_bad_max ss_missing_loc ss_missing_frame ss_frame_guard ss_target_bool ss_target_nat \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe target_sem_encoded_bytes_probeScript.sml target_sem_encoded_bytes_probe.out \
  oracle_first oracle_shift bytes_empty bytes_nonempty bytes_domain_fail bytes_wrap \
  encoded_drop encoded_guard_true encoded_guard_strict encoded_bytes_match encoded_bytes_in_mem_whole \
  "$cake_dir/compiler/backend/semantics/targetSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe misc_asm_write_bytearray_probeScript.sml misc_asm_write_bytearray_probe.out \
  wa_empty wa_wrap0 wa_wrap1 wa_wrap255 \
  "$cake_dir/misc/miscScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_lang_occurrences_exact_probeScript.sml word_lang_occurrences_exact_probe.out \
  name_empty name_even name_odd var_move_even var_move_odd var_loop_live stack_loop_live stack_alloc_odd var_call_none stack_call_none var_call_some stack_call_some \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_frames_probeScript.sml word_to_stack_frames_probe.out \
  hv_empty hv_plain hv_handler hf_none hf_some se_empty se_desc se_equal se_asc \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_abs_stack_probeScript.sml word_to_stack_abs_stack_probe.out \
  as_base as_base_bad as_plain as_bitmap_bad as_len_bad as_short as_rest_bad as_handler as_marker_bad as_handler_short as_lens_bad \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_index_list_probeScript.sml word_to_stack_index_list_probe.out \
  il_empty il_single il_desc an_even an_odd il_snd il_fst il_el_zero il_el_last \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe parmove_semantics_probeScript.sml parmove_semantics_probe.out \
  sem_windmill sem_repeated sem_parallel_swap1 sem_parallel_swap2 sem_sequential_swap2 sem_parallel_last sem_sequential_last sem_untouched sem_state_first sem_state_second sem_ignore_temp sem_real_difference \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_scheduler_probeScript.sml parmove_scheduler_probe.out \
  pm_final pm_temp_self pm_empty pm_self pm_single pm_chain pm_swap pm_cycle pm_repeated \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe reg_alloc_clash_tree_probeScript.sml reg_alloc_clash_tree_probe.out \
  delete_names col_collision partial_existing partial_collision delta_discard_writes seq_right_first branch_merge branch_fixed_collision \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe linear_scan_pure_defs_probeScript.sml linear_scan_pure_defs_probe.out \
  get_live_tree_branch_cut get_live_backward_branch fix_domination_reads fix_domination_writes check_live_tree_seq check_live_tree_collision check_live_tree_branch add_if_lt add_if_gt get_intervals_seq get_intervals_withlive_branch get_intervals_ct size_of_live_tree numset_list_insert_nottailrec numset_list_insert \
  "$cake_dir/compiler/backend/reg_alloc/linear_scanScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe linear_scan_pure_props_probeScript.sml linear_scan_pure_props_probe.out \
  cnp_writes cnp_signed_bound cnp_weak_branch cnp_strong_branch cnp_strong_seq_live startlive_ok startlive_ndef startlive_missing_end startlive_branch_numbers registers_mem registers_not_mem intersect_touch intersect_disjoint point_inside point_outside the_some check_intervals_missing_end check_intervals_clash \
  "$cake_dir/compiler/backend/reg_alloc/linear_scanScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe monad_arrays_probeScript.sml monad_arrays_probe.out \
  msub_hit msub_miss mupdate_hit mupdate_miss marray_length marray_sub_hit marray_sub_miss marray_update_hit marray_update_miss st_ex_map_ok st_ex_map_fail \
  "$cake_dir/translator/monadic/monad_base/ml_monadBaseScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe linear_scan_monad_probeScript.sml linear_scan_monad_probe.out \
  add_if_lt_monad add_if_gt_monad add_if_subscript intervals_ct_monad remove_inactive add_active find_color_in_list find_color_pool find_color_colornum spill color_phy color_virt find_last_stealable find_spill_steal find_spill_keep step_aux_pref step_aux_spill pass1_phy pass1_stack pass1_forced pass2_virt find_reg_exchange apply_reg_exchange foldl filter_good edges sort_moves_rev sort_regs sorted_regs_to_list list_to_sorted_regs sort_moves sorted_moves_to_list list_to_sorted_moves pass_init \
  "$cake_dir/compiler/backend/reg_alloc/linear_scanScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe linear_scan_generic_types_probeScript.sml linear_scan_generic_types_probe.out \
  check_col check_intervals colors_length int_beg_length int_end_length sorted_regs_length sorted_moves_length find_last_stealable run_i_linear_scan_hidden_state linear_reg_alloc_and_extract_coloration i_linear_scan_hidden_state_CASE \
  "$cake_dir/compiler/backend/reg_alloc/linear_scanScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe linear_scan_top_probeScript.sml linear_scan_top_probe.out \
  bijection_seq bijection_branch apply_bij_tree apply_bijection size_ct extract run_i run_i_fail lsra_delta lsra_moves lsra_forced lsra_branch_spill lsra_phys lsra_stack \
  "$cake_dir/compiler/backend/reg_alloc/linear_scanScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe labsem_updates_probeScript.sml labsem_updates_probe.out lab_updates_pc_overwrite lab_updates_pc_increment lab_updates_clock_zero lab_updates_clock_positive lab_updates_reg_hit lab_updates_reg_other lab_updates_reg_loc lab_updates_mem_hit lab_updates_mem_other lab_updates_assert_sticky lab_updates_assert_false lab_updates_failed_reg_write lab_updates_failed_mem_write lab_updates_reg_imm_loc lab_updates_reg_imm_word lab_updates_fp_hit lab_updates_fp_other "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe parmove_invariants_probeScript.sml parmove_invariants_probe.out \
  iv_empty_path iv_single_path iv_chain_path iv_bad_path iv_empty_wf iv_pending_wf iv_repeated iv_pending_dest iv_pending_source iv_active_last_temp iv_active_front_temp iv_active_dest iv_active_path \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe word_to_stack_map_fst_probeScript.sml word_to_stack_map_fst_probe.out \
  mf_empty mf_keys mf_collision mf_values \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_bitmap_append_probeScript.sml word_to_stack_bitmap_append_probe.out \
  ba_terminal ba_continuation ba_full_one ba_full_two \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_abs_stack_prefix_probeScript.sml word_to_stack_abs_stack_prefix_probe.out \
  ap_base ap_plain ap_handler ap_nested ap_mixed \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_abs_stack_lengths_probeScript.sml word_to_stack_abs_stack_lengths_probe.out \
  al_base al_plain al_handler al_nested al_mixed \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_wmove_probeScript.sml word_to_stack_wmove_probe.out \
  wm_empty wm_self wm_reg wm_load wm_store wm_spill wm_swap wm_spill_swap wm_odd wm_underflow wm_fprime \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe parmove_updates_probeScript.sml parmove_updates_probe.out \
  pu_fresh pu_snapshot pu_untouched pu_later_destination pu_freshness_boundary pu_empty pu_self pu_swap pu_eq_forward pu_eq_reverse \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe labsem_navigation_probeScript.sml labsem_navigation_probe.out nav_fetch0 nav_fetch1 nav_fetch2 nav_fetch3 nav_fetch4 nav_fetch_end nav_length nav_entry1 nav_entry2 nav_empty9 nav_empty8 nav_label5 nav_label7 nav_label4 nav_missing nav_missingsection nav_return0 nav_return1 nav_return2 nav_return3 nav_return4 nav_return5 nav_first_label "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"


run_probe parmove_path_probeScript.sml parmove_path_probe.out \
  pv_empty pv_single pv_chain pv_cycle pv_changed_dest pv_bad_prefix pv_windmill_empty pv_windmill_fresh pv_windmill_repeated pv_windmill_sources \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"


run_probe parmove_environment_probeScript.sml parmove_environment_probe.out \
  pe_first_written pe_second_written pe_first_untouched pe_second_untouched \
  pe_source_boundary pe_source_maps pe_empty pe_snapshot \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe labsem_arithmetic_probeScript.sml labsem_arithmetic_probe.out lab_arith_binop_add lab_arith_binop_sub lab_arith_binop_and lab_arith_binop_or lab_arith_binop_xor lab_arith_loc_or_self lab_arith_loc_or_other_reg lab_arith_loc_or_imm lab_arith_loc_add_self lab_arith_binop_right_loc lab_arith_lsl_valid lab_arith_lsl_invalid lab_arith_lsr_invalid lab_arith_asr_invalid lab_arith_ror_invalid lab_arith_shift_source_loc lab_arith_shift_amount_loc lab_arith_div_valid lab_arith_div_zero lab_arith_div_divisor_loc lab_arith_div_dividend_loc lab_arith_carry_nonzero lab_arith_carry_zero lab_arith_carry_flag_alias lab_arith_carry_loc lab_arith_longmul_valid lab_arith_longmul_dest_alias lab_arith_longmul_loc lab_arith_longdiv_valid lab_arith_longdiv_dest_alias lab_arith_longdiv_quotient_bound lab_arith_longdiv_zero lab_arith_longdiv_loc lab_arith_add_overflow lab_arith_add_no_overflow lab_arith_add_negative_overflow lab_arith_sub_overflow lab_arith_sub_negative_rhs_overflow lab_arith_sub_no_overflow lab_arith_addOverflow_flag_alias lab_arith_addOverflow_loc lab_arith_subOverflow_flag_alias lab_arith_subOverflow_loc lab_arith_sticky_failed "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_permutation_probeScript.sml parmove_permutation_probe.out \
  pp_first_one pp_second_one pp_first_three pp_second_three pp_first_four pp_second_four pp_duplicate_first pp_duplicate_second pp_swap pp_empty \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"


run_probe parmove_steps_probeScript.sml parmove_steps_probe.out \
  ps_remove ps_start ps_extend ps_save ps_emit_head ps_emit_last \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"


run_probe parmove_noread_probeScript.sml parmove_noread_probe.out \
  pn_duplicate_left pn_duplicate_right pn_untouched_left pn_untouched_right pn_boundary_left pn_boundary_right pn_self_left pn_self_right \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe labsem_fp_updates_probeScript.sml labsem_fp_updates_probe.out lab_fp_less_nan lab_fp_less_equal_zero lab_fp_equal_nan lab_fp_equal_zero lab_fp_mov_payload lab_fp_abs_payload lab_fp_neg_zero lab_fp_sqrt_four lab_fp_add_two lab_fp_sub_zero lab_fp_mul_four lab_fp_div_half lab_fp_fma_order lab_fp_to_reg64 lab_fp_to_reg_alias32 lab_fp_from_reg64 lab_fp_from_reg_loc_error lab_fp_from_reg32 lab_fp_from_reg8 lab_fp_to_int_tie_even lab_fp_to_int_negative lab_fp_to_int_overflow_bits lab_fp_to_int_overflow_failed lab_fp_to_int_inf_error lab_fp_to_int_odd32 lab_fp_from_int64 lab_fp_from_int32 lab_fp_from_int8 lab_fp_from_int128 "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_wf_steps_probeScript.sml parmove_wf_steps_probe.out \
  pw_remove_pre pw_remove_post pw_start_pre pw_start_post pw_extend_pre pw_extend_post pw_save_pre pw_save_post pw_emit_head_pre pw_emit_head_post pw_emit_last_pre pw_emit_last_post pw_bad_source pw_bad_path \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe labsem_memory_probeScript.sml labsem_memory_probe.out lab_mem_load_word lab_mem_load_loc lab_mem_store_loc lab_mem_load_unaligned_write lab_mem_store_unaligned_write lab_mem_load_domain_write lab_mem_store_domain_write lab_mem_load_address_loc lab_mem_store_address_loc lab_mem_address_wrap lab_mem_load32_le_low lab_mem_load32_le_high lab_mem_load32_be_high lab_mem_load32_be_low lab_mem_load32_unsigned lab_mem_load32_unaligned lab_mem_load32_domain lab_mem_load32_loc lab_mem_load32_address_loc lab_mem_store32_le_narrow lab_mem_store32_be_narrow lab_mem_store32_upper_half lab_mem_store32_unaligned lab_mem_store32_domain lab_mem_store32_source_loc lab_mem_store32_memory_loc lab_mem_load8_le lab_mem_load8_be lab_mem_load8_unsigned lab_mem_load8_domain_base lab_mem_load8_loc lab_mem_load8_address_loc lab_mem_store8_le_narrow lab_mem_store8_be_narrow lab_mem_store8_domain_base lab_mem_store8_source_loc lab_mem_store8_memory_loc lab_mem_load16_unsupported lab_mem_load16_loc_address lab_mem_store16_unsupported lab_mem_store16_loc_address lab_mem_sticky_load lab_mem_sticky_store lab_mem_width1_address0 lab_mem_width1_address1 lab_mem_width8_address1 "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_start_extend_probeScript.sml parmove_start_extend_probe.out \
  ps_start_pre_1 ps_start_pre_4 ps_start_pre_5 ps_start_post_1 ps_start_post_4 ps_start_post_5 ps_extend_pre_1 ps_extend_pre_3 ps_extend_pre_5 ps_extend_post_1 ps_extend_post_3 ps_extend_post_5 ps_bad_pre ps_bad_post \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe labsem_shared_memory_probeScript.sml labsem_shared_memory_probe.out \
  lab_shared_load lab_shared_load8 lab_shared_load16 lab_shared_load32 lab_shared_store lab_shared_store8 lab_shared_store16 lab_shared_store32 lab_shared_load16_unaligned lab_shared_store16_unaligned lab_shared_load_word_unaligned lab_shared_store_word_unaligned lab_shared_load_word_domain lab_shared_store_word_domain lab_shared_load_narrow_domain lab_shared_store_narrow_domain lab_shared_load_address_loc lab_shared_store_address_loc lab_shared_store_value_loc lab_shared_load_final lab_shared_store_final lab_shared_load_wrong_length lab_shared_store_wrong_length lab_shared_load_zero_clock lab_shared_store_zero_clock lab_shared_load_address_alias lab_shared_load_protocol_ignores_be lab_shared_store_protocol_ignores_be lab_shared_load24_alignment lab_shared_store24_alignment lab_shared_load1_empty lab_shared_store1_empty lab_shared_load1_mod0 lab_shared_store1_mod0 lab_shared_load8_word lab_shared_store8_short_take16 lab_shared_load_size256 lab_shared_store_size256 lab_shared_load_address_wrap \
  "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe parmove_remove_last_probeScript.sml parmove_remove_last_probe.out \
  pr_self_pre_1 pr_self_pre_4 pr_self_pre_5 pr_self_post_1 pr_self_post_4 pr_self_post_5 pr_last_pre_1 pr_last_pre_4 pr_last_pre_5 pr_last_post_1 pr_last_post_4 pr_last_post_5 pr_bad_self_pre pr_bad_self_post pr_bad_read_pre pr_bad_read_post \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe labsem_inst_probeScript.sml labsem_inst_probe.out \
  lab_inst_skip lab_inst_const lab_inst_arith_or_loc lab_inst_arith_or_loc_other lab_inst_arith_div_zero lab_inst_arith_shift_invalid lab_inst_mem_load_loc lab_inst_mem_store_unaligned lab_inst_mem_load32_loc_failure lab_inst_mem_load16_unsupported lab_inst_mem_store16_unsupported lab_inst_fp_mov_payload lab_inst_fp_neg_zero lab_inst_fp_from_reg_loc_failure \
  "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_save_probeScript.sml parmove_save_probe.out \
  pv_save_history_pre_1 pv_save_history_pre_4 pv_save_history_pre_5 pv_save_history_pre_temp pv_save_history_post_1 pv_save_history_post_4 pv_save_history_post_5 pv_save_history_post_temp pv_save_cycle_pre_1 pv_save_cycle_pre_2 pv_save_cycle_pre_4 pv_save_cycle_post_1 pv_save_cycle_post_2 pv_save_cycle_post_4 pv_save_none_source_pre_1 pv_save_none_source_pre_4 pv_save_none_source_post_1 pv_save_none_source_post_4 pv_save_bad_pending_pre_4 pv_save_bad_pending_post_4 \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe word_lang_max_var_exp_probeScript.sml word_lang_max_var_exp_probe.out \
  max_var max_load max_op_empty max_op_nested max_shift max_const max_lookup max_mixed \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe parmove_emithead_probeScript.sml parmove_emithead_probe.out \
  pv_head_history_pre_1 pv_head_history_pre_2 pv_head_history_pre_3 pv_head_history_pre_4 pv_head_history_pre_5 pv_head_history_post_1 pv_head_history_post_2 pv_head_history_post_3 pv_head_history_post_4 pv_head_history_post_5 pv_head_none_pre_1 pv_head_none_pre_2 pv_head_none_pre_4 pv_head_none_post_1 pv_head_none_post_2 pv_head_none_post_4 pv_head_bad_endpoint_pre_1 pv_head_bad_endpoint_pre_2 pv_head_bad_endpoint_post_1 pv_head_bad_endpoint_post_2 pv_head_bad_pending_pre_1 pv_head_bad_pending_pre_2 pv_head_bad_pending_pre_4 pv_head_bad_pending_post_1 pv_head_bad_pending_post_2 pv_head_bad_pending_post_4 \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_stepssem_probeScript.sml parmove_stepssem_probe.out \
  pv_rtc_0_1 pv_rtc_0_2 pv_rtc_0_temp pv_rtc_1_1 pv_rtc_1_2 pv_rtc_1_temp pv_rtc_2_1 pv_rtc_2_2 pv_rtc_2_temp pv_rtc_3_1 pv_rtc_3_2 pv_rtc_3_temp \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_dsteps_probeScript.sml parmove_dsteps_probe.out \
  pd_remove pd_start pd_extend pd_save_emit pd_emit_head pd_emit_last pd_start_guard pd_read_guard pd_extend_suffix_read \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe parmove_final_probeScript.sml parmove_final_probe.out \
  pv_final_terminal pv_final_self pv_final_chain pv_final_cycle pv_final_scratch pv_final_duplicate pv_final_active \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe labsem_evaluate_probeScript.sml labsem_evaluate_probe.out \
  lab_eval_clock_zero lab_eval_halt_success lab_eval_halt_resource lab_eval_halt_loc_error lab_eval_halt_failed_still_success lab_eval_fetch_empty lab_eval_fetch_beyond lab_eval_unsupported_asmi lab_eval_const_then_halt lab_eval_skip_timeout lab_eval_failed_skip_rollback lab_eval_div_failure_rollback lab_eval_store_failure_rollback lab_eval_fp_neg_then_halt lab_eval_jumpreg_return lab_eval_jumpreg_word_error lab_eval_jumpreg_missing_error lab_eval_cbw_then_halt lab_eval_cbw_timeout lab_eval_cbw_address_error lab_eval_cbw_space_error lab_eval_cbw_loc_error lab_eval_locvalue_success lab_eval_locvalue_missing lab_eval_jump_success lab_eval_jump_missing lab_eval_jump_self_timeout lab_eval_jumpcmp_true lab_eval_jumpcmp_false lab_eval_jumpcmp_true_missing lab_eval_jumpcmp_false_missing_ignored lab_eval_jumpcmp_loc_test lab_eval_jumpcmp_loc_error lab_eval_call_return lab_eval_call_missing_target lab_eval_call_missing_return lab_eval_shared_domain_error lab_eval_shared_loc_address_error lab_eval_shared_load16_identity lab_eval_shared_load16_final lab_eval_shared_load16_badlength lab_eval_shared_store16_return lab_eval_install_operands_error lab_eval_install_flush_error lab_eval_install_return_missing lab_eval_install_compile_none lab_eval_ffi_operand_error lab_eval_ffi_domain_error lab_eval_ffi_return_missing lab_eval_ffi_identity lab_eval_ffi_final lab_eval_ffi_badlength lab_eval_install_good lab_eval_install_bytes lab_eval_install_cfg lab_eval_install_empty lab_eval_install_execute_code \
  "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_native_config_probeScript.sml word_to_stack_native_config_probe.out \
  nc_length nc_empty nc_single nc_nonwf nc_raw nc_update_length nc_update_tree \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe parmove_stepscorrect_probeScript.sml parmove_stepscorrect_probe.out \
  pv_correct_cycle_parallel_1 pv_correct_cycle_parallel_2 pv_correct_cycle_parallel_temp pv_correct_cycle_sequential_1 pv_correct_cycle_sequential_2 pv_correct_cycle_sequential_temp pv_correct_chain_parallel_1 pv_correct_chain_parallel_2 pv_correct_chain_parallel_temp pv_correct_chain_sequential_1 pv_correct_chain_sequential_2 pv_correct_chain_sequential_temp \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_to_stack_programs_native_probeScript.sml word_to_stack_programs_native_probe.out \
  wts_prog_zero_registers wts_prog_register_only wts_prog_exact_register_args wts_prog_first_stack_arg wts_prog_three_stack_args wts_prog_all_stack_args wts_prog_huge_register_count wts_prog_var_boundary wts_prog_var_first_stack wts_prog_var_odd_stack wts_prog_vars_exceed_args wts_prog_args_exceed_vars wts_prog_perf_tick wts_prog_width_one wts_prog_list_empty wts_prog_list_generic wts_prog_list_duplicates wts_prog_bitmap_order wts_prog_bitmap_reverse wts_prog_bitmap_multiword wts_prog_bitmap_zero_frame \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_compile_keys_probeScript.sml word_to_stack_compile_keys_probe.out \
  ck_empty ck_single ck_generic ck_duplicate ck_order ck_bitmap ck_width_one \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend"
run_probe parmove_split_source_probeScript.sml parmove_split_source_probe.out \
  pv_split_empty pv_split_first pv_split_middle pv_split_absent pv_split_none pv_split_duplicate_dest pv_split_late_zero \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_source_probeScript.sml parmove_source_probe.out \
  pv_source_terminal pv_source_self pv_source_chain pv_source_cycle pv_source_scratch pv_source_duplicate pv_source_active pv_source_history \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"


run_probe parmove_destination_probeScript.sml parmove_destination_probe.out \
  pv_destination_terminal pv_destination_self pv_destination_chain pv_destination_cycle pv_destination_scratch pv_destination_duplicate pv_destination_active \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe labsem_semantics_probeScript.sml labsem_semantics_probe.out \
  lab_semantics_empty_error lab_semantics_halt_success lab_semantics_halt_resource lab_semantics_loop_diverge \
  "$cake_dir/compiler/backend/semantics/labSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_dstep_step_probeScript.sml parmove_dstep_step_probe.out \
  pv_ds_wf_0 pv_ds_wf_1 pv_ds_wf_2 pv_ds_wf_3 pv_ds_wf_4 pv_ds_wf_5 pv_ds_cycle_0_0 pv_ds_cycle_0_1 pv_ds_cycle_0_2 pv_ds_cycle_1_0 pv_ds_cycle_1_1 pv_ds_cycle_1_2 pv_ds_cycle_2_0 pv_ds_cycle_2_1 pv_ds_cycle_2_2 \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe lab_to_target_encoding_probeScript.sml lab_to_target_encoding_probe.out \
  FFIOffset LabInstJump LabInstJumpCmp LabInstCall LabInstLocValue LabInstHalt LabInstInstall LabInstCallFFI \
  CbwToAsmAsmi CbwToAsmCbw CbwToAsmShareMem \
  EncLineLabel EncLineAsm EncLineAsmCbw EncLineLabAsm EncSec EncSecList \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_labels_probeScript.sml lab_to_target_labels_probe.out \
  SectionLabelsEmpty SectionLabelsEmptyLabs SectionLabelsConcrete SectionLabelsConcreteLabs \
  ComputeLabelsAltEmpty ComputeLabelsAltConcrete \
  ComputeLookupSection1 ComputeLookupSection2 ComputeLookupSection3Absent \
  ComputeLookupSection1Start ComputeLookupSection1Label1 \
  ComputeLookupSection2Start ComputeLookupSection2Label2 \
    "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_positions_probeScript.sml lab_to_target_positions_probe.out \
  FindPosHit FindPosHitZero FindPosDefaultLabel FindPosDefaultSection \
  GetLabelJump GetLabelJumpCmp GetLabelCall GetLabelLocValue GetLabelDefault \
  GetFfiIndexHit GetFfiIndexDefault \
  GetJumpOffsetCallFFI GetJumpOffsetInstall GetJumpOffsetHalt GetJumpOffsetJump \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_secondpass_probeScript.sml lab_to_target_secondpass_probe.out \
  EncLinesAgainEmpty EncLinesAgainKeep EncLinesAgainReencodeShort \
  EncLinesAgainReencodeLong EncSecsAgainEmpty EncSecsAgainTwo \
  LinesUpdLabLenEmpty LinesUpdLabLenEven LinesUpdLabLenOdd \
  UpdLabLenEmpty UpdLabLenTwo \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_padding_probeScript.sml lab_to_target_padding_probe.out \
  PadBytesFits PadBytesAppend PadBytesLonger \
  AddNopEmpty AddNopLabelThenAsm AddNopAsmHead AddNopLabAsmHead \
  PadSectionEmpty PadSectionConcrete PadCodeEmpty PadCodeTwo \
  SecLengthEmpty SecLengthConcrete GetSymbolsEmpty GetSymbolsTwo \
  LineOkLightLabel LineOkLightAsm LineOkLightHaltOk LineOkLightHaltBad \
  LineOkLightInstall LineOkLightCallFFIOk LineOkLightCall \
  LineOkLightJumpCmpOk LineOkLightJumpCmpBad LineOkLightLocValue \
  SecOkLightMixed SecOkLightCall \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_removelabels_probeScript.sml lab_to_target_removelabels_probe.out \
  ZeroLabsAccOfLocHit ZeroLabsAccOfLocNonzero ZeroLabsAccOfJumpHit \
  ZeroLabsAccOfJumpNonzero ZeroLabsAccOfJumpCmpHit ZeroLabsAccOfJumpCmpNonzero \
  ZeroLabsAccOfCatchAll LineGetZeroLabsAccLabAsm LineGetZeroLabsAccLabel \
  LineGetZeroLabsAccAsm GetZeroLabsAccEmpty GetZeroLabsAccConcrete \
  ZeroLabsAccExistTrue ZeroLabsAccExistFalse LineBytesLabel LineBytesAsm \
  LineBytesLabAsm ProgToBytesEmpty ProgToBytesConcrete RemoveLabelsLoopZero \
  RemoveLabelsLoopOne RemoveLabelsZero \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_line_len_probeScript.sml lab_to_target_line_len_probe.out \
  LineLenLabel LineLenAsmEmpty LineLenAsmBytesMismatch LineLenLabAsm LineLenWide \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe lab_to_target_section_length_probeScript.sml lab_to_target_section_length_probe.out \
  SectionLengthEmpty SectionLengthMixed SectionLengthMixedPosition SectionLengthMixedLabels \
  SectionLengthZeroLabel SectionLengthZeroLenLabel SectionLengthDuplicateLabels \
  SectionLengthArbitraryAccumulator SecLengthAddEmpty SecLengthAddMixed SecLengthAddMixedValue \
  SecLengthAddZeroAnnotation SecLengthAddEmptyBytesAnnotation SecLengthSumEmpty SecLengthSumMixed \
  SectionAppendEmptyLeft SectionAppendMixedTail SectionAppendConcretePair SectionAppendZeroLabel \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe byte_word_to_bytes_aux_probeScript.sml byte_word_to_bytes_aux_probe.out \
  ByteAuxLE16Cycle ByteAuxBE16Cycle ByteAuxLE32Cycle ByteAuxBE32Cycle \
  ByteAuxOneByteCycle ByteAuxSubByteLEWrap ByteAuxSubByteBEWrap ByteAuxZero \
  ByteWholeLE16 ByteWholeBE16 ByteWholeSubByte ByteIndexSubByteLE ByteIndexSubByteBE \
  ByteGetSubByteShift \
  "$cake_dir/compiler/backend/semantics/targetSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe lab_to_target_padding_length_probeScript.sml lab_to_target_padding_length_probe.out \
  OriginalLengthPadBytes PadLengthExtend PadLengthMultiNop PadLengthExact PadLengthZero \
  PadLengthGenericBool PadLengthEmptyNopOutsidePremise \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe lab_to_target_maplemmas_probeScript.sml lab_to_target_maplemmas_probe.out \
  PadCodeMapEmptyEq PadCodeMapConcreteEq PadCodeMapConcreteLhs PadCodeMapConcreteRhs \
  ProgToBytesMapEmptyEq ProgToBytesMapConcreteEq ProgToBytesMapConcreteLhs \
  ProgToBytesMapConcreteRhs \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_shmeminfo_probeScript.sml lab_to_target_shmeminfo_probe.out \
  GetMemopInfoLoad GetMemopInfoLoad32 GetMemopInfoLoad16 GetMemopInfoLoad8 \
  GetMemopInfoStore GetMemopInfoStore32 GetMemopInfoStore16 GetMemopInfoStore8 \
  ListAddIfFreshEmpty ListAddIfFreshPresent ListAddIfFreshAbsent \
  FindFfiNamesEmpty FindFfiNamesConcrete FindFfiNamesNonCallFFI \
  GetShmemInfoEmpty GetShmemInfoLabelSkip GetShmemInfoShareMem \
  GetShmemInfoAsmAdvance \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe lab_to_target_compile_probeScript.sml lab_to_target_compile_probe.out \
  NotSkipSkip NotSkipAsm NotSkipLabel NotSkipLabAsm \
  FilterSkipEmpty FilterSkipOne FilterSkipTwo \
  ListSubsetTrue ListSubsetFalse \
  ConfigLabels ConfigSecPosLen ConfigPos ConfigInitClock ConfigFfiNames \
  ConfigShmemExtra ConfigHashSize \
  CompileLabSuccess CompileLabFfiSubsetFail CompileLabRemoveLabelsNone \
  CompileSkip CompileLabFilterSkip \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_total_colour_probeScript.sml word_alloc_total_colour_probe.out \
  tc_absent_zero tc_absent_physical tc_absent_virtual tc_absent_large_physical tc_absent_large_virtual tc_mapped_physical tc_mapped_virtual tc_mapped_zero \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_even_locals_probeScript.sml word_alloc_even_locals_probe.out \
  wa_even_empty wa_even_zero wa_even_even_holes wa_even_odd wa_even_mixed wa_even_overwrite \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe parmove_destination_wrapper_probeScript.sml parmove_destination_wrapper_probe.out \
  dw_empty dw_self dw_chain dw_cycle dw_duplicate dw_order dw_nested_option \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_to_stack_live_length_probeScript.sml word_to_stack_live_length_probe.out \
  ll_zero ll_empty ll_slack ll_tree ll_nonwf ll_width8 \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_live_prefix_probeScript.sml word_to_stack_live_prefix_probe.out \
  lp_zero lp_empty lp_slack lp_tree lp_nonwf lp_width8 lp_shortcount \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_insert_prefix_probeScript.sml word_to_stack_insert_prefix_probe.out \
  ip_empty ip_append ip_nested ip_shortcount ip_slack ip_bool ip_option \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_comp_prefix_probeScript.sml word_to_stack_comp_prefix_probe.out \
  cp_skip cp_alloc cp_must cp_seq cp_if cp_loop cp_return cp_handler cp_consts \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_merge_stack_sets_probeScript.sml word_alloc_merge_stack_sets_probe.out \
  mss_empty mss_retained_right mss_new_left_bias mss_new_right mss_removed mss_fixed_left_bias mss_raw mss_generic \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_remove_temp_stack_probeScript.sml word_alloc_remove_temp_stack_probe.out \
  rts_empty rts_zero rts_duplicate rts_missing rts_fixed rts_raw rts_generic_payload rts_generic_fixed \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_merge_stack_only_probeScript.sml word_alloc_merge_stack_only_probe.out \
  mso_present_alloc mso_present_physical mso_present_stack mso_absent_stack_alloc mso_absent_stack_physical mso_absent_delete_missing mso_absent_delete_root mso_present_overwrite mso_raw \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe parmove_correct_probeScript.sml parmove_correct_probe.out \
  pc_empty pc_self pc_chain pc_cycle pc_fanout pc_order pc_bool \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_alloc_coalesce_cost_probeScript.sml word_alloc_coalesce_cost_probe.out \
  cc_absent cc_left cc_right cc_both cc_same cc_zero cc_large cc_raw \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe target_sem_mapped_memory_probeScript.sml target_sem_mapped_memory_probe.out \
  tm_read_0 tm_read_0_wrong_opcode tm_read_1 tm_read_1_wrong_opcode tm_read_2 tm_read_2_wrong_opcode tm_read_4 tm_read_4_wrong_opcode tm_write_0 tm_write_0_wrong_opcode tm_write_1 tm_write_1_wrong_opcode tm_write_2 tm_write_2_wrong_opcode tm_write_4 tm_write_4_wrong_opcode tm_read_invalid_3 tm_read_invalid_8 tm_read_invalid_16 tm_read_invalid_255 tm_write_invalid_3 tm_write_invalid_8 tm_write_invalid_16 tm_write_invalid_255 tm_read_register_mismatch tm_read_base_mismatch tm_read_offset_mismatch tm_write_domain_gap tm_read_wrap tm_write_wrap tm_read_empty_domain tm_write_empty_domain tm_read_invalid_empty tm_read_byte_size_wrap tm_write_byte_size_wrap \
  "$cake_dir/compiler/backend/semantics/targetSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_alloc_even_colour_probeScript.sml word_alloc_even_colour_probe.out \
  even_colour_empty even_colour_zero even_colour_zero_bad even_colour_physical even_colour_physical_bad even_colour_virtual even_colour_mixed even_colour_mixed_bad even_colour_virtual_large even_colour_physical_large even_colour_physical_large_bad even_colour_duplicate_first_good even_colour_duplicate_first_bad even_colour_duplicate_virtual even_colour_no_zero even_colour_last_bad even_colour_empty_internal even_colour_physical_root_bad even_colour_virtual_left even_colour_physical_right_bad \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe spt_union_algebra_probeScript.sml spt_union_algebra_probe.out \
  spt_union_insert_all spt_union_assoc_all spt_union_unit_sym_all spt_union_singleton_all spt_union_insert_empty_0 spt_union_insert_empty_1 spt_union_insert_empty_2 spt_union_insert_empty_17 spt_union_insert_leaf_0 spt_union_insert_leaf_1 spt_union_insert_leaf_2 spt_union_insert_leaf_17 spt_union_insert_empty_internal_0 spt_union_insert_empty_internal_1 spt_union_insert_empty_internal_2 spt_union_insert_empty_internal_17 spt_union_insert_branch_0 spt_union_insert_branch_1 spt_union_insert_branch_2 spt_union_insert_branch_17 spt_union_insert_root_0 spt_union_insert_root_1 spt_union_insert_root_2 spt_union_insert_root_17 spt_union_insert_malformed_nested_0 spt_union_insert_malformed_nested_1 spt_union_insert_malformed_nested_2 spt_union_insert_malformed_nested_17 spt_union_left_bias spt_union_nat_noncomm spt_union_malformed_retained spt_union_unit_malformed \
  "$hol_dir/src/finite_maps/sptreeScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_native_top_probeScript.sml word_to_stack_native_top_probe.out \
  wts_top_empty_plain wts_top_empty_perf wts_top_empty_zero wts_top_empty_narrow wts_top_width_one_plain wts_top_width_one_perf wts_top_zero_registers wts_top_reg_underflow wts_top_avoid_duplicate wts_top_avoid_single wts_top_reg_only wts_top_stack_args wts_top_perf_args wts_top_break wts_top_duplicates wts_top_duplicates_reverse wts_top_order wts_top_large_identifier wts_top_bitmap_plain wts_top_bitmap_perf wts_top_bitmap_order wts_top_bitmap_reverse wts_top_bitmap_multiword wts_top_bitmap_zero_frame \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

# `word_remove$remove_must_terminate`: nested and sequenced `MustTerminate`,
# `If`, `Loop`, both `Call` bodies and the catchall.
run_probe word_remove_must_terminate_probeScript.sml word_remove_must_terminate_probe.out \
  rmt_mt_seq rmt_tick \
  "$cake_dir/compiler/backend/word_removeScript.sml" \
  "$cake_dir/compiler/backend"

# `data_to_word` pointer-layout helpers: `shift_length`, `small_shift_length`
# and `get_gen_size` (empty, in range, overflowing) at 64 and 32 bits.
run_probe data_to_word_config_probeScript.sml data_to_word_config_probe.out \
  shift_length gen_size_three_32 \
  "$cake_dir/compiler/backend/data_to_wordScript.sml" \
  "$cake_dir/compiler/backend"

run_probe word_alloc_checker_call_none_probeScript.sml word_alloc_checker_call_none_probe.out \
  ccn_empty ccn_one ccn_duplicate ccn_args ccn_collision ccn_handler_ignored \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_loop_checker_probeScript.sml word_alloc_loop_checker_probe.out \
  lc_break_absent lc_continue_absent lc_break_present lc_continue_present lc_loop_skip lc_loop_continue lc_break_collision \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_stack_only_probeScript.sml word_alloc_stack_only_probe.out \
  gso_skip gso_move gso_foldr gso_seq gso_must gso_loop gso_call_none gso_call_return gso_tick gso_return gso_alloc_nondelta gso_entry gso_if_reg gso_if_imm gso_call_both \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_get_prefs_probeScript.sml word_alloc_get_prefs_probe.out \
  prefs_skip prefs_empty prefs_move prefs_duplicate prefs_self prefs_seq prefs_if_reg prefs_if_imm prefs_must prefs_loop prefs_tail prefs_tail_handler prefs_return prefs_both prefs_nested prefs_ignored prefs_large \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_sp_default_probeScript.sml word_alloc_sp_default_probe.out \
  spd_missing_phy spd_missing_virtual spd_present_phy spd_present_virtual spd_present_zero spd_raw_bs spd_raw_bn_hit spd_raw_bn_miss spd_large_phy spd_large_virtual tc_missing_phy tc_missing_virtual tc_present tc_raw tc_large \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe reg_alloc_in_clash_tree_probeScript.sml reg_alloc_in_clash_tree_probe.out \
  ict_delta_write ict_delta_read ict_delta_miss ict_set ict_set_miss ict_set_raw ict_branch_left ict_branch_right ict_branch_none_miss ict_branch_some ict_branch_some_miss ict_seq_left ict_seq_right ict_large cct_ok_f cct_ok_gf cct_collision_f cct_collision_gf \
  "$cake_dir/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "$cake_dir/compiler/backend/reg_alloc/proofs"
run_probe reg_alloc_invariants_probeScript.sml reg_alloc_invariants_probe.out \
  he_hit he_miss he_y_oob he_x_oob he_large und_sym und_asym grs_ok grs_unsorted grs_bad_move grs_bad_length nc_ok nc_clash nc_atemp nc_self spi_ok spi_bad spi_insert clq_ok clq_bad sub_ok sub_bad hide_num cs_ok cs_bad cs_self_loop gp_first gp_outside gnp_none gnp_low \
  "$cake_dir/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "$cake_dir/compiler/backend/reg_alloc/proofs"
run_probe reg_alloc_mk_bij_lemmas_probeScript.sml reg_alloc_mk_bij_lemmas_probe.out \
  mbl_remap_keys mbl_remap_wf mbl_remap_inverse mbl_tree_keys mbl_tree_wf mbl_large \
  "$cake_dir/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "$cake_dir/compiler/backend/reg_alloc/proofs"
run_probe reg_alloc_accessors_probeScript.sml reg_alloc_accessors_probe.out \
  acc_get_dim acc_get_stack acc_get_avail acc_set_dim acc_set_keeps acc_adj_length acc_tag_sub acc_tag_sub_oob acc_adj_sub acc_large_oob acc_update_deg acc_update_oob acc_update_mr acc_update_tag acc_coalesced_sub acc_map_sub acc_map_oob acc_mupdate \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe reg_alloc_colouring_probeScript.sml reg_alloc_colouring_probe.out \
  rc_empty_ks rc_no_nodes rc_fixed rc_dup_colours rc_oob rc_oob_after_empty aat_none aat_pref aat_stemp aat_non_atemp aat_oob aa_all aa_pref aa_one_colour fmc_hit fmc_not_in_ks fmc_empty fmc_oob \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe word_alloc_select_reg_alloc_probeScript.sml word_alloc_select_reg_alloc_probe.out \
  sra_type sra_simple0 sra_simple1 sra_irc2 sra_irc3_cost sra_linear4 sra_linear5_spill sra_linear_forced \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe reg_alloc_allocator_probeScript.sml reg_alloc_allocator_probe.out \
  ra_simple_delta ra_irc_move ra_simple_move ra_irc_spill_cost ra_irc_spill_deg ra_simple_branch_forced ra_irc_phys ra_irc_fs ra_irc_stack ra_irc_coalesce_chain ra_irc_pressure ra_empty \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe reg_alloc_exception_functions_probeScript.sml reg_alloc_exception_functions_probe.out \
  ef_raise_fail ef_raise_sub ef_hs_success ef_hs_catch ef_hs_pass_fail ef_hs_failing_state ef_hs_accessor ef_hf_catch ef_hf_pass_sub ef_hf_success ef_hf_failing_state \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe reg_alloc_stemp_colouring_probeScript.sml reg_alloc_stemp_colouring_probe.out \
  st_type_assign_tag st_type_neg_biased st_tag_col st_unbound_empty st_unbound_gap st_unbound_below st_unbound_dup st_tag_none st_tag_pref st_tag_non_stemp st_tag_oob st_all st_all_k_high st_neg_first_hit st_neg_first_bad st_neg_first_oob st_neg_biased st_neg_biased_missing st_neg_biased_oob_partner st_neg_biased_out_of_dim \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe word_alloc_remove_dead_probeScript.sml word_alloc_remove_dead_probe.out \
  rd_move_partial rd_move_dead rd_inst_dead rd_inst_live rd_get_dead rd_get_live rd_curr_heap rd_locvalue_dead rd_set_dead_store rd_set_live_store rd_set_exp rd_seq_drop rd_seq_both rd_must rd_if_dead rd_if_imm rd_call_ret rd_call_tail rd_alloc rd_loop rd_break rd_continue_missing rd_catchall rd_prog lsr_agree lsr_differ \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_alloc_nlive_store_probeScript.sml word_alloc_nlive_store_probe.out \
  ns_lookup_dead ns_lookup_live ns_var ns_const ns_op_dead ns_op_live ns_op_empty ns_load ns_load_dead ns_shift_left_dead ns_shift_right_dead ns_shift_live \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_gc_functions_probeScript.sml word_gc_functions_probe.out \
  gc_ptr_to_addr gc_is_gc_word_const_odd \
  "$cake_dir/compiler/backend/proofs/word_gcFunctionsScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe stack_alloc_gc_code_probeScript.sml stack_alloc_gc_code_probe.out \
  sa_memcpy_code sa_compile_none \
  "$cake_dir/compiler/backend/stack_allocScript.sml" \
  "$cake_dir/compiler/backend"

run_probe stack_alloc_get_bits_probeScript.sml stack_alloc_get_bits_probe.out \
  get_bits_11 get_bits_msb_64 \
  "$cake_dir/compiler/backend/proofs/stack_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe stack_alloc_gc_bitmaps_probeScript.sml stack_alloc_gc_bitmaps_probe.out \
  gcb_bitmap gcb_roots_bitmaps \
  "$cake_dir/compiler/backend/proofs/stack_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe word_alloc_get_forced_probeScript.sml word_alloc_get_forced_probe.out \
  gf_addcarry_riscv gf_addcarry_mips gf_addcarry_self gf_addcarry_x86 gf_addovf_riscv gf_addovf_armv8 gf_subovf_mips gf_subovf_self gf_longmul_armv7 gf_longmul_armv7_self gf_longmul_riscv gf_longmul_ag32 gf_longmul_x86 gf_fptoreg_32 gf_fptoreg_32_self gf_fptoreg_64 gf_fpfromreg_32 gf_fpfromreg_64 gf_other_inst gf_seq gf_if gf_must gf_loop gf_call_return gf_call_both gf_call_tail gf_skip gf_large \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"


run_probe word_alloc_share_checker_probeScript.sml word_alloc_share_checker_probe.out \
  sc_store sc_store8 sc_store16 sc_store32 sc_load sc_load8 sc_load16 sc_load32 \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_spillcost_probeScript.sml word_alloc_spillcost_probe.out \
  spill_zero spill_call_tail spill_call_nontail spill_left_register spill_left_memory spill_right_register spill_right_memory spill_asymmetric_tail spill_asymmetric_nontail spill_large \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe spt_mapi_probeScript.sml spt_mapi_probe.out \
  mi_empty mi_leaf mi_children mi_root mi_nested mi_raw_bn mi_raw_bs mi_raw_nested mi_index3 mi_index6 mi_bool_nat mi_nat_bool \
  "$hol_dir/src/finite_maps/sptreeScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_return_checker_probeScript.sml word_alloc_return_checker_probe.out \
  rc_empty rc_cuts rc_duplicate_args rc_return_tick rc_return_break rc_return_collision rc_args_collision \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_oracle_colour_probeScript.sml word_alloc_oracle_colour_probe.out \
  oc_none oc_empty oc_physical_bad oc_checker_collision oc_forced_collision oc_forced_distinct oc_rename oc_stack_equal oc_stack_below oc_raw_map \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_heu_counters_probeScript.sml word_alloc_heu_counters_probe.out \
  hc_lhs_const_absent hc_lhs_const_present hc_lhs_const_repeat hc_lhs_const_other hc_lhs_reg_absent hc_lhs_reg_present hc_lhs_reg_repeat hc_lhs_reg_other hc_lhs_mem_absent hc_lhs_mem_present hc_lhs_mem_repeat hc_lhs_mem_other hc_rhs_reg_absent hc_rhs_reg_present hc_rhs_reg_repeat hc_rhs_reg_other hc_rhs_mem_absent hc_rhs_mem_present hc_rhs_mem_repeat hc_rhs_mem_other \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe parmove_temp_mixed_probeScript.sml parmove_temp_mixed_probe.out \
  ntm_real ntm_read ntm_write ntm_both \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_alloc_checker_assembly_probeScript.sml word_alloc_checker_assembly_probe.out \
  ca_control ca_return ca_handler ca_tail_ignored ca_collision \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe parmove_independence_probeScript.sml parmove_independence_probe.out \
  ind_head ind_middle ind_tail ind_cycle ind_fanout ind_self ind_bool ind_empty_others ind_nil_nat ind_nil_bool \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_seqsem_unchanged_probeScript.sml parmove_seqsem_unchanged_probe.out \
  su_empty su_chain su_cycle su_repeat su_source su_written su_self su_bool \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_parsem_map_inj_probeScript.sml parmove_parsem_map_inj_probe.out \
  pi_one pi_chain pi_cycle pi_shared_source pi_self pi_high pi_mixed pi_collision \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe spt_map_probeScript.sml spt_map_probe.out \
  sm_empty sm_leaf sm_children sm_root sm_raw_bn sm_raw_bs sm_raw_nested sm_bool_nat sm_nat_bool sm_unit_raw \
  "$hol_dir/src/finite_maps/sptreeScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_heu_inst_probeScript.sml word_alloc_heu_inst_probe.out \
  hi_skip hi_const hi_binreg hi_shiftreg hi_div hi_binimm hi_shiftimm hi_carry hi_addoverflow hi_suboverflow hi_longmul hi_longdiv hi_load hi_load32 hi_load8 hi_store hi_store32 hi_store8 hi_fpless hi_fplessequal hi_fpequal hi_to_1 hi_from_1 hi_to_32 hi_from_32 hi_to_64 hi_from_64 hi_to_128 hi_from_128 hi_bin_alias hi_carry_alias hi_longdiv_alias hi_to_alias hi_from_alias hi_existing hi_large hi_const_raw hi_load16_raw hi_store16_raw hi_fpabs_raw hi_fpneg_raw hi_fpsqrt_raw hi_fpadd_raw hi_fpsub_raw hi_fpmul_raw hi_fpdiv_raw hi_fpfma_raw hi_fpmov_raw hi_fptoint_raw hi_fpfromint_raw \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_heu_max_probeScript.sml word_alloc_heu_max_probe.out \
  hm_tuple hm_tuple_equal hm_tuple_zero hm_tuple_large hm_empty hm_left hm_right hm_overlap hm_disjoint hm_mixed hm_nested hm_raw_left_bn hm_raw_right_bn hm_raw_both_bn hm_raw_left_bs hm_raw_right_bs hm_raw_both_bs hm_raw_bs_leaf hm_raw_leaf_bs hm_raw_empty_leaf \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe monad_base_probeScript.sml monad_base_probe.out \
  mb_bind_ok mb_bind_fail mb_ignore_ok mb_ignore_fail mb_return mb_run_ok mb_run_fail mb_alloc_three mb_alloc_zero mb_exn_bytes \
  "$cake_dir/translator/monadic/monad_base/ml_monadBaseScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe word_to_stack_full_read_bitmap_mixed_probeScript.sml word_to_stack_full_read_bitmap_mixed_probe.out \
  fra_8_1 fra_8_16 fra_1_32 fra_16_8 fra_offset fra_same fra_success8_1 fra_success1_32 fra_zero fra_loc \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe find_index_append_probeScript.sml find_index_append_probe.out \
  fia_empty fia_empty_left fia_empty_right fia_left_head fia_duplicates fia_right_last fia_absent fia_zero fia_bool fia_large \
  "$cake_dir/misc/miscScript.sml" "$cake_dir/misc"
run_probe word_alloc_heu_call_probeScript.sml word_alloc_heu_call_probe.out \
  hc_merge_empty hc_merge_left hc_merge_right hc_merge_overlap hc_merge_disjoint hc_merge_raw_left hc_merge_raw_right hc_merge_raw_root hc_add_empty hc_add_nat hc_add_bool hc_add_tuple hc_add_nested hc_add_raw_bn hc_add_raw_bs hc_add_raw_overlap \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_abs_stack_generality_probeScript.sml word_to_stack_abs_stack_generality_probe.out \
  asg_base16 asg_base1 asg_plain16 asg_handler16 asg_plain1 asg_handler1 asg_nested16 asg_marker_bad \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_handler_val_generality_probeScript.sml word_to_stack_handler_val_generality_probe.out \
  hvg_empty hvg_plain_empty hvg_handler_empty hvg_plain_three hvg_handler_two hvg_mixed hvg_middle_function hvg_frame_functions \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_comp_length_probeScript.sml word_to_stack_comp_length_probe.out \
  comp_length_skip comp_length_alloc comp_length_must_terminate comp_length_sequence comp_length_if_both_branches comp_length_loop comp_length_tail_ignores_handler comp_length_returning_call comp_length_call_and_handler comp_length_store_empty comp_length_call_store_nested_handler comp_length_zero_frame comp_length_multiword comp_length_width_one comp_length_bound_required comp_length_large_gap comp_length_empty_initial comp_length_sequence_store \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_cutset_maximum_probeScript.sml word_to_stack_cutset_maximum_probe.out \
  cs_empty cs_root cs_left cs_right cs_duplicates cs_left_max cs_reordered cs_root_duplicates cs_large cs_overlap cs_range cs_sparse \
  "$cake_dir/pancake/loop_to_wordScript.sml" "$cake_dir/pancake"

run_probe word_to_stack_instruction_maximum_probeScript.sml word_to_stack_instruction_maximum_probe.out \
  im_const im_bin_reg im_bin_imm im_shift_reg im_shift_imm im_div im_carry im_mul im_longdiv im_load im_store8 im_large im_load16 im_store16 \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe reg_alloc_remap_probeScript.sml reg_alloc_remap_probe.out \
  remap_empty remap_delta remap_duplicate remap_seq remap_branch remap_fixed remap_raw_empty remap_raw_root remap_set_order remap_large remap_nested remap_initial \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_to_stack_ssa_codec_probeScript.sml word_to_stack_ssa_codec_probe.out \
  sc_skip sc_assigns sc_constant sc_shift sc_multiply sc_raise sc_call sc_return \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_heu_prog_probeScript.sml word_alloc_heu_prog_probe.out \
  hp_move hp_inst hp_get hp_set_var hp_set_other hp_heap hp_heap_alias hp_loc hp_seq hp_must hp_loop hp_if_reg hp_if_alias hp_if_imm hp_tail_indirect hp_tail_other hp_tail_self hp_ret_indirect hp_ret_other hp_ret_self hp_ret_discard hp_ret_self_discard hp_ret_handler hp_if_calls hp_seq_calls hp_share_load hp_share_load8 hp_share_load16 hp_share_load32 hp_share_store hp_share_store8 hp_share_store16 hp_share_store32 hp_ignore_skip hp_ignore_assign hp_ignore_store hp_ignore_alloc hp_ignore_consts hp_ignore_raise hp_ignore_return hp_ignore_break hp_ignore_continue hp_ignore_tick hp_ignore_install hp_ignore_code hp_ignore_data hp_ignore_ffi hp_width1 hp_width128 hp_large_counter hp_raw_skip hp_raw_self \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_canonize_moves_aux_probeScript.sml word_alloc_canonize_moves_aux_probe.out \
  cma_empty cma_acc cma_same_up cma_same_down cma_same_equal cma_different cma_groups cma_unsorted cma_reversed cma_self cma_large cma_bool \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe misc_find_index_shift_zero_probeScript.sml misc_find_index_shift_zero_probe.out \
  fiz_empty fiz_head fiz_middle fiz_last fiz_absent fiz_zero fiz_large_offset fiz_large_value fiz_bool fiz_bool_absent \
  "$cake_dir/misc/miscScript.sml" "$cake_dir/misc"

run_probe parmove_temp_step_probeScript.sml parmove_temp_step_probe.out \
  pts_remove pts_start pts_extend pts_save_cycle pts_emit_head pts_emit_last pts_save_none pts_emit_scratch pts_bool \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_to_stack_dead_codec_probeScript.sml word_to_stack_dead_codec_probe.out \
  dc_skip dc_move dc_const dc_load dc_load16 dc_store dc_share dc_seq dc_if dc_loop dc_must dc_tail_handler dc_return_handler \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_colour_domain_probeScript.sml word_to_stack_colour_domain_probe.out \
  cd_load16 cd_store16 cd_load8 cd_store32 cd_carry cd_collision cd_seq cd_must cd_if cd_loop cd_tail_handler cd_both cd_large \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_program_maximum_probeScript.sml word_to_stack_program_maximum_probe.out \
  pm_skip pm_tick pm_move pm_assign pm_inst pm_get pm_store pm_set pm_seq pm_if_reg pm_if_imm pm_loop pm_must pm_break pm_continue pm_raise pm_loc pm_return pm_return_initial pm_tail_handler pm_return_call pm_both_call pm_alloc pm_constants pm_heap pm_install pm_code_write pm_data_write pm_ffi pm_shared16 pm_large pm_tail_empty \
  "$cake_dir/pancake/loop_to_wordScript.sml" "$cake_dir/pancake"

run_probe word_to_stack_cse_codec_probeScript.sml word_to_stack_cse_codec_probe.out \
  cc_skip cc_move cc_const cc_get cc_load cc_offset cc_shift cc_load16 cc_share cc_loop cc_must cc_if cc_tail cc_return cc_store_barrier cc_call_barrier \
  "$cake_dir/compiler/backend/word_cseScript.sml" "$cake_dir/compiler/backend"
run_probe word_alloc_canonize_sort_probeScript.sml word_alloc_canonize_sort_probe.out \
  cs_empty cs_one cs_two cs_three cs_four cs_five cs_odd cs_even cs_dups cs_priority cs_x_first cs_y_second cs_reversed_coords cs_large cs_zeros cs_descending cs_ascending \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_unreach_codec_probeScript.sml word_to_stack_unreach_codec_probe.out \
  uc_skip uc_skip_seq uc_raise uc_return uc_break uc_continue uc_tail uc_merge uc_overlap uc_rest uc_assoc uc_loop uc_must uc_if uc_tail_handler uc_both \
  "$cake_dir/compiler/backend/word_unreachScript.sml" "$cake_dir/compiler/backend"

run_probe reg_alloc_safe_div_probeScript.sml reg_alloc_safe_div_probe.out \
  sd_0 sd_1 sd_2 sd_3 sd_4 sd_5 sd_6 sd_7 sd_8 sd_9 sd_10 sd_11 sd_12 sd_13 \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_first_index_probeScript.sml parmove_first_index_probe.out \
  fi_0 fi_1 fi_2 fi_3 fi_4 fi_5 fi_6 fi_7 fi_8 fi_9 fi_10 fi_11 fi_12 fi_mixed fi_function \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe reg_alloc_state_map_probeScript.sml reg_alloc_state_map_probe.out \
  sm_type sm_bool_state sm_num_state sm_empty sm_one sm_order sm_reverse sm_duplicates sm_large sm_fail_empty sm_fail_first sm_fail_middle sm_fail_last sm_fail_duplicates sm_success sm_state_failure sm_list_state sm_list_error sm_tuple_state sm_empty_failure_callback \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe monad_list_primitives_probeScript.sml monad_list_primitives_probe.out \
  lp_sub_empty lp_sub_empty_bound lp_sub_head lp_sub_middle lp_sub_last lp_sub_length lp_sub_length_bound lp_sub_large lp_sub_large_bound lp_sub_duplicate lp_update_empty lp_update_empty_bound lp_update_head lp_update_middle lp_update_last lp_update_length lp_update_length_bound lp_update_large lp_update_large_bound lp_update_duplicate lp_bool_sub lp_bool_update lp_bool_fail lp_tuple_error lp_tuple_value \
  "$cake_dir/translator/monadic/monad_base/ml_monadBaseScript.sml" "$cake_dir/translator/monadic/monad_base"

run_probe monad_array_length_probeScript.sml monad_array_length_probe.out \
  al_type al_empty al_duplicates al_bool_state al_list_state al_bool_values \
  "$cake_dir/translator/monadic/monad_base/ml_monadBaseScript.sml" "$cake_dir/translator/monadic/monad_base"

run_probe word_alloc_canonize_moves_probeScript.sml word_alloc_canonize_moves_probe.out \
  cm_empty cm_one cm_two cm_three cm_four cm_five cm_odd cm_even cm_dups cm_priority cm_x_first cm_y_second cm_reversed_coords cm_large cm_zeros cm_descending cm_ascending cm_self_moves cm_all_flipped \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_copy_codec_domain_probeScript.sml word_copy_codec_domain_probe.out \
  copy_carry copy_load16 copy_store16 copy_seq_alias copy_if copy_loop copy_must copy_both \
  "$cake_dir/compiler/backend/word_copyScript.sml" "$cake_dir/compiler/backend"

run_probe reg_alloc_initialization_probeScript.sml reg_alloc_initialization_probe.out \
  ira_adj ira_tag ira_degrees ira_coalesced ira_move_related ira_preserved ira_failure ira_zero \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_preservation_shape_probeScript.sml parmove_preservation_shape_probe.out \
  pm_audit_not_use_temp_before_assign_append pm_audit_not_use_temp_before_assign_insert pm_audit_not_use_temp_before_assign_thm pm_audit_step_not_use_temp_before_assign pm_audit_steps_not_use_temp_before_assign pm_audit_pmov_not_use_temp_before_assign pm_audit_parmove_not_use_temp_before_assign pm_audit_ALL_DISTINCT_step pm_audit_ALL_DISTINCT_steps pm_audit_ALL_DISTINCT_pmov pm_audit_ALL_DISTINCT_parmove pm_audit_state_to_list_def pm_audit_step_preserves_moves pm_audit_steps_preserves_moves pm_audit_pmov_preserves_moves pm_audit_parmove_preserves_moves pm_audit_map_state_def pm_audit_inj_on_state_def pm_audit_step_inj_on_state pm_audit_steps_inj_on_state pm_audit_step_MAP_INJ pm_audit_fstep_MAP_INJ pm_audit_pmov_MAP_INJ pm_audit_parmove_MAP_INJ pm_audit_type_state_to_list pm_audit_type_map_state pm_audit_type_inj_on_state \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_all_distinct_step_probeScript.sml parmove_all_distinct_step_probe.out \
  ads_remove ads_start ads_extend ads_save_cycle ads_emit_head ads_emit_last ads_save_none ads_emit_scratch ads_bool ads_scratch_start ads_scratch_save \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_state_to_list_probeScript.sml parmove_state_to_list_probe.out \
  stl_empty stl_pending stl_active stl_emitted stl_order stl_duplicates stl_large stl_bool stl_pairs \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_temp_steps_probeScript.sml parmove_temp_steps_probe.out \
  ptr_remove ptr_start ptr_extend ptr_save_cycle ptr_emit_head ptr_emit_last ptr_save_none ptr_emit_scratch ptr_bool ptr_refl_empty ptr_refl_scratch ptr_cycle_three \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe stackprops_code_labels_probeScript.sml stackprops_code_labels_probe.out \
  sl_skip sl_jump sl_raw sl_location sl_store_none sl_store_some sl_direct_tail sl_indirect_tail_handler sl_direct_tail_handler sl_return_owner sl_return_other_owner sl_return_no_handler sl_sequence_duplicate sl_if_loop sl_nested_handlers \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe parmove_map_state_probeScript.sml parmove_map_state_probe.out \
  pms_empty pms_pending pms_active pms_emitted pms_order pms_constant pms_large pms_bool pms_cross_carrier pms_option_constant \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_alloc_full_ssa_probeScript.sml word_alloc_full_ssa_probe.out \
  fs_skip fs_args fs_assign fs_if fs_big \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_ssa_cc_trans_probeScript.sml word_alloc_ssa_cc_trans_probe.out \
  sc_skip sc_move sc_storeconsts sc_inst sc_assign sc_get sc_store sc_seq sc_mustterminate sc_if sc_if_skip sc_alloc sc_raise sc_opcurrheap sc_return sc_tick sc_set sc_locvalue sc_install sc_codebufferwrite sc_databufferwrite sc_ffi sc_call_tail sc_call_ret sc_call_handler sc_shareinst_load sc_shareinst_store sc_loop sc_loop_break sc_break_free sc_continue_free \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_ssa_helpers_probeScript.sml word_alloc_ssa_helpers_probe.out \
  lnvrm_basic lnvrm_empty fr_basic mp_left mp_right mp_both mp_none sr_moves sr_skip sr_payload ls_mixed ls_empty \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_ssa_trans_inst_probeScript.sml word_alloc_ssa_trans_inst_probe.out \
  sti_skip sti_const sti_binop_reg sti_binop_imm sti_shift_reg sti_shift_imm sti_div sti_addcarry sti_addoverflow sti_suboverflow sti_longmul sti_longdiv sti_load sti_store sti_load32 sti_store8 sti_load16 sti_fpless sti_fpadd sti_movto64 sti_movto32 sti_movfrom64 sti_movfrom32_distinct sti_movfrom32_same ste_var ste_missing ste_nested ste_lookup \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_fix_inconsistencies_probeScript.sml word_alloc_fix_inconsistencies_probe.out \
  ol_hit ol_miss pr_none pr_inl pr_inr fm fms_empty fms_left_only fms_right_only fms_both fi_equal fi_mixed \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe hol_sorting_probeScript.sml hol_sorting_probe.out \
  sorted_type part_type partition_type sorted_empty sorted_single sorted_asc sorted_dup sorted_le_dup sorted_gt sorted_nontrans part_basic part_empty partition_basic partition_bool \
  "$repo_dir/HOL/src/sort/sortingScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe hol_mergesort_probeScript.sml hol_mergesort_probe.out \
  sort2_type sort3_type merge_type mergesortN_type sort2_lt sort2_eq_le sort3_all sort3_dup_le merge_basic merge_unsorted merge_left_empty merge_nontotal msn_full msn_prefix msn_over msn_three_short msn_nontotal msn_zero \
  "$repo_dir/HOL/src/sort/mergesortScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe hol_list_el_probeScript.sml hol_list_el_probe.out \
  hd_type el_type hd_cons hd_bool el_zero el_last el_nested el_large \
  "$repo_dir/HOL/src/list/src/listScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_move_prep_probeScript.sml reg_alloc_move_prep_probe.out \
  ec_basic ec_oob cr_self cr_chain cr_fixed fco_same fco_out_dim fco_adjacent fco_fixed_atemp fco_fixed_high fco_ok um_order um_keep \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_coalesce_probeScript.sml reg_alloc_coalesce_probe.out \
  la_hit la_miss la_bool id_basic id_oob co_same co_adjacent co_fixed_mr co_not_mr co_both_mr co_oob cp_self cp_chain cp_fixed cp_forward cp_oob cm_fixed_second cm_fixed_first cm_order sf_empty sf_first sf_none rmr_basic rmr_oob maxd_basic maxd_tie maxd_oob_dim minc_basic minc_zero_deg \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_worklist_probeScript.sml reg_alloc_worklist_probe.out \
  asw_type aspw_type afw_type aum_type dd_basic dd_zero dd_oob ddeg_basic ddeg_dup ddeg_out_of_dim ddeg_oob_adj asw_basic aspw_basic afw_basic aum_basic ps_basic ps_oob_move_related ps_oob rs_low rs_high_frozen rs_high_not_frozen rs_oob \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_considered_var_probeScript.sml reg_alloc_considered_var_probe.out \
  if_fixed if_atemp if_oob ia_atemp ia_stemp ia_fixed ifk_below ifk_above ifk_equal ifk_stemp cv_atemp cv_fixed_low cv_fixed_high cv_stemp cv_oob doi_fixed_low doi_fixed_high doi_atemp doi_oob doi_state \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_split_degree_probeScript.sml reg_alloc_split_degree_probe.out \
  inc_self inc_other inc_last inc_oob sd_low_self sd_high sd_low_coalesced_k6 sd_eq_k sd_out_of_d sd_oob_bound_true sd_beyond_all sd_state \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_graph_construction_probeScript.sml reg_alloc_graph_construction_probe.out \
  ie_basic ie_self ie_oob ie_oob_first lie_basic lie_fail_mid cie_basic ec_basic ec_fail mt_basic mt_oob mg_delta mg_set mg_branch_none mg_branch_some mg_seq mg_fail eg_basic eg_fail ira_basic \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_move_table_probeScript.sml reg_alloc_move_table_probe.out \
  tc_type uc_type et_type pmi_type umi_type mts_type rm_type tc_fixed tc_atemp tc_stemp et_fixed et_atemp et_stemp uc_empty uc_gap uc_below uc_dup uc_run uc_unsorted uc_unsorted_miss uc_large pmi_empty pmi_existing pmi_bool umi_empty umi_self mts_empty mts_three mts_bool rm_three rm_ties rm_empty_list \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_list_helpers_probeScript.sml reg_alloc_list_helpers_probe.out \
  fi_type si_type fi_empty fi_mixed fi_all_true fi_all_false fi_duplicates fi_state_pred fi_fail_first fi_fail_middle fi_fail_last fi_bool_value fi_large si_empty si_empty_acc si_middle si_dup si_end si_front si_acc si_acc_dup si_unsorted si_unsorted_dup_later si_zero si_large \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_sorted_mem_probeScript.sml reg_alloc_sorted_mem_probe.out \
  sorted_mem_empty sorted_mem_singleton sorted_mem_above sorted_mem_middle sorted_mem_gap sorted_mem_below sorted_mem_tail sorted_mem_duplicate sorted_mem_unsorted_stop sorted_mem_unsorted_continue sorted_mem_zero sorted_mem_large \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_to_stack_program_bitmaps_probeScript.sml word_to_stack_program_bitmaps_probe.out \
  pb_single_skip pb_single_zero_frame pb_single_alloc pb_single_seq pb_single_invalid_bound pb_single_width_one pb_rows_empty pb_rows_repeat_id pb_rows_mixed pb_rows_bool \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe reg_alloc_sort_moves_probeScript.sml reg_alloc_sort_moves_probe.out \
  sort_empty sort_one sort_mixed sort_ties sort_bool merge_empty merge_left merge_right merge_ties merge_unsorted merge_duplicate merge_bool \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_all_distinct_steps_probeScript.sml parmove_all_distinct_steps_probe.out \
  adrtc_scratch adrtc_first adrtc_middle adrtc_last \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_alloc_max3_eq_probeScript.sml word_alloc_max3_eq_probe.out \
  max3_eq_statement max3_zero max3_x max3_y max3_z_after_x max3_z_after_y \
  max3_xy_tie max3_xz_tie max3_yz_tie max3_large \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/misc"
run_probe wordconvs_code_labels_probeScript.sml wordconvs_code_labels_probe.out \
  wl_skip wl_location wl_direct_tail wl_indirect_tail wl_tail_handler wl_both_bodies wl_metadata_omitted wl_return_only wl_duplicate wl_if wl_loop wl_must \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_code_labels_probeScript.sml word_to_stack_code_labels_probe.out \
  lh_load_empty lh_load_many lh_move_zero lh_move_many lh_aux_zero lh_aux_many lh_ret_zero lh_ret_plain lh_ret_handler lh_ret_perf lh_ret_width_one lh_live_zero lh_live_frame lh_live_width_one \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_comp_code_labels_probeScript.sml word_to_stack_comp_code_labels_probe.out \
  cl_skip cl_loc_spilled cl_raise cl_store cl_sequence cl_loop cl_tail_drops_handler cl_indirect_empty cl_indirect_nonempty cl_returning cl_owned_handler cl_wrong_owner cl_zero_frame cl_width_one \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_program_code_labels_probeScript.sml word_to_stack_program_code_labels_probe.out \
  pl_rhs_group pl_empty pl_duplicates pl_spilled pl_owned pl_wrong_owner pl_tail_drop pl_threaded \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe parmove_preserves_moves_step_probeScript.sml parmove_preserves_moves_step_probe.out \
  preserve_4_before preserve_4_after preserve_6_before preserve_6_after preserve_1_before preserve_1_after preserve_8_before preserve_8_after preserve_scratch_before preserve_scratch_after \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_preserves_moves_steps_probeScript.sml parmove_preserves_moves_steps_probe.out \
  rtc_real_before rtc_real_after rtc_scratch_before rtc_scratch_after rtc_changed_source rtc_old_source_absent \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe backendprops_nonzero_labels_probeScript.sml backendprops_nonzero_labels_probe.out \
  nz_empty nz_zero nz_first_zero nz_mixed nz_duplicate nz_large nz_subset nz_subset_left nz_left_union nz_right_union nz_mono nz_bigunion nz_univ_kept nz_univ_zero nz_false_premise \
  "$cake_dir/compiler/backend/semantics/backendPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe reg_alloc_phase_closure_probeScript.sml reg_alloc_phase_closure_probe.out \
  ra_phase_do_simplify ra_phase_do_coalesce ra_phase_do_prefreeze ra_phase_do_freeze ra_phase_do_spill ra_phase_dec_deg ra_phase_dec_degree ra_phase_push_stack ra_phase_is_not_coalesced ra_phase_split_degree ra_phase_sort_moves ra_phase_smerge ra_phase_revive_moves ra_phase_unspill ra_phase_inc_deg ra_phase_is_Fixed ra_phase_is_Atemp ra_phase_is_Fixed_k ra_phase_considered_var ra_phase_deg_or_inf ra_phase_bg_ok ra_phase_consistency_ok ra_phase_coalesce_parent ra_phase_canonize_move ra_phase_st_ex_FIRST ra_phase_respill ra_phase_reset_move_related ra_phase_st_ex_list_MIN_cost ra_phase_st_ex_list_MAX_deg \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe reg_alloc_state_partition_probeScript.sml reg_alloc_state_partition_probe.out \
  sp_type sp_empty sp_singleton_true sp_singleton_false sp_all_true sp_all_false sp_mixed sp_reverse sp_duplicates sp_large sp_fail_empty sp_fail_first sp_fail_middle sp_fail_last sp_fail_duplicate sp_state_predicate sp_state_failure sp_bool_value sp_bool_state sp_list_state sp_list_error sp_tuple_state sp_empty_always_failure \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe reg_alloc_state_foreach_probeScript.sml reg_alloc_state_foreach_probe.out \
  sf_type sf_empty sf_order sf_reverse sf_duplicates sf_fail_empty sf_fail_first sf_fail_middle sf_fail_last sf_bool_result sf_list_state sf_bool_state \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe parmove_preserves_moves_pmov_probeScript.sml parmove_preserves_moves_pmov_probe.out \
  pmv_terminal pmv_pending pmv_output \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_alloc_get_heuristics_probeScript.sml word_alloc_get_heuristics_probe.out \
  gh_empty_even gh_empty_odd gh_move_even gh_move_odd gh_duplicates gh_self_call gh_other_call gh_get_cost gh_large_even gh_large_odd gh_move_structure gh_dup_structure gh_self_structure gh_get_structure \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_compile_lookup_probeScript.sml word_to_stack_compile_lookup_probe.out \
  lookup_duplicate_first lookup_later_threaded lookup_missing lookup_bool_first \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_register_labels_probeScript.sml word_to_stack_register_labels_probe.out \
  wr_physical wr_boundary wr_spilled wr_zero wr_large wr_labelled \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe parmove_all_distinct_wrapper_probeScript.sml parmove_all_distinct_wrapper_probe.out \
  pad_original_statement pad_empty pad_self pad_chain pad_swap pad_cycle \
  pad_shared_source pad_duplicate_boundary \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe word_alloc_max_inst_probeScript.sml word_alloc_max_inst_probe.out \
  mi_skip mi_const mi_binreg mi_binimm mi_shift mi_div mi_longdiv mi_load8 mi_fp64_to mi_fp32_to mi_fp80_from mi_fpignored mi_original_theorem \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"

run_probe word_alloc_max_exp_probeScript.sml word_alloc_max_exp_probe.out \
  me_const me_lookup me_var me_load me_empty me_nested me_duplicate me_shiftleft me_shiftright me_zero me_original_theorem \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe wordconvs_exp_mono_probeScript.sml wordconvs_exp_mono_probe.out \
  em_var em_nested em_empty em_const em_lookup em_duplicate em_large em_guard_needed em_original_theorem \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_preserves_moves_parmove_probeScript.sml parmove_preserves_moves_parmove_probe.out \
  pmm_shared pmm_cycle pmm_bool pmm_output pmm_self pmm_empty \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_convs_every_var_inst_mono_probeScript.sml word_convs_every_var_inst_mono_probe.out \
  im_original_theorem im_skip im_const im_binreg im_binimm im_shift im_div im_longdiv im_load8 im_load16_ignored im_fpless im_fp64_to im_fp32_to im_fp80_from im_fpignored im_fp32_reject \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe parmove_fstep_map_inj_probeScript.sml parmove_fstep_map_inj_probe.out \
  pfm_statement pfm_empty pfm_self pfm_start pfm_found pfm_emit pfm_cycle pfm_no_cycle pfm_temp \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe parmove_scratch_order_wrapper_probeScript.sml parmove_scratch_order_wrapper_probe.out \
  pso_original_statement pso_empty pso_self pso_chain pso_swap pso_cycle pso_shared_source pso_bool_swap pso_duplicate_boundary \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"
run_probe wordconvs_name_mono_probeScript.sml wordconvs_name_mono_probe.out \
  nm_empty nm_single nm_both nm_invalid nm_guard_needed nm_original_theorem \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe wordconvs_program_mono_probeScript.sml wordconvs_program_mono_probe.out \
  pm_skip pm_moves pm_inst pm_assign pm_seq pm_alloc pm_loop pm_call_none pm_call_return pm_call_handler pm_guard_needed pm_original_theorem \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stackprops_label_safety_probeScript.sml stackprops_label_safety_probe.out \
  safety_empty safety_self_zero safety_self_one safety_missing_zero safety_external_zero safety_external_one safety_missing_one safety_higher_entry safety_owned_handler safety_foreign_handler \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe parmove_step_map_inj_probeScript.sml parmove_step_map_inj_probe.out \
  smi_original_statement smi_remove_self smi_start smi_extend smi_save smi_emit_head smi_emit_last smi_scoped_collapse smi_scoped_injectivity \
  "$cake_dir/compiler/backend/reg_alloc/parmoveScript.sml" "$cake_dir/compiler/backend/reg_alloc"

run_probe word_alloc_max_var_max_probeScript.sml word_alloc_max_var_max_probe.out \
  mvm_original_statement mvm_skip mvm_move mvm_move_empty mvm_inst64 mvm_inst32 mvm_assign mvm_get mvm_store mvm_tail_ignored mvm_tail_empty mvm_call_body mvm_call_cutset mvm_call_values mvm_handler_value mvm_handler_body mvm_seq mvm_must mvm_if_reg mvm_if_imm mvm_alloc mvm_consts mvm_install mvm_codewrite mvm_datawrite mvm_ffi mvm_raise mvm_heap mvm_return mvm_return_empty mvm_tick mvm_loc mvm_set mvm_share mvm_loop_exit mvm_loop_body mvm_break mvm_continue mvm_width1_huge mvm_inst_load16_ignored mvm_inst_store16_ignored mvm_inst_fp80_from mvm_call_arguments mvm_call_nested_handler mvm_cutsets_nonwf mvm_op_list_nested mvm_inst_fp_ignored \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_setup_probeScript.sml ssa_setup_probe.out \
  ss_even ss_empty ss_duplicates ss_invalid ss_one ss_setup0 ss_setup1 ss_setup3 ss_setup80 even_list_def next_var_rename_def list_next_var_rename_def setup_ssa_def ss_setup_1_to_80 ss_setup_80_to_1 ss_setup_original_type \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe ssa_map_ok_probeScript.sml ssa_map_ok_probe.out \
  sm_empty sm_valid sm_at_bound sm_physical sm_invalid sm_definition \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_locals_rel_probeScript.sml ssa_locals_rel_probe.out \
  sl_empty sl_valid sl_missing_map sl_missing_target sl_wrong_value sl_bound sl_bound_ok sl_invalid sl_definition sl_original_type \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_register_class_probeScript.sml ssa_register_class_probe.out \
  rc_alloc1 rc_stack3 rc_physical0 rc_physical2 rc_alloc5 rc_stack7 rc_large_alloc rc_large_stack rc_alloc_source_replay rc_stack_source_replay \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe ssa_rename_lookup_probeScript.sml ssa_rename_lookup_probe.out \
  rename_empty rename_overwrite rename_invalid rename_order rename_large \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"

run_probe ssa_merge_route_probeScript.sml ssa_merge_route_probe.out \
  route_empty route_missing route_equal route_unequal route_tail route_duplicate_names route_duplicate_maps route_big \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe ssa_merge_moves_probeScript.sml ssa_merge_moves_probe.out \
  merge_empty merge_missing_both merge_missing_left merge_missing_right merge_equal merge_unequal merge_tail_order merge_duplicate merge_invalid merge_big merge_definition merge_original_type \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe list_next_var_rename_lemma1_probeScript.sml list_next_var_rename_lemma1_probe.out \
  lnvr1_original_statement lnvr1_empty lnvr1_duplicates lnvr1_invalid lnvr1_collision lnvr1_zero_duplicates lnvr1_odd_start lnvr1_huge lnvr1_range \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe stackprops_forbidden_operations_probeScript.sml stackprops_forbidden_operations_probe.out \
  forbid_skip forbid_inst forbid_get forbid_set forbid_heap forbid_call_empty forbid_seq forbid_if forbid_loop forbid_jump forbid_alloc forbid_store_consts forbid_raise forbid_return forbid_break forbid_continue forbid_ffi forbid_tick forbid_loc forbid_install forbid_shmem forbid_code_write forbid_data_write forbid_raw_call forbid_stack_alloc forbid_stack_free forbid_stack_store forbid_stack_store_any forbid_stack_load forbid_stack_load_any forbid_stack_get_size forbid_stack_set_size forbid_bitmap_load forbid_halt forbid_call_handler_install forbid_call_handler_shmem forbid_call_return_install forbid_call_return_shmem forbid_call_both forbid_call_safe forbid_seq_left forbid_seq_right forbid_if_left forbid_if_right forbid_loop_install forbid_loop_shmem \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_alloc_limit_var_probeScript.sml word_alloc_limit_var_probe.out \
  lv_original_definition lv_original_type lv_residue0 lv_residue1 lv_residue2 lv_residue3 lv_residue4 lv_skip1 lv_seven lv_eight lv_ignored16 lv_tail_handler lv_call_body lv_huge \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe ssa_rename_properties_probeScript.sml ssa_rename_properties_probe.out \
  rp_empty_alloc rp_empty_stack rp_alloc_duplicates rp_stack_duplicates rp_existing rp_overwrite rp_invalid rp_huge rp_full_source_replay \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_max_inst_route_probeScript.sml word_max_inst_route_probe.out \
  load16_max store16_max load32_max store8_max load16_limit store16_limit load32_limit \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_handler_safety_probeScript.sml word_to_stack_handler_safety_probe.out \
  hls_empty hls_duplicates hls_owned hls_wrong_owner hls_wrong_zero hls_wrong_one hls_tail_drop hls_same_owner_twice hls_nested hls_nested_bad hls_threaded hls_width_one \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe wordconvs_label_safety_probeScript.sml wordconvs_label_safety_probe.out \
  wcs_empty wcs_skip wcs_self wcs_missing wcs_external wcs_univ wcs_duplicates wcs_cross wcs_owned wcs_wrong_owner wcs_tail_foreign wcs_tail_missing wcs_nested wcs_width_one \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_no_shmemop_helpers_probeScript.sml word_to_stack_no_shmemop_helpers_probe.out \
  nsh_move_empty nsh_move_rr nsh_move_rs nsh_move_sr nsh_move_ss nsh_move_multi nsh_move_width1 nsh_load_empty nsh_load_loads nsh_load_forbidden nsh_write1_register nsh_write1_stack nsh_write1_forbidden nsh_write2_register nsh_write2_stack nsh_write2_forbidden nsh_live_zero nsh_live_nonzero nsh_live_width1 nsh_stack_zero nsh_stack_positive nsh_stack_forbidden \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_handler_frame_carriers_probeScript.sml word_to_stack_handler_frame_carriers_probe.out \
  hcf_push_type hcf_pop_type hcf_push_64_F hcf_pop_64_F_skip hcf_pop_64_F_forbidden hcf_push_64_T hcf_pop_64_T_skip hcf_pop_64_T_forbidden hcf_push_1_F hcf_pop_1_F_skip hcf_pop_1_F_forbidden hcf_push_1_T hcf_pop_1_T_skip hcf_pop_1_T_forbidden \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe ssa_map_extend_probeScript.sml ssa_map_extend_probe.out \
  se_empty_alloc se_empty_stack se_existing se_overwrite se_invalid se_huge_alloc se_huge_stack se_physical_premise se_at_bound_premise se_full_source_replay \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_register_flip_probeScript.sml ssa_register_flip_probe.out \
  rf_residue_0 rf_equalities_0 rf_residue_1 rf_equalities_1 rf_residue_2 rf_equalities_2 rf_residue_3 rf_equalities_3 rf_residue_4 rf_equalities_4 rf_residue_5 rf_equalities_5 rf_residue_6 rf_equalities_6 rf_residue_7 rf_equalities_7 rf_alloc_application_0 rf_alloc_application_1 rf_alloc_application_2 rf_stack_application_0 rf_stack_application_1 rf_stack_application_2 rf_is_alloc_var_flip_source_replay rf_is_stack_var_flip_source_replay rf_flip_rw_source_replay \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_locals_bounds_probeScript.sml ssa_locals_bounds_probe.out \
  lb_more \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_alloc_move_head_probeScript.sml word_alloc_move_head_probe.out \
  mh_original_statement mh_original_types mh_original_state_type mh_empty mh_single mh_parallel mh_overwrite mh_self mh_same_source mh_malformed mh_huge mh_missing_source mh_duplicate_destination mh_bad_tail \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_alloc_limit_arithmetic_probeScript.sml word_alloc_limit_arithmetic_probe.out \
  la_original_numeric_proof la_0 la_1 la_2 la_3 la_4 la_7 la_8 la_15 la_16 la_1208925819614629174706176 la_1208925819614629174706177 la_1208925819614629174706178 la_1208925819614629174706179 \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_no_shmemop_call_core_probeScript.sml word_to_stack_no_shmemop_call_core_probe.out \
  cc_ret_zero cc_ret_one cc_ret_many cc_ret_width1 cc_prefix_1 cc_suffix_1 cc_prefix_32 cc_suffix_32 cc_prefix_64 cc_suffix_64 cc_prefix_80 cc_suffix_80 \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_program_max_unrestricted_probeScript.sml word_program_max_unrestricted_probe.out \
  seq16_max seq16_limit tail16_max tail16_limit both16_max both16_limit loop16_max loop16_limit \
  "$cake_dir/compiler/backend/wordLangScript.sml" "$cake_dir/compiler/backend"
run_probe ssa_locals_swap_probeScript.sml ssa_locals_swap_probe.out \
  sw_type_ssaL sw_type_cst sw_type_st sw_type_ssaR sw_type_na sw_full \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_map_preservation_probeScript.sml ssa_map_preservation_probe.out \
  mi_empty mi_retain_alloc mi_retain_stack mi_drop mi_invalid mi_branch mi_huge ms_empty ms_stack ms_overwrite ms_extend ms_invalid ms_huge ms_physical_guard ms_bound_guard ssa_map_ok_inter_source_replay ssa_map_ok_insert_source_replay mi_original_types \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_locals_physical_insert_probeScript.sml ssa_locals_physical_insert_probe.out \
  pi_empty pi_empty_existing pi_live pi_overwrite pi_branch pi_invalid pi_huge pi_generic_nat pi_nonphysical_guard pi_invalid_map_guard pi_full_source_replay pi_original_types \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_merge_frame_probeScript.sml ssa_merge_frame_probe.out \
  mf_full_source_replay mf_empty mf_missing_both mf_missing_left mf_missing_right mf_equal mf_unequal mf_tail_order mf_duplicate mf_invalid mf_big \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_code_label_safety_probeScript.sml word_to_stack_code_label_safety_probe.out \
  cls_empty cls_self cls_missing cls_external cls_duplicates cls_owned cls_wrong_owner cls_tail_missing cls_threaded cls_width_one \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_convs_code_label_carriers_probeScript.sml word_convs_code_label_carriers_probe.out \
  clc_bool clc_unit clc_list clc_option \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_convs_no_alloc_def_probeScript.sml word_convs_no_alloc_def_probe.out \
  wcna_01_mt wcna_02_seq wcna_03_loop wcna_04_if wcna_05_call wcna_06_alloc wcna_07_loc wcna_08_share wcna_09_install wcna_10_skip wcna_11_move wcna_12_inst wcna_13_assign wcna_14_get wcna_15_set wcna_16_store wcna_17_consts wcna_18_raise wcna_19_return wcna_20_break wcna_21_continue wcna_22_tick wcna_23_heap wcna_24_code wcna_25_data wcna_26_ffi wcna_call_none_none_width1 wcna_call_return_only_width1 wcna_call_both_present_width1 \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_convs_no_mt_def_probeScript.sml word_convs_no_mt_def_probe.out \
  wcnm_01_mt wcnm_02_seq wcnm_03_loop wcnm_04_if wcnm_05_call wcnm_06_alloc wcnm_07_loc wcnm_08_share wcnm_09_install wcnm_10_skip wcnm_11_move wcnm_12_inst wcnm_13_assign wcnm_14_get wcnm_15_set wcnm_16_store wcnm_17_consts wcnm_18_raise wcnm_19_return wcnm_20_break wcnm_21_continue wcnm_22_tick wcnm_23_heap wcnm_24_code wcnm_25_data wcnm_26_ffi wcnm_call_none_none_width1 wcnm_call_return_only_width1 wcnm_call_both_present_width1 \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_convs_no_share_inst_def_probeScript.sml word_convs_no_share_inst_def_probe.out \
  wcns_01_mt wcns_02_seq wcns_03_loop wcns_04_if wcns_05_call wcns_06_alloc wcns_07_loc wcns_08_share wcns_09_install wcns_10_skip wcns_11_move wcns_12_inst wcns_13_assign wcns_14_get wcns_15_set wcns_16_store wcns_17_consts wcns_18_raise wcns_19_return wcns_20_break wcns_21_continue wcns_22_tick wcns_23_heap wcns_24_code wcns_25_data wcns_26_ffi wcns_call_none_none_width1 wcns_call_return_only_width1 wcns_call_both_present_width1 \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe word_to_stack_no_shmemop_return_probeScript.sml word_to_stack_no_shmemop_return_probe.out \
  cr_0_safe cr_0_forbidden cr_1_safe cr_1_forbidden cr_2_safe cr_2_forbidden cr_3_safe cr_3_forbidden cr_4_safe cr_4_forbidden cr_5_safe cr_5_forbidden cr_6_safe cr_6_forbidden cr_7_safe cr_7_forbidden \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_no_shmemop_inst_probeScript.sml word_to_stack_no_shmemop_inst_probe.out \
  ci_skip ci_const ci_binop_imm ci_binop_reg ci_shift_imm ci_shift_reg ci_div ci_long_mul ci_long_div ci_carry ci_add_overflow ci_sub_overflow ci_load ci_load8 ci_load16 ci_load32 ci_store ci_store8 ci_store16 ci_store32 ci_fpless ci_fplessequal ci_fpequal ci_fpabs ci_fpneg ci_fpsqrt ci_fpadd ci_fpsub ci_fpmul ci_fpdiv ci_fpfma ci_fpmov ci_fpmovtoreg ci_fpmovfromreg ci_fptoint ci_fpfromint ci_fpmovtoreg1 ci_fpmovfromreg1 ci_fpmovtoreg32 ci_fpmovfromreg32 ci_fpmovtoreg80 ci_fpmovfromreg80 \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe real_sqrt_round_agreement_special_probeScript.sml real_sqrt_round_agreement_special_probe.out \
  sqrt_zero_pinf sqrt_zero_nz sqrt_positive_pinf sqrt_positive_nz sqrt_negative_pinf sqrt_negative_nz sqrt_negative_flags_all_modes sqrt_quiet_nan_flags_all_modes \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" "$hol_dir/src/floating-point"

run_probe ssa_map_bounds_probeScript.sml ssa_map_bounds_probe.out \
  mb_empty mb_valid mb_same mb_bound mb_physical mb_invalid mb_large_physical mb_large mb_overwrite mb_more \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"




run_probe word_alloc_limit_props_probeScript.sml word_alloc_limit_props_probe.out \
  lp_full_source_replay lp_residue0 lp_residue1 lp_residue2 lp_residue3 lp_residue4 lp_skip1 lp_seven lp_eight lp_ignored16 lp_tail_handler lp_call_body lp_huge \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"



run_probe word_to_stack_no_shmemop_handlers_probeScript.sml word_to_stack_no_shmemop_handlers_probe.out \
  hn_push_source hn_pop_source hn_args_source hn_push_type hn_pop_type hn_args_type hn_push_64_F hn_pop_64_F_safe hn_pop_64_F_forbidden hn_push_64_T hn_pop_64_T_safe hn_pop_64_T_forbidden hn_push_1_F hn_pop_1_F_safe hn_pop_1_F_forbidden hn_push_1_T hn_pop_1_T_safe hn_pop_1_T_forbidden hn_args_direct_zero hn_args_direct_perf hn_args_indirect_small hn_args_indirect_huge \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe stack_to_lab_native_probeScript.sml stack_to_lab_native_probe.out \
  native_flatten_definition native_seq_tail_tree native_if_left_skip_tree native_if_right_skip_tree native_if_left_noreturn_tree native_if_right_noreturn_tree native_if_fallthrough_tree native_loop_tree native_call_handler_tree native_section_seq native_tick native_inst native_halt native_raise native_return native_break_missing native_continue_missing native_rawcall native_tailcall_label native_tailcall_register native_lower native_location native_install native_shared native_buffer native_fallback native_width1 native_width80 native_ffi native_fallback_01 native_fallback_02 native_fallback_03 native_fallback_04 native_fallback_05 native_fallback_06 native_fallback_07 native_fallback_08 native_fallback_09 native_fallback_10 native_fallback_11 native_fallback_12 native_fallback_13 native_fallback_14 native_fallback_15 native_if_both_skip native_call_return_only \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" "$cake_dir/compiler/backend"
run_probe ssa_locals_insert_probeScript.sml ssa_locals_insert_probe.out \
  fi_full fi_source_type fi_target_type fi_value_type fi_set_var_full fi_empty fi_preserve \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_map_step_probeScript.sml ssa_map_step_probe.out \
  ml_full ml_empty ml_valid ml_rejected ml_physical ml_invalid ml_large \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_merge_correct_right_probeScript.sml ssa_merge_correct_right_probe.out \
  mr_full mr_type_ls mr_type_na mr_type_ssaL mr_type_ssaR mr_type_stR mr_type_cstR mr_type_pri \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_merge_correct_left_probeScript.sml ssa_merge_correct_left_probe.out \
  mlc_full mlc_type_ls mlc_type_na mlc_type_ssaL mlc_type_ssaR mlc_type_stL mlc_type_cstL mlc_type_pri \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_physical_state_updates_probeScript.sml ssa_physical_state_updates_probe.out \
  ph_set_full ph_set_type_st ph_set_type_cst ph_list_full ph_list_type_st ph_list_type_cst \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_merge_move_lookups_probeScript.sml ssa_merge_move_lookups_probe.out \
  frame3_full_source_replay frame3_empty frame3_absent frame3_outside frame3_absent_result frame3_outside_result frame3_common_guard \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe loop_to_word_label_handlers_probeScript.sml loop_to_word_label_handlers_probe.out \
  comp_l_invariant_source_replay good_handlers_comp_source_replay loop_to_word_good_handlers_source_replay loop_to_word_comp_SND_LE_source_replay lh_nested64_result lh_nested64_owner lh_nested64_counter lh_nested64_handlers lh_nested1_result lh_nested1_owner lh_nested1_counter lh_nested1_handlers lh_nested80_result lh_nested80_owner lh_nested80_counter lh_nested80_handlers lh_ignored_tail_result lh_ignored_tail_owner lh_ignored_tail_counter lh_ignored_tail_handlers lh_program_result lh_program_handlers lh_wrong_owner \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" "$cake_dir/pancake/proofs"
run_probe word_to_stack_no_shmemop_flat_probeScript.sml word_to_stack_no_shmemop_flat_probe.out \
  fe_move_1 fe_return_1 fe_heap_1 fe_set_1 fe_get_1 fe_alloc_1 fe_consts_1 fe_loc_1 fe_install_1 fe_code_1 fe_data_1 fe_ffi_1 fe_move_32 fe_return_32 fe_heap_32 fe_set_32 fe_get_32 fe_alloc_32 fe_consts_32 fe_loc_32 fe_install_32 fe_code_32 fe_data_32 fe_ffi_32 fe_move_64 fe_return_64 fe_heap_64 fe_set_64 fe_get_64 fe_alloc_64 fe_consts_64 fe_loc_64 fe_install_64 fe_code_64 fe_data_64 fe_ffi_64 fe_move_80 fe_return_80 fe_heap_80 fe_set_80 fe_get_80 fe_alloc_80 fe_consts_80 fe_loc_80 fe_install_80 fe_code_80 fe_data_80 fe_ffi_80 fe_set_bitmap fe_set_const fe_set_lookup fe_set_load fe_set_op fe_set_shift \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_no_shmemop_recursive_probeScript.sml word_to_stack_no_shmemop_recursive_probe.out \
  rc_must_1 rc_loop_1 rc_seq_1 rc_reg_1 rc_imm_yes_1 rc_imm_no_1 rc_must_32 rc_loop_32 rc_seq_32 rc_reg_32 rc_imm_yes_32 rc_imm_no_32 rc_must_64 rc_loop_64 rc_seq_64 rc_reg_64 rc_imm_yes_64 rc_imm_no_64 rc_must_80 rc_loop_80 rc_seq_80 rc_reg_80 rc_imm_yes_80 rc_imm_no_80 rc_must_shared rc_must_invalid rc_must_ignored_handler rc_loop_shared rc_loop_invalid rc_loop_ignored_handler rc_seq_shared rc_seq_invalid rc_seq_ignored_handler rc_reg_shared rc_reg_invalid rc_reg_ignored_handler rc_imm_yes_shared rc_imm_yes_invalid rc_imm_yes_ignored_handler rc_imm_no_shared rc_imm_no_invalid rc_imm_no_ignored_handler \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe ssa_rename_property_wrappers_probeScript.sml ssa_rename_property_wrappers_probe.out \
  rw_core_full rw_move_full rw_move_type rw_single_full \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe ssa_option_lookup_subset_probeScript.sml ssa_option_lookup_subset_probe.out \
  os_full os_type_ssa os_type_cst_locs os_type_ls \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_rename_move_preserve_weak_probeScript.sml ssa_rename_move_preserve_weak_probe.out \
  rmw_full rmw_type_st rmw_type_cst rmw_type_ssa rmw_type_na rmw_type_ls \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe loop_to_word_program_names_probeScript.sml loop_to_word_program_names_probe.out \
  first_compile_prog_all_distinct_source_replay first_compile_all_distinct_source_replay mem_prog_mem_compile_prog_source_replay lookup_prog_some_lookup_compile_prog_source_replay pn_duplicate_result pn_distinct_result pn_duplicate_names pn_distinct_names pn_first_lookup pn_missing_lookup pn_distinct_theorem pn_compile_theorem pn_member_theorem pn_lookup_theorem \
  "$cake_dir/pancake/proofs/loop_to_wordProofScript.sml" "$cake_dir/pancake/proofs"

run_probe lab_validity_native_probeScript.sml lab_validity_native_probe.out \
  line_ok_asm_skip line_ok_asm_cbw line_ok_label line_ok_labasm_halt line_ok_asm_badreg all_enc_ok_one_ok all_enc_ok_one_bad cbw_to_asm_store8 cbw_to_asm_sharemem sec_ok_one_ok sec_ok_one_bad sec_ok_empty all_enc_ok_two_ok all_enc_ok_empty native_cbw_width1_huge native_shared_width80 native_cbw_definition native_line_definition native_section_definition \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_to_lab_nonrecursive_validity_probeScript.sml stack_to_lab_nonrecursive_validity_probe.out \
  native_flatten_full_source_proof native_cbw_application native_shared_application \
  "$cake_dir/compiler/backend/proofs/stack_to_labProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_no_shmemop_tail_probeScript.sml word_to_stack_no_shmemop_tail_probe.out \
  tc_direct0_1 tc_directmany_1 tc_indirect0_1 tc_indirectsmall_1 tc_indirectlarge_1 tc_direct0_32 tc_directmany_32 tc_indirect0_32 tc_indirectsmall_32 tc_indirectlarge_32 tc_direct0_64 tc_directmany_64 tc_indirect0_64 tc_indirectsmall_64 tc_indirectlarge_64 tc_direct0_80 tc_directmany_80 tc_indirect0_80 tc_indirectsmall_80 tc_indirectlarge_80 tc_ignored_safe tc_ignored_shared \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_no_shmemop_returning_probeScript.sml word_to_stack_no_shmemop_returning_probe.out \
  cr_direct0_1 cr_directmany_1 cr_indirect0_1 cr_indirectsmall_1 cr_indirectlarge_1 cr_direct0_32 cr_directmany_32 cr_indirect0_32 cr_indirectsmall_32 cr_indirectlarge_32 cr_direct0_64 cr_directmany_64 cr_indirect0_64 cr_indirectsmall_64 cr_indirectlarge_64 cr_direct0_80 cr_directmany_80 cr_indirect0_80 cr_indirectsmall_80 cr_indirectlarge_80 cr_shared cr_invalid \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_no_shmemop_handled_probeScript.sml word_to_stack_no_shmemop_handled_probe.out \
  ch_direct0_1 ch_directmany_1 ch_indirect0_1 ch_indirectsmall_1 ch_indirectlarge_1 ch_direct0_32 ch_directmany_32 ch_indirect0_32 ch_indirectsmall_32 ch_indirectlarge_32 ch_direct0_64 ch_directmany_64 ch_indirect0_64 ch_indirectsmall_64 ch_indirectlarge_64 ch_direct0_80 ch_directmany_80 ch_indirect0_80 ch_indirectsmall_80 ch_indirectlarge_80 ch_return_shared ch_handler_shared ch_return_invalid ch_handler_invalid ch_both_shared ch_both_invalid \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_no_shmemop_primitives_probeScript.sml word_to_stack_no_shmemop_primitives_probe.out \
  cp_skip_1 cp_assign_1 cp_store_1 cp_raise_1 cp_break_1 cp_continue_1 cp_tick_1 cp_skip_32 cp_assign_32 cp_store_32 cp_raise_32 cp_break_32 cp_continue_32 cp_tick_32 cp_skip_64 cp_assign_64 cp_store_64 cp_raise_64 cp_break_64 cp_continue_64 cp_tick_64 cp_skip_80 cp_assign_80 cp_store_80 cp_raise_80 cp_break_80 cp_continue_80 cp_tick_80 cp_load_valid cp_load_invalid cp_store_valid cp_store_invalid \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe stack_to_lab_full_encoding_probeScript.sml stack_to_lab_full_encoding_probe.out \
  full_flatten_source_proof full_compile_all_source_statement full_compile_all_application full_compile_all_sections \
  "$cake_dir/compiler/backend/proofs/stack_to_labProofScript.sml" "$cake_dir/compiler/backend/proofs"
# Actual scheduler route and native temporary/frame sentinels.
run_probe word_to_stack_scheduler_route_probeScript.sml word_to_stack_scheduler_route_probe.out \
  sr_order_empty sr_order_swap sr_order_duplicate sr_none_slot sr_spill_cycle sr_spill_zero_frame \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"
run_probe ssa_get_set_vars_probeScript.sml ssa_get_set_vars_probe.out \
  get_vars_list_insert_eq_gen_full get_vars_set_vars_eq_full \
  gvi_type_st gvi_type_ls gvi_type_x gvi_type_locs gvi_type_a gvi_type_b \
  gsv_type_cst gsv_type_ls gsv_type_x \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_locals_list_rename_probeScript.sml ssa_locals_list_rename_probe.out \
  lr_full lr_type_xs lr_type_ssa lr_type_na lr_type_stloc lr_type_cstloc \
  lr_type_ys lr_type_ssaOut lr_type_naOut lr_type_ls \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_setup_props_probeScript.sml ssa_setup_props_probe.out \
  setup_full setup_type_lim setup_type_n setup_type_st setup_type_prog \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_comp_no_shmemop_probeScript.sml word_to_stack_comp_no_shmemop_probe.out \
  cs_full cs_conf_type cs_perf_type cs_source_type cs_bitmap_type cs_frame_type cs_target_type cs_residual_type cs_nested_1 cs_if_1 cs_ignored_1 cs_nested_32 cs_if_32 cs_ignored_32 cs_nested_64 cs_if_64 cs_ignored_64 cs_nested_80 cs_if_80 cs_ignored_80 \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe machine_ieee_fp64_declarations_probeScript.sml machine_ieee_fp64_declarations_probe.out \
  float_to_fp64_def fp64_abs_def fp64_add_def fp64_add_with_flags_def fp64_bottom_def fp64_compare_def fp64_div_def fp64_div_with_flags_def fp64_equal_def fp64_greaterEqual_def fp64_greaterThan_def fp64_isFinite_def fp64_isInfinite_def fp64_isIntegral_def fp64_isNan_def fp64_isNormal_def fp64_isSignallingNan_def fp64_isSubnormal_def fp64_isZero_def fp64_lessEqual_def fp64_lessThan_def fp64_mul_add_def fp64_mul_add_with_flags_def fp64_mul_def fp64_mul_sub_def fp64_mul_sub_with_flags_def fp64_mul_with_flags_def fp64_negInf_def fp64_negMin_def fp64_negZero_def fp64_negate_def fp64_posInf_def fp64_posMin_def fp64_posZero_def fp64_roundToIntegral_def fp64_sqrt_def fp64_sqrt_with_flags_def fp64_sub_def fp64_sub_with_flags_def fp64_to_float_def fp64_to_int_def fp64_to_real_def fp64_to_value_def fp64_top_def int_to_fp64_def real_to_fp64_def real_to_fp64_with_flags_def \
  "$repo_dir/HOL/src/floating-point/machine_ieeeScript.sml" "$hol_dir/src/floating-point"

run_probe ssa_rename_move_preserve_probeScript.sml ssa_rename_move_preserve_probe.out \
  rms_full rms_type_st rms_type_cst rms_type_ssa rms_type_na rms_type_ls \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_fake_moves_correct_left_probeScript.sml ssa_fake_moves_correct_left_probe.out \
  fml_full fml_type_ls fml_type_na fml_type_ssaL fml_type_ssaR fml_type_stL fml_type_cstL fml_type_prio \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_fake_moves_correct_right_probeScript.sml ssa_fake_moves_correct_right_probe.out \
  fmr_full fmr_type_ls fmr_type_na fmr_type_ssaL fmr_type_ssaR fmr_type_stR fmr_type_cstR fmr_type_prio \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_fix_inconsistencies_correct_left_probeScript.sml ssa_fix_inconsistencies_correct_left_probe.out \
  ficl_full ficl_type_na ficl_type_ssaL ficl_type_ssaR ficl_type_prio ficl_type_stL ficl_type_cstL \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_fix_inconsistencies_correct_right_probeScript.sml ssa_fix_inconsistencies_correct_right_probe.out \
  ficr_full ficr_type_na ficr_type_ssaL ficr_type_ssaR ficr_type_prio ficr_type_stR ficr_type_cstR \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_no_shmemop_programs_probeScript.sml word_to_stack_no_shmemop_programs_probe.out \
  pl_full pl_conf_type pl_perf_type pl_register_type pl_source_type pl_bitmap_type pl_outputs_type pl_frames_type pl_residual_type pl_empty_1 pl_safe_1 pl_ignored_1 pl_shared_1 pl_empty_32 pl_safe_32 pl_ignored_32 pl_shared_32 pl_empty_64 pl_safe_64 pl_ignored_64 pl_shared_64 pl_empty_80 pl_safe_80 pl_ignored_80 pl_shared_80 \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_to_stack_no_shmemop_top_probeScript.sml word_to_stack_no_shmemop_top_probe.out \
  tp_full tp_conf_type tp_source_type tp_bitmaps_type tp_config_type tp_frames_type tp_outputs_type tp_empty_1 tp_safe_1 tp_ignored_1 tp_shared_1 tp_empty_32 tp_safe_32 tp_ignored_32 tp_shared_32 tp_empty_64 tp_safe_64 tp_ignored_64 tp_shared_64 tp_empty_80 tp_safe_80 tp_ignored_80 tp_shared_80 \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_exp_correct_probeScript.sml ssa_cc_trans_exp_correct_probe.out \
  sec_full sec_type_st sec_type_w sec_type_cst sec_type_ssa sec_type_na sec_type_res \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_fix_inconsistencies_props_probeScript.sml ssa_fix_inconsistencies_props_probe.out \
  fip_full fip_type_prio fip_type_ssaL fip_type_ssaR fip_type_na fip_type_a fip_type_b fip_type_nextOut fip_type_ssaU \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe stack_to_lab_executed_codec_probeScript.sml stack_to_lab_executed_codec_probe.out \
  codec_source_addcarry codec_source_addoverflow codec_source_memoffset codec_source_cbw codec_source_cbw_store_order codec_source_name_bytes codec_source_ffi codec_source_nonzero_position codec_source_wide_constant \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" "$cake_dir/compiler/backend"
run_probe word_to_stack_comp_no_install_probeScript.sml word_to_stack_comp_no_install_probe.out \
  ci_full ci_conf_type ci_perf_type ci_source_type ci_bitmap_type ci_frame_type ci_target_type ci_residual_type ci_skip_64 ci_move_64 ci_inst_64 ci_assign_64 ci_get_64 ci_set_64 ci_store_64 ci_alloc_64 ci_store_consts_64 ci_raise_64 ci_return_64 ci_break_64 ci_continue_64 ci_tick_64 ci_heap_64 ci_loc_64 ci_install_64 ci_code_write_64 ci_data_write_64 ci_ffi_64 ci_share_64 ci_must_64 ci_loop_64 ci_seq_64 ci_branch_64 ci_call_64 ci_nested_1 ci_if_1 ci_ignored_1 ci_nested_32 ci_if_32 ci_ignored_32 ci_nested_64 ci_if_64 ci_ignored_64 ci_nested_80 ci_if_80 ci_ignored_80 ci_ignored_install \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_inst_props_probeScript.sml ssa_cc_trans_inst_props_probe.out \
  sip_full sip_type_i sip_type_ssa sip_type_na sip_type_iOut sip_type_ssaOut sip_type_naOut \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe word_to_stack_no_install_programs_probeScript.sml word_to_stack_no_install_programs_probe.out \
  ip_full ip_conf_type ip_perf_type ip_register_type ip_source_type ip_bitmap_type ip_outputs_type ip_frames_type ip_residual_type ip_empty_1 ip_safe_1 ip_ignored_1 ip_shared_1 ip_empty_32 ip_safe_32 ip_ignored_32 ip_shared_32 ip_empty_64 ip_safe_64 ip_ignored_64 ip_shared_64 ip_empty_80 ip_safe_80 ip_ignored_80 ip_shared_80 \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_rename_shifted_properties_probeScript.sml ssa_rename_shifted_properties_probe.out \
  srl_full srl_type_ls srl_type_ssa srl_type_na srl_type_lsOut srl_type_ssaOut srl_type_naOut \
  srm_full srm_type_ls srm_type_ssa srm_type_na srm_type_lsOut srm_type_ssaOut srm_type_naOut \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_props_move_probeScript.sml ssa_cc_trans_props_move_probe.out \
  spm_full spm_type_pri spm_type_ls spm_type_ssa spm_type_na spm_type_lt spm_type_progOut spm_type_ssaOut spm_type_naOut \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe word_props_no_install_code_probeScript.sml word_props_no_install_code_probe.out \
  nic_def nic_code_type nic_program_type nic_argument_type nic_empty_1 nic_leaf_zero_1 nic_leaf_missing_1 nic_bad_leaf_1 nic_malformed_empty_1 nic_malformed_value_1 nic_nested_left_1 nic_nested_right_1 nic_empty_80 nic_leaf_zero_80 nic_leaf_missing_80 nic_bad_leaf_80 nic_malformed_empty_80 nic_malformed_value_80 nic_nested_left_80 nic_nested_right_80 \
  "$cake_dir/compiler/backend/semantics/wordPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_no_install_top_probeScript.sml word_to_stack_no_install_top_probe.out \
  nt_full nt_conf_type nt_source_type nt_bitmaps_type nt_config_type nt_frames_type nt_outputs_type nt_empty_1 nt_safe_1 nt_shadow_1 nt_bad_1 nt_empty_32 nt_safe_32 nt_shadow_32 nt_bad_32 nt_empty_64 nt_safe_64 nt_shadow_64 nt_bad_64 nt_empty_80 nt_safe_80 nt_shadow_80 nt_bad_80 nt_code_empty nt_code_safe nt_code_shadow \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_props_allocation_probeScript.sml ssa_cc_trans_props_allocation_probe.out \
  spa_alloc_full spa_alloc_type_num spa_alloc_type_numset spa_alloc_type_ssa spa_alloc_type_na spa_alloc_type_lt spa_alloc_type_progOut spa_alloc_type_ssaOut spa_alloc_type_naOut \
  spa_install_full spa_install_type_ptr spa_install_type_len spa_install_type_dptr spa_install_type_dlen spa_install_type_numset spa_install_type_ssa spa_install_type_na spa_install_type_lt \
  spa_install_type_progOut spa_install_type_ssaOut spa_install_type_naOut spa_ffi_full spa_ffi_type_ffi_index spa_ffi_type_ptr1 spa_ffi_type_len1 spa_ffi_type_ptr2 spa_ffi_type_len2 \
  spa_ffi_type_numset spa_ffi_type_ssa spa_ffi_type_na spa_ffi_type_lt spa_ffi_type_progOut spa_ffi_type_ssaOut spa_ffi_type_naOut \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"
run_probe ssa_force_rename_generic_probeScript.sml ssa_force_rename_generic_probe.out \
  fr_definition fr_lookup_force_rename_aux fr_lookup_force_rename fr_domain_force_rename fr_type \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe binary_ieee_real_carrier_source_probeScript.sml binary_ieee_real_carrier_source_probe.out \
  float_to_real_def_statement float_to_real_def_types float_value_def_statement float_value_def_types is_closest_def_statement is_closest_def_types closest_such_def_statement closest_such_def_types closest_def_statement closest_def_types largest_def_statement largest_def_types threshold_def_statement threshold_def_types round_def_statement round_def_types float_round_def_statement float_round_def_types float_round_with_flags_def_statement float_round_with_flags_def_types float_sqrt_def_statement float_sqrt_def_types fp64_sqrt_def_statement fp64_sqrt_def_types fp64_to_float_def_statement fp64_to_float_def_types float_to_fp64_def_statement float_to_fp64_def_types \
  "$hol_dir/src/floating-point/binary_ieeeScript.sml" "$hol_dir/src/floating-point"
run_probe ssa_cc_trans_props_loop_control_probeScript.sml ssa_cc_trans_props_loop_control_probe.out \
  spl_full spl_type_names spl_type_body spl_type_exit_names spl_type_ssa spl_type_na spl_type_lt spl_type_progOut \
  spl_type_ssaOut spl_type_naOut spl_type_setup_prog spl_type_ssa_refreshed spl_type_na_refreshed spl_type_ssa_names spl_type_ssa_exit spl_type_ssa_body \
  spb_full spb_type_n spb_type_ssa spb_type_na spb_type_lt spb_type_progOut spb_type_ssaOut spb_type_naOut \
  spc_full spc_type_n spc_type_ssa spc_type_na spc_type_lt spc_type_progOut spc_type_ssaOut spc_type_naOut \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_props_calls_probeScript.sml ssa_cc_trans_props_calls_probe.out \
  spt_full spt_type_dest spt_type_args spt_type_h spt_type_ssa spt_type_na spt_type_lt spt_type_progPrime spt_type_ssaPrime spt_type_naPrime spr_full spr_type_ret spr_type_numset spr_type_ret_handler spr_type_l1 spr_type_l2 spr_type_dest spr_type_args spr_type_h spr_type_ssa spr_type_na spr_type_lt spr_type_progPrime spr_type_ssaPrime spr_type_naPrime spr_type_all_names spr_type_ls spr_type_stack_mov spr_type_stack_set spr_type_names spr_type_conv_args spr_type_move_args spr_type_ssa_cut spr_type_ret_mov spr_type_ssaPrimePrime spr_type_naPrimePrime spr_type_retPrime spr_type_ssa_2_p spr_type_na_2_p spr_type_ren_ret_handler spr_type_ssa_2 spr_type_na_2 spr_type_regs spr_type_mov_ret_handler spr_type_v spr_type_n spr_type_v2 spr_type_hPrime spr_type_v4 spr_type_l1PrimePrime spr_type_l2Prime spr_type_nPrime spr_type_ssa_3_p spr_type_na_3_p \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_cse_instruction_keys_probeScript.sml word_cse_instruction_keys_probe.out \
  key_def_wordToNum key_def_shiftToNum key_def_arithOpToNum key_def_regImmToNumList key_def_arithToNumList key_def_memOpToNum key_def_loadToNumList key_def_fpToNumList key_def_instToNumList key_def_OpCurrHeapToNumList key_shift_lsl key_shift_lsr key_shift_asr key_shift_ror key_op_add key_heap_add key_op_sub key_heap_sub key_op_and key_heap_and key_op_or key_heap_or key_op_xor key_heap_xor key_mem_load key_load_load key_mem_load8 key_load_load8 key_mem_load16 key_load_load16 key_mem_load32 key_load_load32 key_mem_store key_load_store key_mem_store8 key_load_store8 key_mem_store16 key_load_store16 key_mem_store32 key_load_store32 key_word_1 key_imm_1 key_const_1 key_word_32 key_imm_32 key_const_32 key_word_64 key_imm_64 key_const_64 key_word_80 key_imm_80 key_const_80 key_reg key_arith_0 key_inst_arith_0 key_arith_1 key_inst_arith_1 key_arith_2 key_inst_arith_2 key_arith_3 key_inst_arith_3 key_arith_4 key_inst_arith_4 key_arith_5 key_inst_arith_5 key_arith_6 key_inst_arith_6 key_arith_7 key_inst_arith_7 key_fp_fpLess key_inst_fpLess key_fp_fpLessEqual key_inst_fpLessEqual key_fp_fpEqual key_inst_fpEqual key_fp_fpAbs key_inst_fpAbs key_fp_fpNeg key_inst_fpNeg key_fp_fpSqrt key_inst_fpSqrt key_fp_fpAdd key_inst_fpAdd key_fp_fpSub key_inst_fpSub key_fp_fpMul key_inst_fpMul key_fp_fpDiv key_inst_fpDiv key_fp_fpFma key_inst_fpFma key_fp_fpMov key_inst_fpMov key_fp_fpMovToReg key_inst_fpMovToReg key_fp_fpMovFromReg key_inst_fpMovFromReg key_fp_fpToInt key_inst_fpToInt key_fp_fpFromInt key_inst_fpFromInt key_skip key_mem_inst \
  key_type_wordToNum key_type_shiftToNum key_type_arithOpToNum key_type_regImmToNumList key_type_arithToNumList key_type_memOpToNum key_type_loadToNumList key_type_fpToNumList key_type_instToNumList key_type_OpCurrHeapToNumList \
  "$cake_dir/compiler/backend/word_cseScript.sml" "$cake_dir/compiler/backend"

run_probe word_cse_register_keys_probeScript.sml word_cse_register_keys_probe.out \
  rk_statement_firstRegOfArith rk_statement_arithWrites rk_statement_arithReads rk_statement_fpWrites rk_statement_can_mem_arith rk_statement_is_store rk_statement_wordToNum_unique rk_statement_arithOpToNum_eq rk_statement_memOpToNum_eq rk_statement_shiftToNum_eq rk_type_firstRegOfArith rk_type_arithWrites rk_type_arithReads rk_type_fpWrites rk_type_can_mem_arith rk_type_is_store rk_a0_firstRegOfArith_8 rk_a0_arithWrites_8 rk_a0_arithReads_8 rk_a0_can_mem_arith_8 rk_a1_firstRegOfArith_8 rk_a1_arithWrites_8 rk_a1_arithReads_8 rk_a1_can_mem_arith_8 rk_a2_firstRegOfArith_8 rk_a2_arithWrites_8 rk_a2_arithReads_8 rk_a2_can_mem_arith_8 rk_a3_firstRegOfArith_8 rk_a3_arithWrites_8 rk_a3_arithReads_8 rk_a3_can_mem_arith_8 rk_a4_firstRegOfArith_8 rk_a4_arithWrites_8 rk_a4_arithReads_8 rk_a4_can_mem_arith_8 rk_a5_firstRegOfArith_8 rk_a5_arithWrites_8 rk_a5_arithReads_8 rk_a5_can_mem_arith_8 rk_a6_firstRegOfArith_8 rk_a6_arithWrites_8 rk_a6_arithReads_8 rk_a6_can_mem_arith_8 rk_a7_firstRegOfArith_8 rk_a7_arithWrites_8 rk_a7_arithReads_8 rk_a7_can_mem_arith_8 rk_a8_firstRegOfArith_8 rk_a8_arithWrites_8 rk_a8_arithReads_8 rk_a8_can_mem_arith_8 rk_a9_firstRegOfArith_8 rk_a9_arithWrites_8 rk_a9_arithReads_8 rk_a9_can_mem_arith_8 rk_a0_firstRegOfArith_80 rk_a0_arithWrites_80 rk_a0_arithReads_80 rk_a0_can_mem_arith_80 rk_a1_firstRegOfArith_80 rk_a1_arithWrites_80 rk_a1_arithReads_80 rk_a1_can_mem_arith_80 rk_a2_firstRegOfArith_80 rk_a2_arithWrites_80 rk_a2_arithReads_80 rk_a2_can_mem_arith_80 rk_a3_firstRegOfArith_80 rk_a3_arithWrites_80 rk_a3_arithReads_80 rk_a3_can_mem_arith_80 rk_a4_firstRegOfArith_80 rk_a4_arithWrites_80 rk_a4_arithReads_80 rk_a4_can_mem_arith_80 rk_a5_firstRegOfArith_80 rk_a5_arithWrites_80 rk_a5_arithReads_80 rk_a5_can_mem_arith_80 rk_a6_firstRegOfArith_80 rk_a6_arithWrites_80 rk_a6_arithReads_80 rk_a6_can_mem_arith_80 rk_a7_firstRegOfArith_80 rk_a7_arithWrites_80 rk_a7_arithReads_80 rk_a7_can_mem_arith_80 rk_a8_firstRegOfArith_80 rk_a8_arithWrites_80 rk_a8_arithReads_80 rk_a8_can_mem_arith_80 rk_a9_firstRegOfArith_80 rk_a9_arithWrites_80 rk_a9_arithReads_80 rk_a9_can_mem_arith_80 rk_fp_fpLess rk_fp_fpLessEqual rk_fp_fpEqual rk_fp_fpAbs rk_fp_fpNeg rk_fp_fpSqrt rk_fp_fpAdd rk_fp_fpSub rk_fp_fpMul rk_fp_fpDiv rk_fp_fpFma rk_fp_fpMov rk_fp_fpMovToReg rk_fp_fpMovFromReg rk_fp_fpToInt rk_fp_fpFromInt rk_store_load rk_store_load8 rk_store_load16 rk_store_load32 rk_store_store rk_store_store8 rk_store_store16 rk_store_store32 rk_replay_wordToNum_unique rk_replay_arithOpToNum_eq rk_replay_memOpToNum_eq rk_replay_shiftToNum_eq \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_cse_insert_equality_probeScript.sml word_cse_insert_equality_probe.out \
  ie_full ie_replay ie_0_7 ie_0_8 ie_1_7 ie_1_8 ie_2_7 ie_2_8 ie_3_7 ie_3_8 ie_4_7 ie_4_8 ie_binder_types \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_cse_arithmetic_keys_probeScript.sml word_cse_arithmetic_keys_probe.out \
  ak_full ak_replay ak_arith_type ak_state_type ak_value_type ak_0_1 ak_1_1 ak_2_1 ak_3_1 ak_4_1 ak_5_1 ak_6_1 ak_7_1 ak_8_1 ak_9_1 ak_10_1 ak_11_1 ak_12_1 ak_13_1 ak_14_1 ak_0_32 ak_1_32 ak_2_32 ak_3_32 ak_4_32 ak_5_32 ak_6_32 ak_7_32 ak_8_32 ak_9_32 ak_10_32 ak_11_32 ak_12_32 ak_13_32 ak_14_32 ak_0_64 ak_1_64 ak_2_64 ak_3_64 ak_4_64 ak_5_64 ak_6_64 ak_7_64 ak_8_64 ak_9_64 ak_10_64 ak_11_64 ak_12_64 ak_13_64 ak_14_64 ak_0_80 ak_1_80 ak_2_80 ak_3_80 ak_4_80 ak_5_80 ak_6_80 ak_7_80 ak_8_80 ak_9_80 ak_10_80 ak_11_80 ak_12_80 ak_13_80 ak_14_80 \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe stack_to_lab_executed_input_probeScript.sml stack_to_lab_executed_input_probe.out \
  guard_source_get_drop guard_source_alloc_drop guard_source_stackstore_drop guard_source_datawrite_drop guard_source_skip_section guard_source_seq_section guard_source_loc_section \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" "$cake_dir/compiler/backend"

run_probe lab_implicit_section_zero_probeScript.sml lab_implicit_section_zero_probe.out \
  zero_original_skip_late_zero zero_original_section_base zero_original_second_base zero_original_second_label zero_original_empty_section zero_original_crosssection_bytes \
  "$cake_dir/compiler/backend/lab_to_targetScript.sml" "$cake_dir/compiler/encoders/riscv"

run_probe stackprops_shared_memory_clock_probeScript.sml stackprops_shared_memory_clock_probe.out \
  sh_mem_load_with_const sh_mem_load_with_const_types sh_mem_store_with_const sh_mem_store_with_const_types sh_mem_load32_with_const sh_mem_load32_with_const_types sh_mem_store32_with_const sh_mem_store32_with_const_types sh_mem_load16_with_const sh_mem_load16_with_const_types sh_mem_store16_with_const sh_mem_store16_with_const_types sh_mem_load_byte_with_const sh_mem_load_byte_with_const_types sh_mem_store_byte_with_const sh_mem_store_byte_with_const_types sh_mem_op_with_const sh_mem_op_with_const_types sh_mem_op_const sh_mem_op_const_types store load store8 load8 store16 load16 store32 load32 load_outside store8_outside load_word_unaligned store_word_unaligned load_final store_final store_loc store_frame load_frame store8_frame load8_frame store16_frame load16_frame store32_frame load32_frame load_outside_frame store8_outside_frame load_word_unaligned_frame store_word_unaligned_frame load_final_frame store_final_frame store_loc_frame \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe ssa_cc_trans_props_primitives_probeScript.sml ssa_cc_trans_props_primitives_probe.out \
  spp_case_0 spp_case_2 spp_case_3 spp_case_4 spp_case_5 spp_case_6 spp_case_11 spp_case_12 spp_case_13 spp_case_14 spp_case_15 spp_case_16 spp_case_18 spp_case_19 spp_case_23 spp_0_type_ssa spp_0_type_na spp_0_type_lt spp_0_type_progOut spp_0_type_ssaOut spp_0_type_naOut spp_2_type_a spp_2_type_b spp_2_type_c spp_2_type_d spp_2_type_ws spp_3_type_i spp_4_type_num spp_4_type_exp spp_5_type_num spp_5_type_store spp_6_type_exp spp_6_type_num spp_11_type_num spp_12_type_b spp_12_type_dst spp_12_type_src spp_13_type_num spp_13_type_nums spp_15_type_n spp_15_type_exp spp_16_type_r spp_16_type_l1 spp_18_type_r1 spp_18_type_r2 spp_19_type_r1 spp_19_type_r2 spp_23_type_op spp_23_type_v spp_23_type_exp \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_props_control_probeScript.sml ssa_cc_trans_props_control_probe.out \
  spc_case_7 spc_case_8 spc_case_9 spc_7_type_s1 spc_7_type_s2 spc_7_type_ssa spc_7_type_na spc_7_type_lt spc_7_type_progOut spc_7_type_ssaOut spc_7_type_naOut spc_8_type_s1 spc_9_type_cmp spc_9_type_r1 spc_9_type_ri spc_9_type_e2 spc_9_type_e3 spc_9_type_r1P spc_9_type_riP spc_9_type_e2P spc_9_type_ssa2 spc_9_type_na2 \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_props_probeScript.sml ssa_cc_trans_props_probe.out \
  ssa_props_full ssa_props_type_prog ssa_props_type_ssa ssa_props_type_na ssa_props_type_lt ssa_props_type_progOut ssa_props_type_ssaOut ssa_props_type_naOut \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe target_sem_evaluate_probeScript.sml target_sem_evaluate_probe.out \
  te_zero te_unknown te_halt_success te_halt_resource te_cache te_shared_missing te_external_mmio te_cache_shift te_empty_external te_empty_external_shift te_normal_priority_encoding_fail te_normal_success te_normal_shift te_normal_guard_rollback te_mm_read_return te_mm_write_return te_mm_write_narrow te_mm_read_final te_mm_unshared te_mm_invalid_size \
  "$cake_dir/compiler/backend/semantics/targetSemScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe word_cse_load_evaluation_probeScript.sml word_cse_load_evaluation_probe.out \
  ld_full_any ld_full_write ld_full_addr ld_type_state ld_type_word ld_type_value ld_type_op ld_any_load_98_1 ld_any_load_3_1 ld_write_load_99_1 ld_write_load_77_1 ld_addr_load_1 ld_any_load8_98_1 ld_any_load8_3_1 ld_write_load8_99_1 ld_write_load8_77_1 ld_addr_load8_1 ld_any_load16_98_1 ld_any_load16_3_1 ld_write_load16_99_1 ld_write_load16_77_1 ld_addr_load16_1 ld_any_load32_98_1 ld_any_load32_3_1 ld_write_load32_99_1 ld_write_load32_77_1 ld_addr_load32_1 ld_any_load_98_32 ld_any_load_3_32 ld_write_load_99_32 ld_write_load_77_32 ld_addr_load_32 ld_any_load8_98_32 ld_any_load8_3_32 ld_write_load8_99_32 ld_write_load8_77_32 ld_addr_load8_32 ld_any_load16_98_32 ld_any_load16_3_32 ld_write_load16_99_32 ld_write_load16_77_32 ld_addr_load16_32 ld_any_load32_98_32 ld_any_load32_3_32 ld_write_load32_99_32 ld_write_load32_77_32 ld_addr_load32_32 ld_any_load_98_64 ld_any_load_3_64 ld_write_load_99_64 ld_write_load_77_64 ld_addr_load_64 ld_any_load8_98_64 ld_any_load8_3_64 ld_write_load8_99_64 ld_write_load8_77_64 ld_addr_load8_64 ld_any_load16_98_64 ld_any_load16_3_64 ld_write_load16_99_64 ld_write_load16_77_64 ld_addr_load16_64 ld_any_load32_98_64 ld_any_load32_3_64 ld_write_load32_99_64 ld_write_load32_77_64 ld_addr_load32_64 ld_any_load_98_80 ld_any_load_3_80 ld_write_load_99_80 ld_write_load_77_80 ld_addr_load_80 ld_any_load8_98_80 ld_any_load8_3_80 ld_write_load8_99_80 ld_write_load8_77_80 ld_addr_load8_80 ld_any_load16_98_80 ld_any_load16_3_80 ld_write_load16_99_80 ld_write_load16_77_80 ld_addr_load16_80 ld_any_load32_98_80 ld_any_load32_3_80 ld_write_load32_99_80 ld_write_load32_77_80 ld_addr_load32_80 \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe target_sem_machine_sem_probeScript.sml target_sem_machine_sem_probe.out \
  ts_terminate_clause ts_diverge_clause ts_fail_clause \
  "$cake_dir/compiler/backend/semantics/targetSemScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe ssa_reconcile_list_props_probeScript.sml ssa_reconcile_list_props_probe.out \
  sr_moves_full sr_filtered_full sr_type_L sr_type_m sr_type_f sr_type_cur_ssa sr_type_tgt_ssa sr_type_ns \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe riscv_jumpcmp_polarity_probeScript.sml riscv_jumpcmp_polarity_probe.out \
  branch_equal_reg_short branch_equal_reg_long branch_equal_imm_short branch_equal_imm_long branch_notequal_reg_short branch_notequal_reg_long branch_notequal_imm_short branch_notequal_imm_long branch_less_reg_short branch_less_reg_long branch_less_imm_short branch_less_imm_long branch_notless_reg_short branch_notless_reg_long branch_notless_imm_short branch_notless_imm_long branch_lower_reg_short branch_lower_reg_long branch_lower_imm_short branch_lower_imm_long branch_notlower_reg_short branch_notlower_reg_long branch_notlower_imm_short branch_notlower_imm_long branch_test_reg_short branch_test_reg_long branch_test_imm_short branch_test_imm_long branch_nottest_reg_short branch_nottest_reg_long branch_nottest_imm_short branch_nottest_imm_long \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"

run_probe stackprops_stack_lengths_probeScript.sml stackprops_stack_lengths_probe.out \
  map_bitmap_length map_bitmap_length_types dec_stack_length dec_stack_length_types map_empty map_mixed map_false map_payload_lists map_missing_root map_missing_value dec_empty dec_zero dec_true dec_false dec_short_roots dec_extra_roots dec_two dec_zero_extra dec_mixed dec_narrow_bitmap dec_loc_header dec_missing_sentinel \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe ssa_reconcile_alookup_zip_probeScript.sml ssa_reconcile_alookup_zip_probe.out \
  sz_some_full sz_none_full sz_alookup_zip_map_some_type_ls sz_alookup_zip_map_some_type_vs sz_alookup_zip_map_some_type_i sz_alookup_zip_map_some_type_f sz_alookup_zip_map_option_lookup_none_type_f sz_alookup_zip_map_option_lookup_none_type_ns sz_alookup_zip_map_option_lookup_none_type_n sz_alookup_zip_map_option_lookup_none_type_ls sz_alookup_zip_map_option_lookup_none_type_vs \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe word_cse_evaluation_frames_probeScript.sml word_cse_evaluation_frames_probe.out \
  fr_full_write fr_full_memory fr_full_arith_agree fr_full_load_agree fr_type_arith fr_type_state fr_type_value fr_type_memory fr_write_0_99_1 fr_write_0_77_1 fr_memory_0_1 fr_arith_agree_0_1 fr_write_1_99_1 fr_write_1_77_1 fr_memory_1_1 fr_arith_agree_1_1 fr_write_2_99_1 fr_write_2_77_1 fr_memory_2_1 fr_arith_agree_2_1 fr_write_3_99_1 fr_write_3_77_1 fr_memory_3_1 fr_arith_agree_3_1 fr_write_4_99_1 fr_write_4_77_1 fr_memory_4_1 fr_arith_agree_4_1 fr_write_5_99_1 fr_write_5_77_1 fr_memory_5_1 fr_arith_agree_5_1 fr_write_6_99_1 fr_write_6_77_1 fr_memory_6_1 fr_arith_agree_6_1 fr_write_7_99_1 fr_write_7_77_1 fr_memory_7_1 fr_arith_agree_7_1 fr_write_8_99_1 fr_write_8_77_1 fr_memory_8_1 fr_arith_agree_8_1 fr_write_9_99_1 fr_write_9_77_1 fr_memory_9_1 fr_arith_agree_9_1 fr_write_10_99_1 fr_write_10_77_1 fr_memory_10_1 fr_arith_agree_10_1 fr_write_11_99_1 fr_write_11_77_1 fr_memory_11_1 fr_arith_agree_11_1 fr_write_12_99_1 fr_write_12_77_1 fr_memory_12_1 fr_arith_agree_12_1 fr_write_13_99_1 fr_write_13_77_1 fr_memory_13_1 fr_arith_agree_13_1 fr_write_14_99_1 fr_write_14_77_1 fr_memory_14_1 fr_arith_agree_14_1 fr_load_agree_load_1 fr_load_agree_load8_1 fr_load_agree_load16_1 fr_load_agree_load32_1 fr_write_0_99_32 fr_write_0_77_32 fr_memory_0_32 fr_arith_agree_0_32 fr_write_1_99_32 fr_write_1_77_32 fr_memory_1_32 fr_arith_agree_1_32 fr_write_2_99_32 fr_write_2_77_32 fr_memory_2_32 fr_arith_agree_2_32 fr_write_3_99_32 fr_write_3_77_32 fr_memory_3_32 fr_arith_agree_3_32 fr_write_4_99_32 fr_write_4_77_32 fr_memory_4_32 fr_arith_agree_4_32 fr_write_5_99_32 fr_write_5_77_32 fr_memory_5_32 fr_arith_agree_5_32 fr_write_6_99_32 fr_write_6_77_32 fr_memory_6_32 fr_arith_agree_6_32 fr_write_7_99_32 fr_write_7_77_32 fr_memory_7_32 fr_arith_agree_7_32 fr_write_8_99_32 fr_write_8_77_32 fr_memory_8_32 fr_arith_agree_8_32 fr_write_9_99_32 fr_write_9_77_32 fr_memory_9_32 fr_arith_agree_9_32 fr_write_10_99_32 fr_write_10_77_32 fr_memory_10_32 fr_arith_agree_10_32 fr_write_11_99_32 fr_write_11_77_32 fr_memory_11_32 fr_arith_agree_11_32 fr_write_12_99_32 fr_write_12_77_32 fr_memory_12_32 fr_arith_agree_12_32 fr_write_13_99_32 fr_write_13_77_32 fr_memory_13_32 fr_arith_agree_13_32 fr_write_14_99_32 fr_write_14_77_32 fr_memory_14_32 fr_arith_agree_14_32 fr_load_agree_load_32 fr_load_agree_load8_32 fr_load_agree_load16_32 fr_load_agree_load32_32 fr_write_0_99_64 fr_write_0_77_64 fr_memory_0_64 fr_arith_agree_0_64 fr_write_1_99_64 fr_write_1_77_64 fr_memory_1_64 fr_arith_agree_1_64 fr_write_2_99_64 fr_write_2_77_64 fr_memory_2_64 fr_arith_agree_2_64 fr_write_3_99_64 fr_write_3_77_64 fr_memory_3_64 fr_arith_agree_3_64 fr_write_4_99_64 fr_write_4_77_64 fr_memory_4_64 fr_arith_agree_4_64 fr_write_5_99_64 fr_write_5_77_64 fr_memory_5_64 fr_arith_agree_5_64 fr_write_6_99_64 fr_write_6_77_64 fr_memory_6_64 fr_arith_agree_6_64 fr_write_7_99_64 fr_write_7_77_64 fr_memory_7_64 fr_arith_agree_7_64 fr_write_8_99_64 fr_write_8_77_64 fr_memory_8_64 fr_arith_agree_8_64 fr_write_9_99_64 fr_write_9_77_64 fr_memory_9_64 fr_arith_agree_9_64 fr_write_10_99_64 fr_write_10_77_64 fr_memory_10_64 fr_arith_agree_10_64 fr_write_11_99_64 fr_write_11_77_64 fr_memory_11_64 fr_arith_agree_11_64 fr_write_12_99_64 fr_write_12_77_64 fr_memory_12_64 fr_arith_agree_12_64 fr_write_13_99_64 fr_write_13_77_64 fr_memory_13_64 fr_arith_agree_13_64 fr_write_14_99_64 fr_write_14_77_64 fr_memory_14_64 fr_arith_agree_14_64 fr_load_agree_load_64 fr_load_agree_load8_64 fr_load_agree_load16_64 fr_load_agree_load32_64 fr_write_0_99_80 fr_write_0_77_80 fr_memory_0_80 fr_arith_agree_0_80 fr_write_1_99_80 fr_write_1_77_80 fr_memory_1_80 fr_arith_agree_1_80 fr_write_2_99_80 fr_write_2_77_80 fr_memory_2_80 fr_arith_agree_2_80 fr_write_3_99_80 fr_write_3_77_80 fr_memory_3_80 fr_arith_agree_3_80 fr_write_4_99_80 fr_write_4_77_80 fr_memory_4_80 fr_arith_agree_4_80 fr_write_5_99_80 fr_write_5_77_80 fr_memory_5_80 fr_arith_agree_5_80 fr_write_6_99_80 fr_write_6_77_80 fr_memory_6_80 fr_arith_agree_6_80 fr_write_7_99_80 fr_write_7_77_80 fr_memory_7_80 fr_arith_agree_7_80 fr_write_8_99_80 fr_write_8_77_80 fr_memory_8_80 fr_arith_agree_8_80 fr_write_9_99_80 fr_write_9_77_80 fr_memory_9_80 fr_arith_agree_9_80 fr_write_10_99_80 fr_write_10_77_80 fr_memory_10_80 fr_arith_agree_10_80 fr_write_11_99_80 fr_write_11_77_80 fr_memory_11_80 fr_arith_agree_11_80 fr_write_12_99_80 fr_write_12_77_80 fr_memory_12_80 fr_arith_agree_12_80 fr_write_13_99_80 fr_write_13_77_80 fr_memory_13_80 fr_arith_agree_13_80 fr_write_14_99_80 fr_write_14_77_80 fr_memory_14_80 fr_arith_agree_14_80 fr_load_agree_load_80 fr_load_agree_load8_80 fr_load_agree_load16_80 fr_load_agree_load32_80 \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe ssa_reconcile_get_vars_probeScript.sml ssa_reconcile_get_vars_probe.out \
  ssa_reconcile_get_vars_original_proof ssa_reconcile_get_vars_original_type \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe stackprops_ordered_code_labels_probeScript.sml stackprops_ordered_code_labels_probe.out \
  extract_labels extract_labels_types find_code_labels find_code_labels_types find_code find_code_types get_labels get_labels_types loc_check loc_check_types key_bool_direct key_bool_indirect key_bool_missing key_bool_nonzero key_bool_word key_list_indirect key_list_missing_code key_nat_legacy ordered_skip ordered_ignore_handler ordered_return ordered_both ordered_nested ordered_duplicate ordered_sequence ordered_loop ordered_if ordered_leaf_labels containment_bool_direct containment_list_indirect \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe target_props_clock_probeScript.sml target_props_clock_probe.out \
  tp_clock_theorem_closed tp_clock_type tp_clock_statement tp_halt_stable tp_error_stable \
  "$cake_dir/compiler/backend/semantics/targetPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe ssa_reconcile_empty_probeScript.sml ssa_reconcile_empty_probe.out \
  re_original_full re_empty_full re_type_na re_type_cur_ssa re_type_tgt_ssa re_type_st_locs re_type_cst re_type_ns \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe word_cse_deletion_frames_probeScript.sml word_cse_deletion_frames_probe.out \
  del_full_arith del_full_load del_type_arith del_type_state del_type_value del_type_memory del_arith_0_99_1 del_arith_0_77_1 del_arith_1_99_1 del_arith_1_77_1 del_arith_2_99_1 del_arith_2_77_1 del_arith_3_99_1 del_arith_3_77_1 del_arith_4_99_1 del_arith_4_77_1 del_arith_5_99_1 del_arith_5_77_1 del_arith_6_99_1 del_arith_6_77_1 del_arith_7_99_1 del_arith_7_77_1 del_arith_8_99_1 del_arith_8_77_1 del_arith_9_99_1 del_arith_9_77_1 del_arith_10_99_1 del_arith_10_77_1 del_arith_11_99_1 del_arith_11_77_1 del_arith_12_99_1 del_arith_12_77_1 del_arith_13_99_1 del_arith_13_77_1 del_arith_14_99_1 del_arith_14_77_1 del_arith_0_99_32 del_arith_0_77_32 del_arith_1_99_32 del_arith_1_77_32 del_arith_2_99_32 del_arith_2_77_32 del_arith_3_99_32 del_arith_3_77_32 del_arith_4_99_32 del_arith_4_77_32 del_arith_5_99_32 del_arith_5_77_32 del_arith_6_99_32 del_arith_6_77_32 del_arith_7_99_32 del_arith_7_77_32 del_arith_8_99_32 del_arith_8_77_32 del_arith_9_99_32 del_arith_9_77_32 del_arith_10_99_32 del_arith_10_77_32 del_arith_11_99_32 del_arith_11_77_32 del_arith_12_99_32 del_arith_12_77_32 del_arith_13_99_32 del_arith_13_77_32 del_arith_14_99_32 del_arith_14_77_32 del_arith_0_99_64 del_arith_0_77_64 del_arith_1_99_64 del_arith_1_77_64 del_arith_2_99_64 del_arith_2_77_64 del_arith_3_99_64 del_arith_3_77_64 del_arith_4_99_64 del_arith_4_77_64 del_arith_5_99_64 del_arith_5_77_64 del_arith_6_99_64 del_arith_6_77_64 del_arith_7_99_64 del_arith_7_77_64 del_arith_8_99_64 del_arith_8_77_64 del_arith_9_99_64 del_arith_9_77_64 del_arith_10_99_64 del_arith_10_77_64 del_arith_11_99_64 del_arith_11_77_64 del_arith_12_99_64 del_arith_12_77_64 del_arith_13_99_64 del_arith_13_77_64 del_arith_14_99_64 del_arith_14_77_64 del_arith_0_99_80 del_arith_0_77_80 del_arith_1_99_80 del_arith_1_77_80 del_arith_2_99_80 del_arith_2_77_80 del_arith_3_99_80 del_arith_3_77_80 del_arith_4_99_80 del_arith_4_77_80 del_arith_5_99_80 del_arith_5_77_80 del_arith_6_99_80 del_arith_6_77_80 del_arith_7_99_80 del_arith_7_77_80 del_arith_8_99_80 del_arith_8_77_80 del_arith_9_99_80 del_arith_9_77_80 del_arith_10_99_80 del_arith_10_77_80 del_arith_11_99_80 del_arith_11_77_80 del_arith_12_99_80 del_arith_12_77_80 del_arith_13_99_80 del_arith_13_77_80 del_arith_14_99_80 del_arith_14_77_80 del_load_load_99_1 del_load_load_77_1 del_load_load8_99_1 del_load_load8_77_1 del_load_load16_99_1 del_load_load16_77_1 del_load_load32_99_1 del_load_load32_77_1 del_load_load_99_32 del_load_load_77_32 del_load_load8_99_32 del_load_load8_77_32 del_load_load16_99_32 del_load_load16_77_32 del_load_load32_99_32 del_load_load32_77_32 del_load_load_99_64 del_load_load_77_64 del_load_load8_99_64 del_load_load8_77_64 del_load_load16_99_64 del_load_load16_77_64 del_load_load32_99_64 del_load_load32_77_64 del_load_load_99_80 del_load_load_77_80 del_load_load8_99_80 del_load_load8_77_80 del_load_load16_99_80 del_load_load16_77_80 del_load_load32_99_80 del_load_load32_77_80 \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe stack_remove_stack_free_probeScript.sml stack_remove_stack_free_probe.out \
  single_stack_free_full_def stack_free_full_def single_stack_free_equation single_stack_free_type stack_free_type free_64_0 free_64_1 free_64_255 free_64_256 free_64_510 free_64_511 free_64_512 free_8_256 free_1_256 free_80_511 single_8_256 single_8_511 single_1_255 single_80_511 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"

run_probe stack_remove_stack_address_probeScript.sml stack_remove_stack_address_probe.out \
  upshift_full_def upshift_type downshift_full_def downshift_type stack_store_full_def stack_store_type stack_load_full_def stack_load_type upshift_64_0 downshift_64_0 stack_store_64_0 stack_load_64_0 upshift_64_1 downshift_64_1 stack_store_64_1 stack_load_64_1 upshift_64_255 downshift_64_255 stack_store_64_255 stack_load_64_255 upshift_64_256 downshift_64_256 stack_store_64_256 stack_load_64_256 upshift_64_510 downshift_64_510 stack_store_64_510 stack_load_64_510 upshift_64_511 downshift_64_511 stack_store_64_511 stack_load_64_511 upshift_64_512 downshift_64_512 stack_store_64_512 stack_load_64_512 upshift_8_256 downshift_8_256 stack_store_8_256 stack_load_8_256 upshift_1_256 downshift_1_256 stack_store_1_256 stack_load_1_256 upshift_80_511 downshift_80_511 stack_store_80_511 stack_load_80_511 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"

run_probe stack_remove_stack_alloc_probeScript.sml stack_remove_stack_alloc_probe.out \
  single_stack_alloc_full_def single_stack_alloc_type stack_alloc_full_def stack_alloc_type alloc_64_0_0 alloc_64_1_0 alloc_64_0_1 alloc_64_1_1 alloc_64_0_255 alloc_64_1_255 alloc_64_0_256 alloc_64_1_256 alloc_64_0_510 alloc_64_1_510 alloc_64_0_511 alloc_64_1_511 alloc_64_0_512 alloc_64_1_512 alloc_8_0_256 alloc_8_1_256 alloc_1_0_256 alloc_1_1_256 alloc_80_0_511 alloc_80_1_511 single_64_0_0 single_64_1_0 single_8_0_511 single_8_1_511 single_1_0_255 single_1_1_255 single_80_0_511 single_80_1_511 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"

run_probe stack_remove_store_address_probeScript.sml stack_remove_store_address_probe.out \
  store_pos_full_def store_pos_type store_offset_full_def store_offset_type position_0 position_1 position_2 position_3 position_4 position_5 position_6 position_7 position_8 position_9 position_10 position_11 position_12 position_13 position_14 position_15 position_16 position_17 position_18 position_19 position_20 position_21 position_22 position_23 position_24 position_25 position_26 position_27 position_28 position_29 position_30 position_31 position_32 position_33 position_34 position_35 position_36 position_37 position_38 position_39 position_40 position_41 position_42 position_43 position_44 position_45 position_46 position_47 position_48 offset_1_0 offset_1_10 offset_1_15 offset_1_16 offset_1_47 offset_1_48 offset_8_0 offset_8_10 offset_8_15 offset_8_16 offset_8_47 offset_8_48 offset_32_0 offset_32_10 offset_32_15 offset_32_16 offset_32_47 offset_32_48 offset_64_0 offset_64_10 offset_64_15 offset_64_16 offset_64_47 offset_64_48 offset_80_0 offset_80_10 offset_80_15 offset_80_16 offset_80_47 offset_80_48 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"

run_probe stacklang_inst_builders_probeScript.sml stacklang_inst_builders_probe.out \
  While_term While_type move_term move_type sub_inst_term sub_inst_type add_inst_term add_inst_type add_bytes_in_word_inst_term add_bytes_in_word_inst_type list_Seq_full_def list_Seq_type move_1 sub_inst_1 add_inst_1 bytes_1 while_1 seq_1_0 seq_1_1 seq_1_2 seq_1_3 move_8 sub_inst_8 add_inst_8 bytes_8 while_8 seq_8_0 seq_8_1 seq_8_2 seq_8_3 move_32 sub_inst_32 add_inst_32 bytes_32 while_32 seq_32_0 seq_32_1 seq_32_2 seq_32_3 move_64 sub_inst_64 add_inst_64 bytes_64 while_64 seq_64_0 seq_64_1 seq_64_2 seq_64_3 move_80 sub_inst_80 add_inst_80 bytes_80 while_80 seq_80_0 seq_80_1 seq_80_2 seq_80_3 \
  While_expanded move_expanded sub_inst_expanded add_inst_expanded add_bytes_in_word_inst_expanded \
  "$cake_dir/compiler/backend/stackLangScript.sml" "$cake_dir/compiler/backend"

run_probe stack_remove_copy_loop_probeScript.sml stack_remove_copy_loop_probe.out \
  copy_each_full_def copy_each_type copy_loop_full_def copy_loop_type copy_each_1_0_0 copy_loop_1_0_0 copy_each_1_5_6 copy_loop_1_5_6 copy_each_1_1234_1234 copy_loop_1_1234_1234 copy_each_8_0_0 copy_loop_8_0_0 copy_each_8_5_6 copy_loop_8_5_6 copy_each_8_1234_1234 copy_loop_8_1234_1234 copy_each_32_0_0 copy_loop_32_0_0 copy_each_32_5_6 copy_loop_32_5_6 copy_each_32_1234_1234 copy_loop_32_1234_1234 copy_each_64_0_0 copy_loop_64_0_0 copy_each_64_5_6 copy_loop_64_5_6 copy_each_64_1234_1234 copy_loop_64_1234_1234 copy_each_80_0_0 copy_loop_80_0_0 copy_each_80_5_6 copy_loop_80_5_6 copy_each_80_1234_1234 copy_loop_80_1234_1234 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"
run_probe ssa_lt_ok_probeScript.sml ssa_lt_ok_probe.out \
  lt_ok_full lt_ok_type_lt \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_correct_control_probeScript.sml ssa_cc_trans_correct_control_probe.out \
  sc_break_full sc_continue_full sc_type_n sc_type_st sc_type_cst sc_type_ssa sc_type_na sc_type_lt \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_correct_primitives_probeScript.sml ssa_cc_trans_correct_primitives_probe.out \
  sp_skip_full sp_tick_full sp_type_st sp_type_cst sp_type_ssa sp_type_na sp_type_lt \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_locals_get_var_probeScript.sml ssa_locals_get_var_probe.out \
  lg_full lg_type_st lg_type_cst lg_type_ssa lg_type_na lg_type_n lg_type_x \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe stackprops_allocation_constants_probeScript.sml stackprops_allocation_constants_probe.out \
  alloc_const alloc_const_types store_const_sem_const store_const_sem_const_types gc_with_const gc_with_const_types alloc_with_const alloc_with_const_types store_const_sem_with_const store_const_sem_with_const_types store_const_sem_def store_const_sem_def_types alloc_success_frame alloc_success_clock alloc_success_outcome alloc_halt_frame alloc_halt_clock alloc_halt_outcome alloc_gc_failure_frame alloc_gc_failure_clock alloc_gc_failure_outcome alloc_missing_frame alloc_missing_clock alloc_missing_outcome alloc_bad_amount_frame alloc_bad_amount_clock alloc_bad_amount_outcome alloc_bad_space_frame alloc_bad_space_clock alloc_bad_space_outcome store_duplicate_frame store_duplicate_clock store_duplicate_outcome store_nonword_frame store_nonword_clock store_nonword_outcome store_copy_failure_frame store_copy_failure_clock store_copy_failure_outcome store_success_alloc_frame store_success_alloc_clock store_success_alloc_outcome store_success_noalloc_frame store_success_noalloc_clock store_success_noalloc_outcome gc_success_clock gc_gc_failure_clock gc_missing_clock gc_bad_amount_clock mixed_state1_result80 mixed_state80_result1 \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe word_cse_list_order_probeScript.sml word_cse_list_order_probe.out \
  lo_definition lo_full_eq lo_full_reverse lo_full_transit lo_value_0_0 lo_eq_0_0 lo_reverse_0_0 lo_value_0_1 lo_eq_0_1 lo_reverse_0_1 lo_value_0_2 lo_eq_0_2 lo_reverse_0_2 lo_value_0_3 lo_eq_0_3 lo_reverse_0_3 lo_value_0_4 lo_eq_0_4 lo_reverse_0_4 lo_value_0_5 lo_eq_0_5 lo_reverse_0_5 lo_value_0_6 lo_eq_0_6 lo_reverse_0_6 lo_value_0_7 lo_eq_0_7 lo_reverse_0_7 lo_value_1_0 lo_eq_1_0 lo_reverse_1_0 lo_value_1_1 lo_eq_1_1 lo_reverse_1_1 lo_value_1_2 lo_eq_1_2 lo_reverse_1_2 lo_value_1_3 lo_eq_1_3 lo_reverse_1_3 lo_value_1_4 lo_eq_1_4 lo_reverse_1_4 lo_value_1_5 lo_eq_1_5 lo_reverse_1_5 lo_value_1_6 lo_eq_1_6 lo_reverse_1_6 lo_value_1_7 lo_eq_1_7 lo_reverse_1_7 lo_value_2_0 lo_eq_2_0 lo_reverse_2_0 lo_value_2_1 lo_eq_2_1 lo_reverse_2_1 lo_value_2_2 lo_eq_2_2 lo_reverse_2_2 lo_value_2_3 lo_eq_2_3 lo_reverse_2_3 lo_value_2_4 lo_eq_2_4 lo_reverse_2_4 lo_value_2_5 lo_eq_2_5 lo_reverse_2_5 lo_value_2_6 lo_eq_2_6 lo_reverse_2_6 lo_value_2_7 lo_eq_2_7 lo_reverse_2_7 lo_value_3_0 lo_eq_3_0 lo_reverse_3_0 lo_value_3_1 lo_eq_3_1 lo_reverse_3_1 lo_value_3_2 lo_eq_3_2 lo_reverse_3_2 lo_value_3_3 lo_eq_3_3 lo_reverse_3_3 lo_value_3_4 lo_eq_3_4 lo_reverse_3_4 lo_value_3_5 lo_eq_3_5 lo_reverse_3_5 lo_value_3_6 lo_eq_3_6 lo_reverse_3_6 lo_value_3_7 lo_eq_3_7 lo_reverse_3_7 lo_value_4_0 lo_eq_4_0 lo_reverse_4_0 lo_value_4_1 lo_eq_4_1 lo_reverse_4_1 lo_value_4_2 lo_eq_4_2 lo_reverse_4_2 lo_value_4_3 lo_eq_4_3 lo_reverse_4_3 lo_value_4_4 lo_eq_4_4 lo_reverse_4_4 lo_value_4_5 lo_eq_4_5 lo_reverse_4_5 lo_value_4_6 lo_eq_4_6 lo_reverse_4_6 lo_value_4_7 lo_eq_4_7 lo_reverse_4_7 lo_value_5_0 lo_eq_5_0 lo_reverse_5_0 lo_value_5_1 lo_eq_5_1 lo_reverse_5_1 lo_value_5_2 lo_eq_5_2 lo_reverse_5_2 lo_value_5_3 lo_eq_5_3 lo_reverse_5_3 lo_value_5_4 lo_eq_5_4 lo_reverse_5_4 lo_value_5_5 lo_eq_5_5 lo_reverse_5_5 lo_value_5_6 lo_eq_5_6 lo_reverse_5_6 lo_value_5_7 lo_eq_5_7 lo_reverse_5_7 lo_value_6_0 lo_eq_6_0 lo_reverse_6_0 lo_value_6_1 lo_eq_6_1 lo_reverse_6_1 lo_value_6_2 lo_eq_6_2 lo_reverse_6_2 lo_value_6_3 lo_eq_6_3 lo_reverse_6_3 lo_value_6_4 lo_eq_6_4 lo_reverse_6_4 lo_value_6_5 lo_eq_6_5 lo_reverse_6_5 lo_value_6_6 lo_eq_6_6 lo_reverse_6_6 lo_value_6_7 lo_eq_6_7 lo_reverse_6_7 lo_value_7_0 lo_eq_7_0 lo_reverse_7_0 lo_value_7_1 lo_eq_7_1 lo_reverse_7_1 lo_value_7_2 lo_eq_7_2 lo_reverse_7_2 lo_value_7_3 lo_eq_7_3 lo_reverse_7_3 lo_value_7_4 lo_eq_7_4 lo_reverse_7_4 lo_value_7_5 lo_eq_7_5 lo_reverse_7_5 lo_value_7_6 lo_eq_7_6 lo_reverse_7_6 lo_value_7_7 lo_eq_7_7 lo_reverse_7_7 lo_transit_0 lo_transit_1 lo_transit_2 lo_transit_3 lo_transit_4 lo_transit_5 lo_transit_6 lo_transit_7 lo_transit_8 lo_transit_9 lo_transit_10 lo_transit_11 lo_transit_12 lo_transit_13 lo_transit_14 lo_transit_15 \
  "$cake_dir/compiler/backend/proofs/word_cseProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe target_props_io_events_probeScript.sml target_props_io_events_probe.out \
  tp_io_full_statement tp_io_type \
  "$cake_dir/compiler/backend/semantics/targetPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe stack_props_register_bounds_probeScript.sml stack_props_register_bounds_probe.out \
  rb_definition_exp rb_definition_inst rb_definition_prog rb_exp_0_3_1 rb_exp_0_4_1 rb_exp_1_0_1 rb_exp_1_100_1 rb_exp_2_0_1 rb_exp_2_100_1 rb_exp_3_3_1 rb_exp_3_4_1 rb_exp_4_5_1 rb_exp_4_6_1 rb_exp_5_0_1 rb_exp_5_100_1 rb_exp_6_9_1 rb_exp_6_10_1 rb_exp_7_0_1 rb_exp_7_100_1 rb_inst_8_0_1 rb_inst_8_100_1 rb_inst_9_1_1 rb_inst_9_2_1 rb_inst_10_2_1 rb_inst_10_3_1 rb_inst_11_2_1 rb_inst_11_3_1 rb_inst_12_2_1 rb_inst_12_3_1 rb_inst_13_2_1 rb_inst_13_3_1 rb_inst_14_2_1 rb_inst_14_3_1 rb_inst_15_2_1 rb_inst_15_3_1 rb_inst_16_2_1 rb_inst_16_3_1 rb_inst_17_2_1 rb_inst_17_3_1 rb_inst_18_3_1 rb_inst_18_4_1 rb_inst_19_2_1 rb_inst_19_3_1 rb_inst_20_3_1 rb_inst_20_4_1 rb_inst_21_2_1 rb_inst_21_3_1 rb_inst_22_3_1 rb_inst_22_4_1 rb_inst_23_4_1 rb_inst_23_5_1 rb_inst_24_5_1 rb_inst_24_6_1 rb_inst_25_4_1 rb_inst_25_5_1 rb_inst_26_4_1 rb_inst_26_5_1 rb_inst_27_4_1 rb_inst_27_5_1 rb_inst_28_1_1 rb_inst_28_2_1 rb_inst_29_1_1 rb_inst_29_2_1 rb_inst_30_1_1 rb_inst_30_2_1 rb_inst_31_0_1 rb_inst_31_100_1 rb_inst_32_0_1 rb_inst_32_100_1 rb_inst_33_0_1 rb_inst_33_100_1 rb_inst_34_0_1 rb_inst_34_100_1 rb_inst_35_0_1 rb_inst_35_100_1 rb_inst_36_0_1 rb_inst_36_100_1 rb_inst_37_0_1 rb_inst_37_100_1 rb_inst_38_0_1 rb_inst_38_100_1 rb_inst_39_0_1 rb_inst_39_100_1 rb_inst_40_0_1 rb_inst_40_100_1 rb_inst_41_0_1 rb_inst_41_100_1 rb_inst_42_2_1 rb_inst_42_3_1 rb_inst_43_2_1 rb_inst_43_3_1 rb_prog_44_0_1 rb_prog_44_100_1 rb_prog_45_1_1 rb_prog_45_2_1 rb_prog_46_1_1 rb_prog_46_2_1 rb_prog_47_1_1 rb_prog_47_2_1 rb_prog_48_0_1 rb_prog_48_100_1 rb_prog_49_2_1 rb_prog_49_3_1 rb_prog_50_0_1 rb_prog_50_100_1 rb_prog_51_2_1 rb_prog_51_3_1 rb_prog_52_3_1 rb_prog_52_4_1 rb_prog_53_2_1 rb_prog_53_3_1 rb_prog_54_3_1 rb_prog_54_4_1 rb_prog_55_1_1 rb_prog_55_2_1 rb_prog_56_2_1 rb_prog_56_3_1 rb_prog_57_2_1 rb_prog_57_3_1 rb_prog_58_0_1 rb_prog_58_100_1 rb_prog_59_3_1 rb_prog_59_4_1 rb_prog_60_1_1 rb_prog_60_2_1 rb_prog_61_1_1 rb_prog_61_2_1 rb_prog_62_0_1 rb_prog_62_100_1 rb_prog_63_0_1 rb_prog_63_100_1 rb_prog_64_5_1 rb_prog_64_6_1 rb_prog_65_0_1 rb_prog_65_100_1 rb_prog_66_1_1 rb_prog_66_2_1 rb_prog_67_5_1 rb_prog_67_6_1 rb_prog_68_2_1 rb_prog_68_3_1 rb_prog_69_2_1 rb_prog_69_3_1 rb_prog_70_2_1 rb_prog_70_3_1 rb_prog_71_0_1 rb_prog_71_100_1 rb_prog_72_0_1 rb_prog_72_100_1 rb_prog_73_0_1 rb_prog_73_100_1 rb_prog_74_1_1 rb_prog_74_2_1 rb_prog_75_999_1 rb_prog_75_1000_1 rb_prog_76_1_1 rb_prog_76_2_1 rb_prog_77_999_1 rb_prog_77_1000_1 rb_prog_78_2_1 rb_prog_78_3_1 rb_prog_79_2_1 rb_prog_79_3_1 rb_prog_80_1_1 rb_prog_80_2_1 rb_prog_81_1_1 rb_prog_81_2_1 rb_prog_82_2_1 rb_prog_82_3_1 rb_prog_83_1_1 rb_prog_83_2_1 rb_exp_0_3_64 rb_exp_0_4_64 rb_exp_1_0_64 rb_exp_1_100_64 rb_exp_2_0_64 rb_exp_2_100_64 rb_exp_3_3_64 rb_exp_3_4_64 rb_exp_4_5_64 rb_exp_4_6_64 rb_exp_5_0_64 rb_exp_5_100_64 rb_exp_6_9_64 rb_exp_6_10_64 rb_exp_7_0_64 rb_exp_7_100_64 rb_inst_8_0_64 rb_inst_8_100_64 rb_inst_9_1_64 rb_inst_9_2_64 rb_inst_10_2_64 rb_inst_10_3_64 rb_inst_11_2_64 rb_inst_11_3_64 rb_inst_12_2_64 rb_inst_12_3_64 rb_inst_13_2_64 rb_inst_13_3_64 rb_inst_14_2_64 rb_inst_14_3_64 rb_inst_15_2_64 rb_inst_15_3_64 rb_inst_16_2_64 rb_inst_16_3_64 rb_inst_17_2_64 rb_inst_17_3_64 rb_inst_18_3_64 rb_inst_18_4_64 rb_inst_19_2_64 rb_inst_19_3_64 rb_inst_20_3_64 rb_inst_20_4_64 rb_inst_21_2_64 rb_inst_21_3_64 rb_inst_22_3_64 rb_inst_22_4_64 rb_inst_23_4_64 rb_inst_23_5_64 rb_inst_24_5_64 rb_inst_24_6_64 rb_inst_25_4_64 rb_inst_25_5_64 rb_inst_26_4_64 rb_inst_26_5_64 rb_inst_27_4_64 rb_inst_27_5_64 rb_inst_28_1_64 rb_inst_28_2_64 rb_inst_29_1_64 rb_inst_29_2_64 rb_inst_30_1_64 rb_inst_30_2_64 rb_inst_31_0_64 rb_inst_31_100_64 rb_inst_32_0_64 rb_inst_32_100_64 rb_inst_33_0_64 rb_inst_33_100_64 rb_inst_34_0_64 rb_inst_34_100_64 rb_inst_35_0_64 rb_inst_35_100_64 rb_inst_36_0_64 rb_inst_36_100_64 rb_inst_37_0_64 rb_inst_37_100_64 rb_inst_38_0_64 rb_inst_38_100_64 rb_inst_39_0_64 rb_inst_39_100_64 rb_inst_40_0_64 rb_inst_40_100_64 rb_inst_41_0_64 rb_inst_41_100_64 rb_inst_42_2_64 rb_inst_42_3_64 rb_inst_43_2_64 rb_inst_43_3_64 rb_prog_44_0_64 rb_prog_44_100_64 rb_prog_45_1_64 rb_prog_45_2_64 rb_prog_46_1_64 rb_prog_46_2_64 rb_prog_47_1_64 rb_prog_47_2_64 rb_prog_48_0_64 rb_prog_48_100_64 rb_prog_49_2_64 rb_prog_49_3_64 rb_prog_50_0_64 rb_prog_50_100_64 rb_prog_51_2_64 rb_prog_51_3_64 rb_prog_52_3_64 rb_prog_52_4_64 rb_prog_53_2_64 rb_prog_53_3_64 rb_prog_54_3_64 rb_prog_54_4_64 rb_prog_55_1_64 rb_prog_55_2_64 rb_prog_56_2_64 rb_prog_56_3_64 rb_prog_57_2_64 rb_prog_57_3_64 rb_prog_58_0_64 rb_prog_58_100_64 rb_prog_59_3_64 rb_prog_59_4_64 rb_prog_60_1_64 rb_prog_60_2_64 rb_prog_61_1_64 rb_prog_61_2_64 rb_prog_62_0_64 rb_prog_62_100_64 rb_prog_63_0_64 rb_prog_63_100_64 rb_prog_64_5_64 rb_prog_64_6_64 rb_prog_65_0_64 rb_prog_65_100_64 rb_prog_66_1_64 rb_prog_66_2_64 rb_prog_67_5_64 rb_prog_67_6_64 rb_prog_68_2_64 rb_prog_68_3_64 rb_prog_69_2_64 rb_prog_69_3_64 rb_prog_70_2_64 rb_prog_70_3_64 rb_prog_71_0_64 rb_prog_71_100_64 rb_prog_72_0_64 rb_prog_72_100_64 rb_prog_73_0_64 rb_prog_73_100_64 rb_prog_74_1_64 rb_prog_74_2_64 rb_prog_75_999_64 rb_prog_75_1000_64 rb_prog_76_1_64 rb_prog_76_2_64 rb_prog_77_999_64 rb_prog_77_1000_64 rb_prog_78_2_64 rb_prog_78_3_64 rb_prog_79_2_64 rb_prog_79_3_64 rb_prog_80_1_64 rb_prog_80_2_64 rb_prog_81_1_64 rb_prog_81_2_64 rb_prog_82_2_64 rb_prog_82_3_64 rb_prog_83_1_64 rb_prog_83_2_64 rb_exp_0_3_80 rb_exp_0_4_80 rb_exp_1_0_80 rb_exp_1_100_80 rb_exp_2_0_80 rb_exp_2_100_80 rb_exp_3_3_80 rb_exp_3_4_80 rb_exp_4_5_80 rb_exp_4_6_80 rb_exp_5_0_80 rb_exp_5_100_80 rb_exp_6_9_80 rb_exp_6_10_80 rb_exp_7_0_80 rb_exp_7_100_80 rb_inst_8_0_80 rb_inst_8_100_80 rb_inst_9_1_80 rb_inst_9_2_80 rb_inst_10_2_80 rb_inst_10_3_80 rb_inst_11_2_80 rb_inst_11_3_80 rb_inst_12_2_80 rb_inst_12_3_80 rb_inst_13_2_80 rb_inst_13_3_80 rb_inst_14_2_80 rb_inst_14_3_80 rb_inst_15_2_80 rb_inst_15_3_80 rb_inst_16_2_80 rb_inst_16_3_80 rb_inst_17_2_80 rb_inst_17_3_80 rb_inst_18_3_80 rb_inst_18_4_80 rb_inst_19_2_80 rb_inst_19_3_80 rb_inst_20_3_80 rb_inst_20_4_80 rb_inst_21_2_80 rb_inst_21_3_80 rb_inst_22_3_80 rb_inst_22_4_80 rb_inst_23_4_80 rb_inst_23_5_80 rb_inst_24_5_80 rb_inst_24_6_80 rb_inst_25_4_80 rb_inst_25_5_80 rb_inst_26_4_80 rb_inst_26_5_80 rb_inst_27_4_80 rb_inst_27_5_80 rb_inst_28_1_80 rb_inst_28_2_80 rb_inst_29_1_80 rb_inst_29_2_80 rb_inst_30_1_80 rb_inst_30_2_80 rb_inst_31_0_80 rb_inst_31_100_80 rb_inst_32_0_80 rb_inst_32_100_80 rb_inst_33_0_80 rb_inst_33_100_80 rb_inst_34_0_80 rb_inst_34_100_80 rb_inst_35_0_80 rb_inst_35_100_80 rb_inst_36_0_80 rb_inst_36_100_80 rb_inst_37_0_80 rb_inst_37_100_80 rb_inst_38_0_80 rb_inst_38_100_80 rb_inst_39_0_80 rb_inst_39_100_80 rb_inst_40_0_80 rb_inst_40_100_80 rb_inst_41_0_80 rb_inst_41_100_80 rb_inst_42_2_80 rb_inst_42_3_80 rb_inst_43_2_80 rb_inst_43_3_80 rb_prog_44_0_80 rb_prog_44_100_80 rb_prog_45_1_80 rb_prog_45_2_80 rb_prog_46_1_80 rb_prog_46_2_80 rb_prog_47_1_80 rb_prog_47_2_80 rb_prog_48_0_80 rb_prog_48_100_80 rb_prog_49_2_80 rb_prog_49_3_80 rb_prog_50_0_80 rb_prog_50_100_80 rb_prog_51_2_80 rb_prog_51_3_80 rb_prog_52_3_80 rb_prog_52_4_80 rb_prog_53_2_80 rb_prog_53_3_80 rb_prog_54_3_80 rb_prog_54_4_80 rb_prog_55_1_80 rb_prog_55_2_80 rb_prog_56_2_80 rb_prog_56_3_80 rb_prog_57_2_80 rb_prog_57_3_80 rb_prog_58_0_80 rb_prog_58_100_80 rb_prog_59_3_80 rb_prog_59_4_80 rb_prog_60_1_80 rb_prog_60_2_80 rb_prog_61_1_80 rb_prog_61_2_80 rb_prog_62_0_80 rb_prog_62_100_80 rb_prog_63_0_80 rb_prog_63_100_80 rb_prog_64_5_80 rb_prog_64_6_80 rb_prog_65_0_80 rb_prog_65_100_80 rb_prog_66_1_80 rb_prog_66_2_80 rb_prog_67_5_80 rb_prog_67_6_80 rb_prog_68_2_80 rb_prog_68_3_80 rb_prog_69_2_80 rb_prog_69_3_80 rb_prog_70_2_80 rb_prog_70_3_80 rb_prog_71_0_80 rb_prog_71_100_80 rb_prog_72_0_80 rb_prog_72_100_80 rb_prog_73_0_80 rb_prog_73_100_80 rb_prog_74_1_80 rb_prog_74_2_80 rb_prog_75_999_80 rb_prog_75_1000_80 rb_prog_76_1_80 rb_prog_76_2_80 rb_prog_77_999_80 rb_prog_77_1000_80 rb_prog_78_2_80 rb_prog_78_3_80 rb_prog_79_2_80 rb_prog_79_3_80 rb_prog_80_1_80 rb_prog_80_2_80 rb_prog_81_1_80 rb_prog_81_2_80 rb_prog_82_2_80 rb_prog_82_3_80 rb_prog_83_1_80 rb_prog_83_2_80 \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" "$cake_dir/compiler/backend/semantics"

run_probe word_to_stack_bitmap_word_lemmas_probeScript.sml word_to_stack_bitmap_word_lemmas_probe.out \
  bw_full_max0 bw_full_max1 bw_full_orzero bw_full_shift bw_full_orone bw_max_0_0 bw_max_1_0 bw_max_0_1 bw_max_1_1 bw_max_0_2 bw_max_1_2 bw_max_0_3 bw_max_1_3 bw_max_0_10 bw_max_1_10 bw_max_0_64 bw_max_1_64 bw_max_0_100 bw_max_1_100 bw_or_value_0_0_1 bw_or_law_0_0_1 bw_or_value_0_1_1 bw_or_law_0_1_1 bw_orone_0_1 bw_shift_value_0_1 bw_shift_law_0_1 bw_or_value_1_0_1 bw_or_law_1_0_1 bw_or_value_1_1_1 bw_or_law_1_1_1 bw_orone_1_1 bw_shift_value_1_1 bw_msb_drop_1_1 bw_or_value_0_0_2 bw_or_law_0_0_2 bw_or_value_0_1_2 bw_or_law_0_1_2 bw_or_value_0_2_2 bw_or_law_0_2_2 bw_or_value_0_3_2 bw_or_law_0_3_2 bw_orone_0_2 bw_shift_value_0_2 bw_shift_law_0_2 bw_or_value_1_0_2 bw_or_law_1_0_2 bw_or_value_1_1_2 bw_or_law_1_1_2 bw_or_value_1_2_2 bw_or_law_1_2_2 bw_or_value_1_3_2 bw_or_law_1_3_2 bw_orone_1_2 bw_shift_value_1_2 bw_shift_law_1_2 bw_or_value_2_0_2 bw_or_law_2_0_2 bw_or_value_2_1_2 bw_or_law_2_1_2 bw_or_value_2_2_2 bw_or_law_2_2_2 bw_or_value_2_3_2 bw_or_law_2_3_2 bw_orone_2_2 bw_shift_value_2_2 bw_msb_drop_2_2 bw_or_value_3_0_2 bw_or_law_3_0_2 bw_or_value_3_1_2 bw_or_law_3_1_2 bw_or_value_3_2_2 bw_or_law_3_2_2 bw_or_value_3_3_2 bw_or_law_3_3_2 bw_orone_3_2 bw_shift_value_3_2 bw_msb_drop_3_2 bw_or_value_0_0_32 bw_or_law_0_0_32 bw_or_value_0_1_32 bw_or_law_0_1_32 bw_or_value_0_2_32 bw_or_law_0_2_32 bw_or_value_0_3_32 bw_or_law_0_3_32 bw_or_value_0_4_32 bw_or_law_0_4_32 bw_orone_0_32 bw_shift_value_0_32 bw_shift_law_0_32 bw_or_value_1_0_32 bw_or_law_1_0_32 bw_or_value_1_1_32 bw_or_law_1_1_32 bw_or_value_1_2_32 bw_or_law_1_2_32 bw_or_value_1_3_32 bw_or_law_1_3_32 bw_or_value_1_4_32 bw_or_law_1_4_32 bw_orone_1_32 bw_shift_value_1_32 bw_shift_law_1_32 bw_or_value_2_0_32 bw_or_law_2_0_32 bw_or_value_2_1_32 bw_or_law_2_1_32 bw_or_value_2_2_32 bw_or_law_2_2_32 bw_or_value_2_3_32 bw_or_law_2_3_32 bw_or_value_2_4_32 bw_or_law_2_4_32 bw_orone_2_32 bw_shift_value_2_32 bw_shift_law_2_32 bw_or_value_3_0_32 bw_or_law_3_0_32 bw_or_value_3_1_32 bw_or_law_3_1_32 bw_or_value_3_2_32 bw_or_law_3_2_32 bw_or_value_3_3_32 bw_or_law_3_3_32 bw_or_value_3_4_32 bw_or_law_3_4_32 bw_orone_3_32 bw_shift_value_3_32 bw_msb_drop_3_32 bw_or_value_4_0_32 bw_or_law_4_0_32 bw_or_value_4_1_32 bw_or_law_4_1_32 bw_or_value_4_2_32 bw_or_law_4_2_32 bw_or_value_4_3_32 bw_or_law_4_3_32 bw_or_value_4_4_32 bw_or_law_4_4_32 bw_orone_4_32 bw_shift_value_4_32 bw_msb_drop_4_32 bw_or_value_0_0_64 bw_or_law_0_0_64 bw_or_value_0_1_64 bw_or_law_0_1_64 bw_or_value_0_2_64 bw_or_law_0_2_64 bw_or_value_0_3_64 bw_or_law_0_3_64 bw_or_value_0_4_64 bw_or_law_0_4_64 bw_orone_0_64 bw_shift_value_0_64 bw_shift_law_0_64 bw_or_value_1_0_64 bw_or_law_1_0_64 bw_or_value_1_1_64 bw_or_law_1_1_64 bw_or_value_1_2_64 bw_or_law_1_2_64 bw_or_value_1_3_64 bw_or_law_1_3_64 bw_or_value_1_4_64 bw_or_law_1_4_64 bw_orone_1_64 bw_shift_value_1_64 bw_shift_law_1_64 bw_or_value_2_0_64 bw_or_law_2_0_64 bw_or_value_2_1_64 bw_or_law_2_1_64 bw_or_value_2_2_64 bw_or_law_2_2_64 bw_or_value_2_3_64 bw_or_law_2_3_64 bw_or_value_2_4_64 bw_or_law_2_4_64 bw_orone_2_64 bw_shift_value_2_64 bw_shift_law_2_64 bw_or_value_3_0_64 bw_or_law_3_0_64 bw_or_value_3_1_64 bw_or_law_3_1_64 bw_or_value_3_2_64 bw_or_law_3_2_64 bw_or_value_3_3_64 bw_or_law_3_3_64 bw_or_value_3_4_64 bw_or_law_3_4_64 bw_orone_3_64 bw_shift_value_3_64 bw_msb_drop_3_64 bw_or_value_4_0_64 bw_or_law_4_0_64 bw_or_value_4_1_64 bw_or_law_4_1_64 bw_or_value_4_2_64 bw_or_law_4_2_64 bw_or_value_4_3_64 bw_or_law_4_3_64 bw_or_value_4_4_64 bw_or_law_4_4_64 bw_orone_4_64 bw_shift_value_4_64 bw_msb_drop_4_64 bw_or_value_0_0_80 bw_or_law_0_0_80 bw_or_value_0_1_80 bw_or_law_0_1_80 bw_or_value_0_2_80 bw_or_law_0_2_80 bw_or_value_0_3_80 bw_or_law_0_3_80 bw_or_value_0_4_80 bw_or_law_0_4_80 bw_orone_0_80 bw_shift_value_0_80 bw_shift_law_0_80 bw_or_value_1_0_80 bw_or_law_1_0_80 bw_or_value_1_1_80 bw_or_law_1_1_80 bw_or_value_1_2_80 bw_or_law_1_2_80 bw_or_value_1_3_80 bw_or_law_1_3_80 bw_or_value_1_4_80 bw_or_law_1_4_80 bw_orone_1_80 bw_shift_value_1_80 bw_shift_law_1_80 bw_or_value_2_0_80 bw_or_law_2_0_80 bw_or_value_2_1_80 bw_or_law_2_1_80 bw_or_value_2_2_80 bw_or_law_2_2_80 bw_or_value_2_3_80 bw_or_law_2_3_80 bw_or_value_2_4_80 bw_or_law_2_4_80 bw_orone_2_80 bw_shift_value_2_80 bw_shift_law_2_80 bw_or_value_3_0_80 bw_or_law_3_0_80 bw_or_value_3_1_80 bw_or_law_3_1_80 bw_or_value_3_2_80 bw_or_law_3_2_80 bw_or_value_3_3_80 bw_or_law_3_3_80 bw_or_value_3_4_80 bw_or_law_3_4_80 bw_orone_3_80 bw_shift_value_3_80 bw_msb_drop_3_80 bw_or_value_4_0_80 bw_or_law_4_0_80 bw_or_value_4_1_80 bw_or_law_4_1_80 bw_or_value_4_2_80 bw_or_law_4_2_80 bw_or_value_4_3_80 bw_or_law_4_3_80 bw_or_value_4_4_80 bw_or_law_4_4_80 bw_orone_4_80 bw_shift_value_4_80 bw_msb_drop_4_80 bw_type_word bw_type_maximum bw_type_genlist \
  "$cake_dir/compiler/backend/proofs/word_to_stackProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe lab_to_target_navigation_bounds_probeScript.sml lab_to_target_navigation_bounds_probe.out \
  sec_loc_to_pc_bound sec_loc_to_pc_bound_types loc_to_pc_bound loc_to_pc_bound_types zero_empty local_last_bound local_last_count code_empty_tail_bound code_total_count wide_zero_empty \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe lab_to_target_position_values_probeScript.sml lab_to_target_position_values_probe.out \
  line_length_def line_length_def_types sec_pos_val_def sec_pos_val_def_types sec_pos_val_too_big sec_pos_val_too_big_types every_label_sec_pos_val every_label_sec_pos_val_types pos_val_def pos_val_def_types pos_val_thm0 pos_val_thm0_types pos_val_thm pos_val_thm_types pos_val_thm_operator_types pos_val_acc pos_val_acc_types label_zero_length label_nonzero_length asm_bytes_length labasm_bytes_length sec_first sec_second sec_equal_exhaustion sec_past_exhaustion sec_labels_only code_first code_second code_third code_equal_exhaustion code_past_exhaustion code_empty_wide \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe lab_to_target_ignore_clocks_probeScript.sml lab_to_target_ignore_clocks_probe.out \
  lt_ignore_full_statement lt_ignore_type \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"
run_probe stack_remove_comp_probeScript.sml stack_remove_comp_probe.out \
  comp_full_def comp_type comp_get_heap_tree comp_get_heap_equation comp_get_store_tree comp_get_store_equation comp_set_heap_tree comp_set_heap_equation comp_set_temp_tree comp_set_temp_equation comp_op_heap_tree comp_op_heap_equation comp_free_tree comp_free_equation comp_alloc_false_tree comp_alloc_false_equation comp_alloc_true_tree comp_alloc_true_equation comp_store_direct_tree comp_store_direct_equation comp_load_direct_tree comp_load_direct_equation comp_store_fallback_tree comp_store_fallback_equation comp_load_fallback_tree comp_load_fallback_equation comp_data_write_tree comp_data_write_equation comp_load_any_tree comp_load_any_equation comp_store_any_tree comp_store_any_equation comp_get_size_1_tree comp_get_size_1_equation comp_set_size_1_tree comp_set_size_1_equation comp_get_size_32_tree comp_get_size_32_equation comp_set_size_32_tree comp_set_size_32_equation comp_get_size_64_tree comp_get_size_64_equation comp_set_size_64_tree comp_set_size_64_equation comp_get_size_80_tree comp_get_size_80_equation comp_set_size_80_tree comp_set_size_80_equation comp_bitmap_tree comp_bitmap_equation comp_consts_none_tree comp_consts_none_equation comp_consts_some_tree comp_consts_some_equation comp_seq_tree comp_seq_equation comp_if_tree comp_if_equation comp_loop_tree comp_loop_equation comp_call_0_0_tree comp_call_0_0_equation comp_call_0_1_tree comp_call_0_1_equation comp_call_1_0_tree comp_call_1_0_equation comp_call_1_1_tree comp_call_1_1_equation comp_signed_negative_tree comp_signed_negative_equation comp_signed_reversed_tree comp_signed_reversed_equation comp_wrapped_zero_tree comp_wrapped_zero_equation comp_unchanged_skip_tree comp_unchanged_skip_equation comp_unchanged_inst_tree comp_unchanged_inst_equation comp_unchanged_jump_tree comp_unchanged_jump_equation comp_unchanged_alloc_runtime_tree comp_unchanged_alloc_runtime_equation comp_unchanged_raise_tree comp_unchanged_raise_equation comp_unchanged_return_tree comp_unchanged_return_equation comp_unchanged_break_tree comp_unchanged_break_equation comp_unchanged_continue_tree comp_unchanged_continue_equation comp_unchanged_ffi_tree comp_unchanged_ffi_equation comp_unchanged_tick_tree comp_unchanged_tick_equation comp_unchanged_loc_tree comp_unchanged_loc_equation comp_unchanged_install_tree comp_unchanged_install_equation comp_unchanged_shared_tree comp_unchanged_shared_equation comp_unchanged_code_write_tree comp_unchanged_code_write_equation comp_unchanged_raw_tree comp_unchanged_raw_equation comp_unchanged_halt_tree comp_unchanged_halt_equation \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"

run_probe ssa_cc_trans_correct_register_writes_probeScript.sml ssa_cc_trans_correct_register_writes_probe.out \
  sw_assign_full sw_get_full sw_loc_full sw_type_st sw_type_cst sw_type_expr sw_type_store sw_type_label sw_type_lt \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe ssa_cc_trans_correct_state_writes_probeScript.sml ssa_cc_trans_correct_state_writes_probe.out \
  ss_set_full ss_store_full ss_type_st ss_type_cst ss_type_expr ss_type_store ss_type_n ss_type_lt \
  "$cake_dir/compiler/backend/proofs/word_allocProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe lab_to_target_ignore_clocks_probeScript.sml lab_to_target_ignore_clocks_probe.out \
  lt_ignore_full_statement lt_ignore_type \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe target_props_clock_io_events_probeScript.sml target_props_clock_io_events_probe.out \
  tp_clock_io_full_statement tp_clock_io_type \
  "$cake_dir/compiler/backend/semantics/targetPropsScript.sml" "$cake_dir/compiler/backend/semantics"
run_probe stack_remove_prog_comp_probeScript.sml stack_remove_prog_comp_probe.out \
  prog_comp_full_def prog_comp_type wrapper_1_bool wrapper_1_list wrapper_1_nat wrapper_8_bool wrapper_8_list wrapper_8_nat wrapper_32_bool wrapper_32_list wrapper_32_nat wrapper_64_bool wrapper_64_list wrapper_64_nat wrapper_80_bool wrapper_80_list wrapper_80_nat \
  "$cake_dir/compiler/backend/stack_removeScript.sml" "$cake_dir/compiler/backend"

run_probe word_to_stack_native_addr_probeScript.sml word_to_stack_native_addr_probe.out \
  addr_load_0_2_0 addr_load_0_2_8 addr_load_0_2_18446744073709551608 addr_load_4_2_0 addr_load_4_2_8 addr_load_4_2_18446744073709551608 addr_load_0_6_0 addr_load_0_6_8 addr_load_0_6_18446744073709551608 addr_load_4_6_0 addr_load_4_6_8 addr_load_4_6_18446744073709551608 addr_store_0_2_0 addr_store_0_2_8 addr_store_0_2_18446744073709551608 addr_store_4_2_0 addr_store_4_2_8 addr_store_4_2_18446744073709551608 addr_store_0_6_0 addr_store_0_6_8 addr_store_0_6_18446744073709551608 addr_store_4_6_0 addr_store_4_6_8 addr_store_4_6_18446744073709551608 addr_load8_0_2_0 addr_load8_0_2_8 addr_load8_0_2_18446744073709551608 addr_load8_4_2_0 addr_load8_4_2_8 addr_load8_4_2_18446744073709551608 addr_load8_0_6_0 addr_load8_0_6_8 addr_load8_0_6_18446744073709551608 addr_load8_4_6_0 addr_load8_4_6_8 addr_load8_4_6_18446744073709551608 addr_store8_0_2_0 addr_store8_0_2_8 addr_store8_0_2_18446744073709551608 addr_store8_4_2_0 addr_store8_4_2_8 addr_store8_4_2_18446744073709551608 addr_store8_0_6_0 addr_store8_0_6_8 addr_store8_0_6_18446744073709551608 addr_store8_4_6_0 addr_store8_4_6_8 addr_store8_4_6_18446744073709551608 addr_load32_0_2_0 addr_load32_0_2_8 addr_load32_0_2_18446744073709551608 addr_load32_4_2_0 addr_load32_4_2_8 addr_load32_4_2_18446744073709551608 addr_load32_0_6_0 addr_load32_0_6_8 addr_load32_0_6_18446744073709551608 addr_load32_4_6_0 addr_load32_4_6_8 addr_load32_4_6_18446744073709551608 addr_store32_0_2_0 addr_store32_0_2_8 addr_store32_0_2_18446744073709551608 addr_store32_4_2_0 addr_store32_4_2_8 addr_store32_4_2_18446744073709551608 addr_store32_0_6_0 addr_store32_0_6_8 addr_store32_0_6_18446744073709551608 addr_store32_4_6_0 addr_store32_4_6_8 addr_store32_4_6_18446744073709551608 selected_store_0 selected_store_8 selected_store_2047 selected_store_2048 selected_store_18446744073709551608 \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" "$cake_dir/compiler/backend"

run_probe lab_to_target_position_append_probeScript.sml lab_to_target_position_append_probe.out \
  label_zero_def label_zero_def_types sec_label_zero_def sec_label_zero_def_types sec_label_zero_pos_val_0 sec_label_zero_pos_val_0_types pos_val_append pos_val_append_types zero_label nonzero_label asm_annotation_ignored labasm_annotation_ignored suffix_valid prefix_invalid zero_suffix_position before_boundary at_boundary prefix_at_boundary suffix_at_boundary past_boundary far_past_boundary empty_prefix_zero empty_suffix_past label_only_prefix_boundary label_only_prefix_past \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"

run_probe lab_to_target_encoding_validity_probeScript.sml lab_to_target_encoding_validity_probe.out \
  lab_lookup_def lab_lookup_def_types lab_lookup_IMP lab_lookup_IMP_types line_ok_def line_ok_def_types lines_ok_def lines_ok_def_types all_enc_ok_def all_enc_ok_def_types all_enc_ok_cons all_enc_ok_cons_types all_enc_ok_imp_sec_label_zero all_enc_ok_imp_sec_label_zero_types pos_val_0 pos_val_0_types pos_val_bound pos_val_bound_types lookup_generic_bool lookup_outer_missing lookup_inner_missing label_even label_odd label_nonzero asm_skip asm_padding asm_bad_length asm_bad_bytes asm_bad_reg asm_cbw lab_halt lab_install lab_ffi_index lab_ffi_missing_default lab_call_unsupported lab_jump lab_jump_cmp lab_loc lab_missing_label all_empty all_empty_section_even all_empty_section_odd all_code_valid all_code_bytes all_zero_position independent_bound_position \
  "$cake_dir/compiler/backend/proofs/lab_to_targetProofScript.sml" "$cake_dir/compiler/backend/proofs"
