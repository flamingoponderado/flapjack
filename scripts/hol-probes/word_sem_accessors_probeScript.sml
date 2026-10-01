(*
  Direct HOL-EVAL fixture for the wordSem state accessors ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/Accessors.lean
  (cakeml/compiler/backend/semantics/wordSemScript.sml:37-68, 262-372,
  707-714, 941-944) at 64-bit words.  States are record updates of a free
  state `s`, so every row holds for every omitted field.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,'ffi) wordSem$state``;
val st = ``^s with <| locals := insert 1 (Word 5w) (insert 2 (Loc 4 0) LN);
                      store := FEMPTY |+ (NextFree, Word 7w);
                      fp_regs := FEMPTY |+ (3, 11w);
                      memory := (\a. if a = 8w then Word 9w else Loc 0 0);
                      mdomain := {8w} |>``;

val _ = print_eval "cmp_equal" ``word_cmp Equal (Word 3w : 64 word_loc) (Word 3w)``;
val _ = print_eval "cmp_less_signed" ``word_cmp Less (Word (-1w) : 64 word_loc) (Word 0w)``;
val _ = print_eval "cmp_lower" ``word_cmp Lower (Word (-1w) : 64 word_loc) (Word 0w)``;
val _ = print_eval "cmp_test_loc" ``word_cmp Test (Loc 3 0 : 64 word_loc) (Word 1w)``;
val _ = print_eval "cmp_nottest_loc" ``word_cmp NotTest (Loc 3 0 : 64 word_loc) (Word 1w)``;
val _ = print_eval "cmp_test_loc_nz" ``word_cmp Test (Loc 3 1 : 64 word_loc) (Word 1w)``;
val _ = print_eval "cmp_test_loc_two" ``word_cmp Test (Loc 3 0 : 64 word_loc) (Word 2w)``;
val _ = print_eval "cmp_equal_loc" ``word_cmp Equal (Loc 1 2 : 64 word_loc) (Loc 1 2)``;
val _ = print_eval "fwd_ptr_8" ``is_fwd_ptr (Word 8w : 64 word_loc)``;
val _ = print_eval "fwd_ptr_9" ``is_fwd_ptr (Word 9w : 64 word_loc)``;
val _ = print_eval "fwd_ptr_loc" ``is_fwd_ptr (Loc 0 0 : 64 word_loc)``;
val _ = print_eval "exp_op" ``word_exp ^st (Op Add [Var 1; Lookup NextFree; Const 1w])``;
val _ = print_eval "exp_op_loc" ``word_exp ^st (Op Add [Var 1; Var 2])``;
val _ = print_eval "exp_load_hit" ``word_exp ^st (Load (Const 8w))``;
val _ = print_eval "exp_load_miss" ``word_exp ^st (Load (Const 16w))``;
val _ = print_eval "exp_shift" ``word_exp ^st (Shift Lsl (Var 1) (Const 3w))``;
val _ = print_eval "exp_shift_big" ``word_exp ^st (Shift Lsl (Var 1) (Const 64w))``;
val _ = print_eval "get_vars_hit" ``get_vars [2; 1] ^st``;
val _ = print_eval "get_vars_miss" ``get_vars [1; 3] ^st``;
val _ = print_eval "unset_var" ``get_var 1 (unset_var 1 ^st)``;
val _ = print_eval "set_vars" ``get_vars [1; 6] (set_vars [6; 1] [Word 2w; Word 3w] ^st)``;
val _ = print_eval "set_store" ``get_store Handler (set_store Handler (Word 4w) ^st)``;
val _ = print_eval "flush_true" ``get_store NextFree (flush_state T ^st)``;
val _ = print_eval "flush_false" ``get_store NextFree (flush_state F ^st)``;
val _ = print_eval "flush_locals" ``get_var 1 (flush_state F ^st)``;
val _ = print_eval "fp_var" ``get_fp_var 3 (set_fp_var 4 12w ^st)``;
val _ = print_eval "fix_clock"
  ``(\(r, t:(64,'c,'ffi) wordSem$state). (r, t.clock, t.termdep))
      (fix_clock (^s with <| clock := 3; termdep := 7 |>)
        (5:num, ^s with <| clock := 9; termdep := 2 |>))``;
val _ = print_eval "mem_store_miss" ``mem_store 16w (Word 1w) ^st = NONE``;
val _ = print_eval "mem_store_hit"
  ``OPTION_MAP (\t. t.memory 8w) (mem_store 8w (Word 1w) ^st)``;
val _ = print_eval "var_imm" ``get_var_imm (Imm 4w) ^st``;
val _ = print_eval "var_imm_reg" ``get_var_imm (Reg 2) ^st``;

(* h29l.12: only the specified Word clauses are observable. Never evaluate Loc. *)
val _ = print_eval "the_word_word1" ``theWord (Word (1w:word1))``;
val _ = print_eval "the_word_word64" ``theWord (Word (18446744073709551615w:word64))``;
val _ = print_eval "get_word_word32" ``get_word (Word (2147483648w:word32))``;
val _ = print_eval "get_word_word80" ``get_word (Word (1208925819614629174706175w:80 word))``;
