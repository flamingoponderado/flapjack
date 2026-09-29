(*
  Direct HOL-EVAL fixture for the wordSem environment/stack helpers ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/Env.lean
  (cakeml/compiler/backend/semantics/wordSemScript.sml:472-612), together with
  misc$fromList2 and mllist$sort, at 64-bit words.  States are record
  updates of a free state `s`, and the rows observe projections.
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

(* EVAL leaves list_rearrange's guard BIJ f (count n) (count n) (printed as
   PERMUTES over the enumerated count set) unevaluated; decide it by
   unfolding BIJ/INJ/SURJ over that finite set. *)
fun print_bij label q =
  let
    val th = (EVAL THENC SIMP_CONV (srw_ss())
      [BIJ_DEF, INJ_DEF, SURJ_DEF, DISJ_IMP_THM, FORALL_AND_THM,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]) q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,'ffi) wordSem$state``;

val _ = print_eval "kvc_loc_loc" ``key_val_compare (1:num, Loc 3 4 : 64 word_loc) (1, Loc 1 2)``;
val _ = print_eval "kvc_loc_loc_eq" ``key_val_compare (1:num, Loc 3 4 : 64 word_loc) (1, Loc 3 5)``;
val _ = print_eval "kvc_word_signed" ``key_val_compare (1:num, Word (-1w) : 64 word_loc) (1, Word 0w)``;
val _ = print_eval "kvc_word_signed_rev" ``key_val_compare (1:num, Word 0w : 64 word_loc) (1, Word (-1w))``;
val _ = print_eval "kvc_key" ``key_val_compare (2:num, Loc 0 0 : 64 word_loc) (1, Word 0w)``;
val _ = print_eval "kvc_loc_word" ``key_val_compare (1:num, Loc 0 0 : 64 word_loc) (1, Word 0w)``;
val _ = print_eval "kvc_word_loc" ``key_val_compare (1:num, Word 5w : 64 word_loc) (1, Loc 0 0)``;
val _ = print_bij "rearrange_rev" ``list_rearrange (\i. 2 - i) [10:num; 20; 30]``;
val _ = print_bij "rearrange_bad" ``list_rearrange (\i. 0) [10:num; 20]``;
val _ = print_bij "rearrange_out" ``list_rearrange (\i. i + 1) [10:num; 20]``;
val _ = print_eval "from_list2" ``toAList (fromList2 [Word 1w : 64 word_loc; Loc 2 3; Word 5w])``;
val _ = print_eval "sort_kvc"
  ``mllist$sort key_val_compare
      [(3:num, Word 1w : 64 word_loc); (7, Loc 0 0); (1, Word 2w); (5, Word 3w); (2, Loc 1 1)]``;
val _ = print_bij "env_to_list"
  ``FST (env_to_list (fromList2 [Word 1w : 64 word_loc; Loc 2 3; Word 5w])
      (\n i. if n = 0 then (if i = 0 then 1 else if i = 1 then 0 else i) else i))``;
val _ = print_eval "env_to_list_perm"
  ``SND (env_to_list (LN : 64 word_loc num_map) (\n i. n * 10 + i)) 2 3``;
val _ = print_eval "call_env"
  ``(\t:(64,'c,'ffi) wordSem$state. (toAList t.locals, t.locals_size, t.stack_max))
      (call_env [Word 1w; Word 2w] (SOME 5)
        (^s with <| stack := [StackFrame (SOME 2) [] [] NONE]; stack_max := SOME 4 |>))``;
val _ = print_eval "call_env_none"
  ``(call_env [] NONE (^s with <| stack := []; stack_max := SOME 4 |>)).stack_max``;
val pushed = ``push_env (fromList2 [Word 1w : 64 word_loc], insert 3 (Loc 1 0) LN)
        (SOME (0:num, Skip : 64 wordLang$prog, 7:num, 8:num))
        (^s with <| stack := []; locals_size := SOME 2; handler := 9;
                    stack_max := SOME 1; permute := (\n i. i) |>)``;
val _ = print_eval "push_env_some"
  ``(\t:(64,'c,'ffi) wordSem$state. (t.stack, t.stack_max, t.handler)) ^pushed``;
val _ = print_eval "push_env_none"
  ``(\t:(64,'c,'ffi) wordSem$state. (t.stack, t.stack_max, t.handler))
      (push_env (LN, insert 3 (Loc 1 0 : 64 word_loc) LN) NONE
        (^s with <| stack := []; locals_size := NONE; handler := 9;
                    stack_max := SOME 1; permute := (\n i. i) |>))``;
val _ = print_eval "pop_env"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. (toAList t.locals, t.locals_size, t.handler, t.stack))
      (pop_env ^pushed)``;
val _ = print_eval "pop_env_empty" ``pop_env (^s with stack := []) = NONE``;
val _ = print_eval "jump_exc"
  ``OPTION_MAP (\(t:(64,'c,'ffi) wordSem$state, l1, l2).
                  (toAList t.locals, t.locals_size, t.handler, LENGTH t.stack, l1, l2))
      (jump_exc (^s with <| handler := 0;
         stack := [StackFrame NONE [] [] NONE;
                   StackFrame (SOME 4) [(2, Word 6w)] [(4, Loc 1 1)] (SOME (5, 7, 8))] |>))``;
val _ = print_eval "jump_exc_nohandler"
  ``jump_exc (^s with <| handler := 1;
       stack := [StackFrame NONE [] [] NONE; StackFrame (SOME 4) [] [] (SOME (5, 7, 8))] |>) = NONE``;
val _ = print_eval "jump_exc_range"
  ``jump_exc (^s with <| handler := 2; stack := [StackFrame NONE [] [] NONE] |>) = NONE``;
val env = ``insert 1 (Word 1w : 64 word_loc) (insert 2 (Loc 3 4) (insert 5 (Word 9w) LN))``;
val _ = print_eval "cut_names_hit" ``OPTION_MAP toAList (cut_names (insert 2 () (insert 5 () LN)) ^env)``;
val _ = print_eval "cut_names_miss" ``cut_names (insert 3 () LN) ^env``;
val _ = print_eval "cut_env_hit"
  ``OPTION_MAP toAList (cut_env (insert 1 () LN, insert 5 () LN) ^env)``;
val _ = print_eval "cut_env_miss" ``cut_env (insert 1 () LN, insert 6 () LN) ^env``;
val _ = print_eval "cut_state"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. toAList t.locals)
      (cut_state (insert 2 () LN, LN) (^s with locals := ^env))``;
val _ = print_eval "cut_state_opt_none"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. toAList t.locals)
      (cut_state_opt NONE (^s with locals := ^env))``;
