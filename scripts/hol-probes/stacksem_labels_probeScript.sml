(* Direct original HOL-EVAL observations for StackSem get_labels_def and
   loc_check_def. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;

val leaf = ``(LocValue 1 4 5 : 8 word stackLang$prog)``;
val left = ``(Call (SOME (^leaf, 13, 4, 5)) (INL 0) NONE : 8 word stackLang$prog)``;
val right = ``(Call (SOME (^leaf, 13, 7, 8)) (INL 0) NONE : 8 word stackLang$prog)``;
val loop_body = ``(Call (SOME (^leaf, 13, 9, 10)) (INL 0) NONE : 8 word stackLang$prog)``;
val nested = ``(Call (SOME (^leaf, 13, 16, 17)) (INL 0) NONE : 8 word stackLang$prog)``;
val _ = observe "locvalue_label"
  ``(4,5) IN stackSem$get_labels ^leaf``;
val _ = observe "seq_left"
  ``(4,5) IN stackSem$get_labels (Seq ^left ^right)``;
val _ = observe "seq_right"
  ``(7,8) IN stackSem$get_labels (Seq ^left ^right)``;
val _ = observe "if_right"
  ``(7,8) IN stackSem$get_labels (If Equal 0 (Imm 0w) ^left ^right)``;
val _ = observe "loop_body"
  ``(9,10) IN stackSem$get_labels (Loop ^loop_body)``;
val _ = observe "call_return_direct"
  ``(11,12) IN stackSem$get_labels
      (Call (SOME (^left, 13, 11, 12)) (INL 0) NONE)``;
val _ = observe "call_return_nested"
  ``(16,17) IN stackSem$get_labels
      (Call (SOME (^nested, 13, 11, 12)) (INL 0) NONE)``;
val _ = observe "call_handler_direct"
  ``(14,15) IN stackSem$get_labels
      (Call (SOME (^leaf, 13, 11, 12)) (INL 0) (SOME (^right, 14, 15)))``;
val _ = observe "call_handler_nested"
  ``(7,8) IN stackSem$get_labels
      (Call (SOME (^leaf, 13, 11, 12)) (INL 0) (SOME (^right, 14, 15)))``;
val _ = observe "call_empty"
  ``(1,2) IN stackSem$get_labels (Call NONE (INL 0) NONE)``;
val _ = observe "call_handler_without_return"
  ``(14,15) IN stackSem$get_labels (Call NONE (INL 0) (SOME (^right, 14, 15)))``;
val _ = observe "halt_empty"
  ``(1,2) IN stackSem$get_labels (Halt 0 : 8 word stackLang$prog)``;
val _ = observe "loccheck_zero_present"
  ``stackSem$loc_check (insert 3 ^left LN) (3,0)``;
val _ = observe "loccheck_zero_absent"
  ``stackSem$loc_check LN (3,0)``;
val _ = observe "loccheck_label_present"
  ``stackSem$loc_check (insert 3 ^left LN) (4,5)``;
val _ = observe "loccheck_label_absent"
  ``stackSem$loc_check (insert 3 ^left LN) (8,5)``;

(* The existential alternative needs an explicit code-tree witness; EVAL alone
   intentionally leaves the unbounded existential symbolic. *)
val _ = let
  val th = prove (``stackSem$loc_check (insert 3 ^left LN) (4,5)``,
    rw [stackSemTheory.loc_check_def] >>
    qexists_tac `3` >>
    qexists_tac `^left` >>
    simp [lookup_insert, stackSemTheory.get_labels_def])
in print "loccheck_label_witness=T\n" end;
