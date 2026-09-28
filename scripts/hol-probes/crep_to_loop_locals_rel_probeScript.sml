(* Direct HOL observations for `crep_to_loopProofScript.sml` `locals_rel_def`
   (lines 101-111):
     locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab) t_locals <=>
       distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\
       domain l SUBSET domain t_locals /\
       !vname v. FLOOKUP s_locals vname = SOME v ==>
         ?n. FLOOKUP ctxt.vars vname = SOME n /\ n IN domain l /\
             lookup n t_locals = SOME (wlab_wloc v)

   HOL `crepLang$varname = num` (crepLangScript.sml:19), so `ctxt.vars` is a
   `num |-> num` finite map.  The relation is a universally quantified Prop, so
   the value rows below cannot be produced by `EVAL` alone: they are decided by
   kernel-checked proofs over a concrete context/locals pair (`prove` with a
   `rw`/`fs`/`EVAL_TAC` tactic).  `locals_rel_true` is proved; the two `_false`
   rows are proved as the negation, and the label prints the relation's truth
   value (`F`) only after that kernel proof succeeds. *)
load "bossLib";
load "preamble";
load "mlstringTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open mlstringTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* ctxt.vars : num |-> num, with 0 |-> 0; num_set l has member 0;
   num_map t maps 0 to a word_loc value.  These are the same concrete
   carriers as the Lean checks in `Flapjack.Test.CrepToLoopParity`. *)
val vars = ``((FEMPTY |+ (0:num, (0:num))) : (num, num) fmap)``;
val ctxt = ``(<| vars := ^vars;
                 funcs := (FEMPTY : (mlstring, num # num) fmap);
                 vmax := (0:num);
                 target := ARMv7 |>) : context``;
val l = ``(sptree$fromAList [(0:num,())] : sptree$num_set)``;
val tEmpty = ``(sptree$fromAList [] : 8 word_loc sptree$num_map)``;
val sl = ``((FEMPTY |+ (0:num, Word (9w:8 word))) : (num, 8 panSem$word_lab) fmap)``;
val t = ``(sptree$fromAList
             [(0:num, Word (9w:8 word))]
             : 8 word_loc sptree$num_map)``;
val tBad = ``(sptree$fromAList
                [(0:num, Word (12w:8 word))]
                : 8 word_loc sptree$num_map)``;

val _ = print_eval "ctxt_vars_lookup" (``FLOOKUP ^vars (0:num) = SOME 0``);
val _ = print_eval "distinct_component"
  (``case (FLOOKUP ^vars (0:num), FLOOKUP ^vars (0:num)) of
      | (SOME a, SOME b) => (a = b ==> ((0:num) = (0:num)))
      | _ => T``);
val _ = print_eval "ctxt_max_component"
  (``case FLOOKUP ^vars (0:num) of SOME m => m <= 0 | NONE => T``);
val _ = print_eval "set_domain_mem"
  (``sptree$lookup (0:num) ^l = SOME ()``);
val _ = print_eval "map_lookup"
  (``sptree$lookup (0:num) ^t = SOME (Word (9w:8 word))``);
val _ = print_eval "subset_domain_component"
  (``sptree$lookup (0:num) ^l = SOME () ==>
      sptree$lookup (0:num) ^t <> NONE``);

(* Direct decision of the whole relation at the concrete carrier instances. *)
val relation_tac =
  rw [crep_to_loopProofTheory.locals_rel_def,
      crep_to_loopProofTheory.distinct_vars_def,
      crep_to_loopProofTheory.ctxt_max_def]
  >> fs [sptreeTheory.domain_lookup, sptreeTheory.fromAList_def,
         sptreeTheory.lookup_def, FLOOKUP_UPDATE]
  >> EVAL_TAC;

fun print_relation label goal value =
  let
    val _ = prove(goal, relation_tac)
  in
    print (label ^ "=" ^ value ^ "\n")
  end
  handle _ => print (label ^ "=UNKNOWN\n");

val _ = print_relation "locals_rel_true"
  (``locals_rel ^ctxt ^l ^sl ^t``) "T";
val _ = print_relation "locals_rel_domain_false"
  (``~locals_rel ^ctxt ^l ^sl ^tEmpty``) "F";
val _ = print_relation "locals_rel_value_false"
  (``~locals_rel ^ctxt ^l ^sl ^tBad``) "F";