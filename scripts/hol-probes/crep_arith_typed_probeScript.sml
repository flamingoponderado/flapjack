(* Typed source declarations for crep_arith (task 148). *)
load "preamble";
load "crep_arithTheory";
open HolKernel Parse boolLib bossLib;
open preamble crep_arithTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="crep_arith",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by crep_arith")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of crep_arith")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "dest_2exp_def_typed" "dest_2exp_def";
val _ = emit "dest_2exp_thm_typed" "dest_2exp_thm";
val _ = emit "dest_const_def_typed" "dest_const_def";
val _ = emit "mul_const_def_typed" "mul_const_def";
val _ = emit "simp_exp_def_typed" "simp_exp_def";
val _ = emit "simp_prog_def_typed" "simp_prog_def";

(* dest_2exp_lemma is [local]; capture its typed statement. *)
val dest_2exp_lemma_statement =
  ``∀(i :num) (w :'a word) (n :num).
      dest_2exp i w = SOME n ⇒ i ≤ n ∧ w = word_lsl (1w :'a word) (n − i)``;
val _ = (print "dest_2exp_lemma_typed="; print_term dest_2exp_lemma_statement; print "\n");
