(* Typed source declarations for ast (task 148). *)
load "preamble";
load "astTheory";
open HolKernel Parse boolLib bossLib;
open preamble astTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="ast",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by ast")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of ast")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "opb_typed" "opb";
val _ = dt_label "shift_typed" "shift";
val _ = dt_label "test_typed" "test";
val _ = dt_label "thunk_mode_typed" "thunk_mode";
val _ = dt_label "thunk_op_typed" "thunk_op";
val _ = dt_label "word_size_typed" "word_size";
val _ = dt_label "lit_typed" "lit";
val _ = dt_label "arith_typed" "arith";
val _ = dt_label "prim_type_typed" "prim_type";
val _ = dt_label "op_typed" "op";
val _ = dt_label "op_class_typed" "op_class";
val _ = emit "getOpClass_def_typed" "getOpClass_def";
val _ = dt_label "lop_typed" "lop";
val _ = dt_label "ast_t_typed" "ast_t";
val _ = dt_label "pat_typed" "pat";
val _ = dt_label "exp_typed" "exp";
val _ = dt_label "dec_typed" "dec";
val _ = emit "pat_bindings_def_typed" "pat_bindings_def";
val _ = emit "every_exp_def_typed" "every_exp_def";
