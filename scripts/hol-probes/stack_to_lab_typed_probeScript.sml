(* Typed source declarations for stack_to_lab (task 148). *)
load "preamble";
load "stack_to_labTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_to_labTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_to_lab",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_to_lab")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_to_lab")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "config_typed" "config";
val _ = emit "compile_def_typed" "compile_def";
val _ = emit "compile_no_stubs_def_typed" "compile_no_stubs_def";
val _ = emit "is_gen_gc_def_typed" "is_gen_gc_def";
val _ = emit "compile_jump_def_typed" "compile_jump_def";
val _ = emit "find_lab_def_typed" "find_lab_def";
val _ = emit "flatten_def_typed" "flatten_def";
val _ = emit "is_Seq_def_typed" "is_Seq_def";
val _ = emit "negate_def_typed" "negate_def";
val _ = emit "prog_to_section_def_typed" "prog_to_section_def";
