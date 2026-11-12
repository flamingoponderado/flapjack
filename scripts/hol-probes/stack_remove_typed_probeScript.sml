(* Typed source declarations for stack_remove (task 148). *)
load "preamble";
load "stack_removeTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_removeTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_remove",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_remove")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_remove")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "halt_inst_def_typed" "halt_inst_def";
val _ = emit "max_stack_alloc_def_typed" "max_stack_alloc_def";
val _ = emit "stack_err_lab_def_typed" "stack_err_lab_def";
val _ = emit "store_length_def_typed" "store_length_def";
val _ = emit "store_list_def_typed" "store_list_def";
val _ = emit "word_offset_def_typed" "word_offset_def";
val _ = emit "comp_def_typed" "comp_def";
val _ = emit "compile_def_typed" "compile_def";
val _ = emit "copy_each_def_typed" "copy_each_def";
val _ = emit "copy_loop_def_typed" "copy_loop_def";
val _ = emit "init_code_def_typed" "init_code_def";
val _ = emit "init_memory_def_typed" "init_memory_def";
val _ = emit "init_stubs_def_typed" "init_stubs_def";
val _ = emit "prog_comp_def_typed" "prog_comp_def";
val _ = emit "downshift_def_typed" "downshift_def";
val _ = emit "stack_load_def_typed" "stack_load_def";
val _ = emit "stack_store_def_typed" "stack_store_def";
val _ = emit "upshift_def_typed" "upshift_def";
val _ = emit "single_stack_alloc_def_typed" "single_stack_alloc_def";
val _ = emit "stack_alloc_def_typed" "stack_alloc_def";
val _ = emit "single_stack_free_def_typed" "single_stack_free_def";
val _ = emit "stack_free_def_typed" "stack_free_def";
val _ = emit "store_offset_def_typed" "store_offset_def";
val _ = emit "store_pos_def_typed" "store_pos_def";
val _ = emit "store_init_def_typed" "store_init_def";
val _ = emit "store_list_code_def_typed" "store_list_code_def";
val _ = emit "check_init_stubs_length_typed" "check_init_stubs_length";
val _ = emit "stub_names_def_typed" "stub_names_def";
