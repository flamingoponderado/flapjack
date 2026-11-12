(* Typed source declarations for stack_alloc (task 148). *)
load "preamble";
load "stack_allocTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_allocTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_alloc",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_alloc")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_alloc")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "comp_def_typed" "comp_def";
val _ = emit "compile_def_typed" "compile_def";
val _ = emit "next_lab_def_typed" "next_lab_def";
val _ = emit "prog_comp_def_typed" "prog_comp_def";
val _ = emit "stubs_def_typed" "stubs_def";
val _ = emit "clear_top_inst_def_typed" "clear_top_inst_def";
val _ = emit "memcpy_code_def_typed" "memcpy_code_def";
val _ = emit "SetNewTrigger_def_typed" "SetNewTrigger_def";
val _ = emit "word_gc_code_def_typed" "word_gc_code_def";
val _ = emit "word_gc_move_bitmap_code_def_typed" "word_gc_move_bitmap_code_def";
val _ = emit "word_gc_move_bitmaps_code_def_typed" "word_gc_move_bitmaps_code_def";
val _ = emit "word_gc_move_code_def_typed" "word_gc_move_code_def";
val _ = emit "word_gc_move_list_code_def_typed" "word_gc_move_list_code_def";
val _ = emit "word_gc_move_loop_code_def_typed" "word_gc_move_loop_code_def";
val _ = emit "word_gc_move_roots_bitmaps_code_def_typed" "word_gc_move_roots_bitmaps_code_def";
val _ = emit "word_gc_partial_or_full_def_typed" "word_gc_partial_or_full_def";
val _ = emit "word_gen_gc_move_bitmap_code_def_typed" "word_gen_gc_move_bitmap_code_def";
val _ = emit "word_gen_gc_move_bitmaps_code_def_typed" "word_gen_gc_move_bitmaps_code_def";
val _ = emit "word_gen_gc_move_code_def_typed" "word_gen_gc_move_code_def";
val _ = emit "word_gen_gc_move_data_code_def_typed" "word_gen_gc_move_data_code_def";
val _ = emit "word_gen_gc_move_list_code_def_typed" "word_gen_gc_move_list_code_def";
val _ = emit "word_gen_gc_move_loop_code_def_typed" "word_gen_gc_move_loop_code_def";
val _ = emit "word_gen_gc_move_refs_code_def_typed" "word_gen_gc_move_refs_code_def";
val _ = emit "word_gen_gc_move_roots_bitmaps_code_def_typed" "word_gen_gc_move_roots_bitmaps_code_def";
val _ = emit "word_gen_gc_partial_move_bitmap_code_def_typed" "word_gen_gc_partial_move_bitmap_code_def";
val _ = emit "word_gen_gc_partial_move_bitmaps_code_def_typed" "word_gen_gc_partial_move_bitmaps_code_def";
val _ = emit "word_gen_gc_partial_move_code_def_typed" "word_gen_gc_partial_move_code_def";
val _ = emit "word_gen_gc_partial_move_data_code_def_typed" "word_gen_gc_partial_move_data_code_def";
val _ = emit "word_gen_gc_partial_move_list_code_def_typed" "word_gen_gc_partial_move_list_code_def";
val _ = emit "word_gen_gc_partial_move_ref_list_code_def_typed" "word_gen_gc_partial_move_ref_list_code_def";
val _ = emit "word_gen_gc_partial_move_roots_bitmaps_code_def_typed" "word_gen_gc_partial_move_roots_bitmaps_code_def";
val _ = emit "stub_names_def_typed" "stub_names_def";
