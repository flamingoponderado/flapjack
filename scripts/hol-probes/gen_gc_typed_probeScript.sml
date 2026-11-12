(* Typed source declarations for gen_gc (task 148). *)
load "preamble";
load "gen_gcTheory";
open HolKernel Parse boolLib bossLib;
open preamble gen_gcTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="gen_gc",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by gen_gc")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of gen_gc")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "is_final_def_typed" "is_final_def";
val _ = emit "heap_lookup_APPEND_typed" "heap_lookup_APPEND";
val _ = emit "gc_move_list_length_typed" "gc_move_list_length";
val _ = emit "gen_gc_LENGTH_typed" "gen_gc_LENGTH";
val _ = emit "gc_move_loop_ok_typed" "gc_move_loop_ok";
val _ = emit "gc_move_refs_ok_typed" "gc_move_refs_ok";
val _ = emit "gc_move_data_ok_typed" "gc_move_data_ok";
val _ = emit "gc_move_data_h2_typed" "gc_move_data_h2";
val _ = emit "gc_move_ok_typed" "gc_move_ok";
val _ = emit "gc_move_list_ok_typed" "gc_move_list_ok";
val _ = dt_label "gen_gc_conf_typed" "gen_gc_conf";
val _ = emit "gc_move_def_typed" "gc_move_def";
val _ = emit "gc_move_list_def_typed" "gc_move_list_def";
val _ = emit "gc_move_data_def_typed" "gc_move_data_def";
val _ = emit "gc_move_refs_def_typed" "gc_move_refs_def";
val _ = emit "gc_move_loop_def_typed" "gc_move_loop_def";
val _ = emit "gen_gc_def_typed" "gen_gc_def";
val _ = emit "heap_lookup_IMP_heap_addresses_typed" "heap_lookup_IMP_heap_addresses";
