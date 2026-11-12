(* Typed source declarations for asmSem (task 148). *)
load "preamble";
load "asmSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble asmSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="asmSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by asmSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of asmSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "word_shift_def_typed" "word_shift_def";
val _ = emit "arith_upd_def_typed" "arith_upd_def";
val _ = emit "assert_def_typed" "assert_def";
val _ = emit "binop_upd_def_typed" "binop_upd_def";
val _ = emit "is_test_def_typed" "is_test_def";
val _ = emit "read_fp_reg_def_typed" "read_fp_reg_def";
val _ = emit "read_mem_def_typed" "read_mem_def";
val _ = emit "read_reg_def_typed" "read_reg_def";
val _ = emit "reg_imm_def_typed" "reg_imm_def";
val _ = emit "upd_fp_reg_def_typed" "upd_fp_reg_def";
val _ = emit "upd_mem_def_typed" "upd_mem_def";
val _ = emit "upd_pc_def_typed" "upd_pc_def";
val _ = emit "upd_reg_def_typed" "upd_reg_def";
val _ = emit "fp_upd_def_typed" "fp_upd_def";
val _ = emit "mem_load_def_typed" "mem_load_def";
val _ = emit "mem_op_def_typed" "mem_op_def";
val _ = emit "mem_store_def_typed" "mem_store_def";
val _ = emit "addr_def_typed" "addr_def";
val _ = emit "read_mem_word_def_typed" "read_mem_word_def";
val _ = emit "write_mem_word_def_typed" "write_mem_word_def";
val _ = dt_label "asm_state_typed" "asm_state";
val _ = emit "asm_step_def_typed" "asm_step_def";
val _ = emit "asm_def_typed" "asm_def";
val _ = emit "inst_def_typed" "inst_def";
val _ = emit "jump_to_offset_def_typed" "jump_to_offset_def";
