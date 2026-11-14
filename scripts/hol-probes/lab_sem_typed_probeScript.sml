(* Typed source declarations for labSem (task 148). *)
load "preamble";
load "labSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble labSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="labSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by labSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of labSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "arith_upd_def_typed" "arith_upd_def";
val _ = emit "binop_upd_def_typed" "binop_upd_def";
val _ = emit "is_Label_def_typed" "is_Label_def";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "fp_upd_def_typed" "fp_upd_def";
val _ = emit "asm_inst_def_typed" "asm_inst_def";
val _ = emit "asm_inst_consts_typed" "asm_inst_consts";
val _ = emit "addr_def_typed" "addr_def";
val _ = emit "mem_load_def_typed" "mem_load_def";
val _ = emit "mem_load32_def_typed" "mem_load32_def";
val _ = emit "mem_load_byte_def_typed" "mem_load_byte_def";
val _ = emit "mem_op_def_typed" "mem_op_def";
val _ = emit "mem_store_def_typed" "mem_store_def";
val _ = emit "mem_store32_def_typed" "mem_store32_def";
val _ = emit "mem_store_byte_def_typed" "mem_store_byte_def";
val _ = emit "asm_code_length_def_typed" "asm_code_length_def";
val _ = emit "asm_fetch_def_typed" "asm_fetch_def";
val _ = emit "asm_fetch_aux_def_typed" "asm_fetch_aux_def";
val _ = emit "get_lab_after_def_typed" "get_lab_after_def";
val _ = emit "get_pc_value_def_typed" "get_pc_value_def";
val _ = emit "get_ret_Loc_def_typed" "get_ret_Loc_def";
val _ = emit "lab_to_loc_def_typed" "lab_to_loc_def";
val _ = emit "loc_to_pc_def_typed" "loc_to_pc_def";
val _ = emit "next_label_def_typed" "next_label_def";
val _ = emit "semantics_def_typed" "semantics_def";
val _ = emit "share_mem_load_def_typed" "share_mem_load_def";
val _ = emit "share_mem_op_def_typed" "share_mem_op_def";
val _ = emit "share_mem_store_def_typed" "share_mem_store_def";
val _ = dt_label "state_typed" "state";
val _ = dt_label "word8_loc_typed" "word8_loc";
val _ = emit "assert_def_typed" "assert_def";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "inc_pc_def_typed" "inc_pc_def";
val _ = emit "read_fp_reg_def_typed" "read_fp_reg_def";
val _ = emit "reg_imm_def_typed" "reg_imm_def";
val _ = emit "upd_fp_reg_def_typed" "upd_fp_reg_def";
val _ = emit "upd_mem_def_typed" "upd_mem_def";
val _ = emit "upd_pc_def_typed" "upd_pc_def";
val _ = emit "upd_reg_def_typed" "upd_reg_def";
