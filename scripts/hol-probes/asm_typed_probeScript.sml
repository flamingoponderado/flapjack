(* Typed source declarations for asm (task 148). *)
load "preamble";
load "asmTheory";
open HolKernel Parse boolLib bossLib;
open preamble asmTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="asm",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by asm")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of asm")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "architecture_typed" "architecture";
val _ = dt_label "asm_config_typed" "asm_config";
val _ = dt_label "addr_typed" "addr";
val _ = dt_label "arith_typed" "arith";
val _ = dt_label "asm_typed" "asm";
val _ = dt_label "binop_typed" "binop";
val _ = dt_label "cmp_typed" "cmp";
val _ = dt_label "fp_typed" "fp";
val _ = dt_label "inst_typed" "inst";
val _ = dt_label "memop_typed" "memop";
val _ = dt_label "reg_imm_typed" "reg_imm";
val _ = emit "arith_ok_def_typed" "arith_ok_def";
val _ = emit "cmp_ok_def_typed" "cmp_ok_def";
val _ = emit "fp_ok_def_typed" "fp_ok_def";
val _ = emit "fp_reg_ok_def_typed" "fp_reg_ok_def";
val _ = emit "inst_ok_def_typed" "inst_ok_def";
val _ = emit "is_load_def_typed" "is_load_def";
val _ = emit "offset_ok_def_typed" "offset_ok_def";
val _ = emit "asm_ok_def_typed" "asm_ok_def";
val _ = emit "reg_imm_ok_def_typed" "reg_imm_ok_def";
val _ = emit "reg_ok_def_typed" "reg_ok_def";
val _ = emit "word_cmp_def_typed" "word_cmp_def";
