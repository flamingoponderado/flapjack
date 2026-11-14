(* Typed source declarations for arm8_target (task 148). *)
load "preamble";
load "arm8_targetTheory";
open HolKernel Parse boolLib bossLib;
open preamble arm8_targetTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="arm8_target",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by arm8_target")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of arm8_target")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "arm8_shv_def_typed" "arm8_shv_def";
val _ = emit "arm8_proj_def_typed" "arm8_proj_def";
val _ = emit "arm8_ok_def_typed" "arm8_ok_def";
val _ = emit "arm8_next_def_typed" "arm8_next_def";
val _ = emit "arm8_encode_fail_def_typed" "arm8_encode_fail_def";
val _ = emit "arm8_encode_def_typed" "arm8_encode_def";
val _ = emit "arm8_enc_mov_imm_def_typed" "arm8_enc_mov_imm_def";
val _ = emit "cmp_cond_def_typed" "cmp_cond_def";
val _ = emit "arm8_load_store_ast_def_typed" "arm8_load_store_ast_def";
val _ = emit "arm8_load_store_ast32_def_typed" "arm8_load_store_ast32_def";
val _ = emit "arm8_load_store_ast16_def_typed" "arm8_load_store_ast16_def";
val _ = emit "arm8_ast_def_typed" "arm8_ast_def";
val _ = emit "arm8_enc_def_typed" "arm8_enc_def";
val _ = emit "valid_immediate_def_typed" "valid_immediate_def";
val _ = emit "arm8_config_def_typed" "arm8_config_def";
val _ = emit "arm8_target_def_typed" "arm8_target_def";
