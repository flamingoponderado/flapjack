(* Typed source declarations for targetSem (task 148). *)
load "preamble";
load "targetSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble targetSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="targetSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by targetSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of targetSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "apply_oracle_def_typed" "apply_oracle_def";
val _ = emit "encoded_bytes_in_mem_def_typed" "encoded_bytes_in_mem_def";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "read_ffi_bytearray_def_typed" "read_ffi_bytearray_def";
val _ = emit "read_ffi_bytearrays_def_typed" "read_ffi_bytearrays_def";
val _ = emit "good_init_state_def_typed" "good_init_state_def";
val _ = emit "start_pc_ok_def_typed" "start_pc_ok_def";
val _ = emit "ccache_interfer_ok_def_typed" "ccache_interfer_ok_def";
val _ = emit "ffi_interfer_ok_def_typed" "ffi_interfer_ok_def";
val _ = emit "code_loaded_def_typed" "code_loaded_def";
val _ = emit "get_reg_value_def_typed" "get_reg_value_def";
val _ = emit "target_configured_def_typed" "target_configured_def";
val _ = emit "machine_sem_def_typed" "machine_sem_def";
val _ = emit "is_valid_mapped_read_def_typed" "is_valid_mapped_read_def";
val _ = emit "is_valid_mapped_write_def_typed" "is_valid_mapped_write_def";
val _ = emit "mmio_pcs_min_index_def_typed" "mmio_pcs_min_index_def";
val _ = emit "post_ccache_asm_def_typed" "post_ccache_asm_def";
val _ = emit "post_ffi_asm_def_typed" "post_ffi_asm_def";
val _ = dt_label "machine_config_typed" "machine_config";
val _ = dt_label "machine_result_typed" "machine_result";
val _ = emit "installed_def_typed" "installed_def";
