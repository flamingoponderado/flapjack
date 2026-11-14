(* Typed source declarations for wordLang (task 148). *)
load "preamble";
load "wordLangTheory";
open HolKernel Parse boolLib bossLib;
open preamble wordLangTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="wordLang",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by wordLang")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of wordLang")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "exp_typed" "exp";
val _ = dt_label "prog_typed" "prog";
val _ = dt_label "word_loc_typed" "word_loc";
val _ = emit "every_var_exp_def_typed" "every_var_exp_def";
val _ = emit "every_var_imm_def_typed" "every_var_imm_def";
val _ = emit "every_var_inst_def_typed" "every_var_inst_def";
val _ = emit "exp_to_addr_def_typed" "exp_to_addr_def";
val _ = emit "raise_stub_location_def_typed" "raise_stub_location_def";
val _ = emit "store_consts_stub_location_def_typed" "store_consts_stub_location_def";
val _ = emit "word_op_def_typed" "word_op_def";
val _ = emit "word_sh_def_typed" "word_sh_def";
val _ = emit "cutsets_max_def_typed" "cutsets_max_def";
val _ = emit "max_var_def_typed" "max_var_def";
val _ = emit "max_var_exp_def_typed" "max_var_exp_def";
val _ = emit "max_var_inst_def_typed" "max_var_inst_def";
val _ = emit "every_name_def_typed" "every_name_def";
val _ = emit "every_stack_var_def_typed" "every_stack_var_def";
val _ = emit "every_var_def_typed" "every_var_def";
