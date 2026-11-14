(* Typed source declarations for word_bignum (task 148). *)
load "preamble";
load "word_bignumTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_bignumTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_bignum",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_bignum")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_bignum")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "compile_def_typed" "compile_def";
val _ = dt_label "mini_typed" "mini";
val _ = dt_label "address_typed" "address";
val _ = emit "TempIn1_def_typed" "TempIn1_def";
val _ = emit "TempIn2_def_typed" "TempIn2_def";
val _ = emit "TempOut_def_typed" "TempOut_def";
val _ = emit "div_location_def_typed" "div_location_def";
val _ = emit "SeqTemp_def_typed" "SeqTemp_def";
val _ = emit "SeqTempImm_def_typed" "SeqTempImm_def";
val _ = emit "SeqTempImmNot_def_typed" "SeqTempImmNot_def";
val _ = emit "SeqIndex_def_typed" "SeqIndex_def";
val _ = emit "DivCode_def_typed" "DivCode_def";
val _ = emit "LoadRegs_def_typed" "LoadRegs_def";
val _ = emit "SaveRegs_def_typed" "SaveRegs_def";
val _ = emit "compile_exp_def_typed" "compile_exp_def";
