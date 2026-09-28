(* Direct HOL EVAL cases for the crepSem evaluate_def Primitive clause and the
   Call exception-handler branch (crepSemScript.sml:248-259, 335-366), used by
   Flapjack.Test.CrepSemEvaluateDefArmsParity against the exact evaluator. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

fun mkState code =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)) |+ (1, Word (3w:64 word))
                          |+ (2, Word (1w:64 word)));
        globals := FEMPTY;
        code := ^code;
        memory := K (Word (0w:64 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;

val emptyCode = ``FEMPTY : (funname, num list # 64 crepLang$prog) fmap``;
val raiseCode =
  ``alist_to_fmap
      [(«worker», ([], (Raise (3w:64 word) : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val s = mkState emptyCode;
val r = mkState raiseCode;

val _ = print_eval "primitive_add_carry"
  ``case evaluate ((Primitive [0;1] AddCarry [0;1;2] : 64 crepLang$prog), ^s) of
      (NONE, st) => FLOOKUP st.locals 0 = SOME (Word (11w:64 word)) /\
        FLOOKUP st.locals 1 = SOME (Word (0w:64 word)) /\
        FLOOKUP st.locals 2 = SOME (Word (1w:64 word)) /\ st.clock = 5
    | _ => F``;
val _ = print_eval "primitive_duplicate_lhs"
  ``case evaluate ((Primitive [0;0] AddCarry [0;1;2] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st = ^s | _ => F``;
val _ = print_eval "primitive_missing_lhs"
  ``case evaluate ((Primitive [0;9] AddCarry [0;1;2] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st = ^s | _ => F``;
val _ = print_eval "primitive_wrong_arity"
  ``case evaluate ((Primitive [0;1] AddCarry [0;1] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st = ^s | _ => F``;
val _ = print_eval "primitive_missing_rhs"
  ``case evaluate ((Primitive [0;1] AddCarry [0;1;9] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st = ^s | _ => F``;

val _ = print_eval "call_handler_catch"
  ``case evaluate ((Call (SOME ([1], SOME (3w, Assign 1 (Const 5w)))) «worker» []
                     : 64 crepLang$prog), ^r) of
      (NONE, st) => FLOOKUP st.locals 1 = SOME (Word (5w:64 word)) /\
        FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) /\ st.clock = 4
    | _ => F``;
val _ = print_eval "call_handler_mismatch"
  ``case evaluate ((Call (SOME ([1], SOME (4w, Assign 1 (Const 5w)))) «worker» []
                     : 64 crepLang$prog), ^r) of
      (SOME (Exception (3w:64 word)), st) => st.locals = FEMPTY /\ st.clock = 4
    | _ => F``;
val _ = print_eval "call_handler_absent"
  ``case evaluate ((Call (SOME ([1], NONE)) «worker» [] : 64 crepLang$prog), ^r) of
      (SOME (Exception (3w:64 word)), st) => st.locals = FEMPTY /\ st.clock = 4
    | _ => F``;
val _ = print_eval "call_handler_duplicate_rts"
  ``case evaluate ((Call (SOME ([1;1], SOME (3w, Skip))) «worker» []
                     : 64 crepLang$prog), ^r) of
      (SOME Error, st) => st = ^r | _ => F``;
