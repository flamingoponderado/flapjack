(* Direct HOL observations for pan_to_crepProofScript.sml:540-575. *)

load "bossLib";
load "preamble";
load "crepSemTheory";
load "pan_to_crepProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;
open pan_to_crepProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val s =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)) |+ (1, Word (8w:64 word)));
        globals := FEMPTY;
        code := FEMPTY;
        memory := K (Word (0w:64 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;

val _ = print_eval "assign_list_success"
  ``case evaluate (nested_seq (MAP2 Assign [0;1]
        [Const (10w:64 word);Const (20w:64 word)]), ^s) of
      (NONE, st) => FLOOKUP st.locals 0 = SOME (Word (10w:64 word)) /\
        FLOOKUP st.locals 1 = SOME (Word (20w:64 word)) /\ st.clock = 5
    | _ => F``;
val _ = print_eval "duplicate_names_all_distinct"
  ``ALL_DISTINCT ([0;0] : num list)``;
val _ = print_eval "expression_interference_distinct_lists"
  ``distinct_lists ([0] : num list) (FLAT (MAP var_cexp [Var 0]))``;
