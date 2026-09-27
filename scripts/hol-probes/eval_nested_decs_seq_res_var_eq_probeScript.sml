(* Direct HOL observations for pan_to_crepProofScript.sml:596-620. *)

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

val state_absent =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)) |+ (2, Word (0w:64 word)));
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

val state_present =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)) |+ (1, Word (8w:64 word))
                            |+ (2, Word (0w:64 word)));
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

val _ = print_eval "nested_decs_restore_absent_local"
  ``case evaluate (nested_decs [0;1]
        [Const (10w:64 word);Const (20w:64 word)] (Assign 2 (Var 1)), ^state_absent) of
      (NONE, st) => FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) /\
        FLOOKUP st.locals 1 = NONE /\
        FLOOKUP st.locals 2 = SOME (Word (20w:64 word)) /\ st.clock = 5
    | _ => F``;

val _ = print_eval "nested_decs_restore_existing_local"
  ``case evaluate (nested_decs [0;1]
        [Const (10w:64 word);Const (20w:64 word)] (Assign 2 (Var 1)), ^state_present) of
      (NONE, st) => FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) /\
        FLOOKUP st.locals 1 = SOME (Word (8w:64 word)) /\
        FLOOKUP st.locals 2 = SOME (Word (20w:64 word)) /\ st.clock = 5
    | _ => F``;

val _ = print_eval "nested_decs_length_mismatch_skip"
  ``case evaluate (nested_decs [0;1] [Const (10w:64 word)]
        (Assign 2 (Var 0)), ^state_absent) of
      (NONE, st) => FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) /\
        FLOOKUP st.locals 1 = NONE /\
        FLOOKUP st.locals 2 = SOME (Word (0w:64 word)) /\ st.clock = 5
    | _ => F``;

val _ = print_eval "valid_declaration_premises"
  ``MAP (eval ^state_absent) [Const (10w:64 word);Const (20w:64 word)] =
      MAP SOME [Word (10w:64 word);Word (20w:64 word)] /\
    LENGTH ([0;1] : num list) = LENGTH [Const (10w:64 word);Const (20w:64 word)] /\
    distinct_lists [0;1] (FLAT (MAP var_cexp [Const (10w:64 word);Const (20w:64 word)])) /\
    ALL_DISTINCT ([0;1] : num list)``;

val _ = print_eval "duplicate_names_rejected"
  ``ALL_DISTINCT ([0;0] : num list)``;

val _ = print_eval "expression_interference_rejected"
  ``distinct_lists [0] (FLAT (MAP var_cexp [Var 0]))``;

val _ = print_eval "length_premise_rejected"
  ``LENGTH ([0;1] : num list) = LENGTH [Const (10w:64 word)]``;
