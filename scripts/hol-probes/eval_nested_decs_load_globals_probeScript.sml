(* Direct HOL-EVAL cases for
   pan_to_crepProof$evaluate_nested_decs_load_globals.
   Source: pan_to_crepProofScript.sml:4139-4176. *)
load "bossLib";
load "preamble";
load "pan_to_crepProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val wordState =
  ``(<| locals := FEMPTY |+ (0, Word (9w : 8 word));
        globals := FEMPTY |+ (0w : 5 word, Word (7w : 8 word));
        code := FEMPTY;
        memory := K (Word (0w : 8 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w : 8 word);
        top_addr := (100w : 8 word) |> : (8, unit) crepSem$state)``;

val _ = print_eval "word_lookup_and_nested_decs_theorem"
  ``let s = ^wordState;
        rv = (ValWord (7w : 8 word));
        vs = ([0] : num list);
        p = (Return [Var 0] : 8 crepLang$prog);
        rvs = [Word (7w : 8 word)]
    in pan_to_crepProof$globals_lookup s rv = SOME rvs /\
       size_of_shape (shape_of rv) <= 32 /\ ALL_DISTINCT vs /\
       LENGTH vs = size_of_shape (shape_of rv) /\
       let (res,s') = crepSem$evaluate
         (crepLang$nested_decs vs
           (crepLang$load_globals (0w : 5 word) (size_of_shape (shape_of rv))) p,
          s)
       in (res, FLOOKUP s'.locals 0) =
          (SOME (Return [Word (7w : 8 word)]), SOME (Word (9w : 8 word)))``;

val structState =
  ``(<| locals := FEMPTY |+ (5, Word (99w : 8 word));
        globals := FEMPTY |+ (0w : 5 word, Word (3w : 8 word))
                    |+ (1w : 5 word, Word (4w : 8 word));
        code := FEMPTY;
        memory := K (Word (0w : 8 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 7;
        be := F;
        ffi := ARB;
        base_addr := (0w : 8 word);
        top_addr := (100w : 8 word) |> : (8, unit) crepSem$state)``;

val _ = print_eval "struct_lookup_and_nested_decs_theorem"
  ``let s = ^structState;
        rv = (RStruct [ValWord (3w : 8 word); ValWord (4w : 8 word)]);
        vs = ([5;6] : num list);
        p = (Return [Var 5; Var 6] : 8 crepLang$prog);
        rvs = [Word (3w : 8 word); Word (4w : 8 word)]
    in pan_to_crepProof$globals_lookup s rv = SOME rvs /\
       size_of_shape (shape_of rv) <= 32 /\ ALL_DISTINCT vs /\
       LENGTH vs = size_of_shape (shape_of rv) /\
       let (res,s') = crepSem$evaluate
         (crepLang$nested_decs vs
           (crepLang$load_globals (0w : 5 word) (size_of_shape (shape_of rv))) p,
          s)
       in (res, FLOOKUP s'.locals 5, FLOOKUP s'.locals 6) =
          (SOME (Return [Word (3w : 8 word); Word (4w : 8 word)]),
           SOME (Word (99w : 8 word)), NONE)``;
