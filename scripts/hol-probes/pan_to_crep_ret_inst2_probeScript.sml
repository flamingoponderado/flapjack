(* Direct original-HOL EVAL fixture for the five premises of
   pan_to_crepProof$evaluate_shape_invariant_ret_inst2.  The source, target,
   context, argument list, code lookup, and body run are all concrete. *)
load "bossLib";
load "preamble";
load "pan_to_crepProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val target = ``(t:(8,unit) crepSem$state)``;
val source = ``((ARB:((8),unit) panSem$state) with <|
  memory := ^target.memory;
  memaddrs := ^target.memaddrs;
  sh_memaddrs := ^target.sh_memaddrs;
  locals := FEMPTY;
  structs := [];
  globals := FEMPTY;
  clock := ^target.clock;
  be := ^target.be;
  ffi := ^target.ffi;
  base_addr := ^target.base_addr;
  top_addr := ^target.top_addr|>)``;
val source_with_code = ``(^source with code := FEMPTY |+ (strlit "f",
  ([] : (mlstring # panLang$shape) list,
   panLang$Return (panLang$Const (7w:8 word)), panLang$One)))``;
val context = ``pan_to_crepProof$ctxt_fc FEMPTY FEMPTY [] [] []``;
val body = ``panLang$Return (panLang$Const (7w:8 word))``;
val emptyTargetLocals = ``(FEMPTY : num |-> (8) panSem$word_lab)``;

val _ = print_eval "ret_inst2_args"
  ``OPT_MMAP (panSem$eval ^source_with_code) []``;
val _ = print_eval "ret_inst2_lookup"
  ``panSem$lookup_code ^source_with_code.code (strlit "f") []``;
val _ = print_eval "ret_inst2_body_run"
  ``panSem$evaluate (^body,
    ((panSem$dec_clock ^source_with_code) with locals := FEMPTY))``;
val _ = print_eval "ret_inst2_state_rel"
  ``pan_to_crepProof$state_rel ^source_with_code ^target``;
val _ = print_eval "ret_inst2_locals_rel"
  ``pan_to_crepProof$locals_rel ^context ^source_with_code.locals
    ^emptyTargetLocals``;

val _ = print_eval "ret_inst2_five_premise_return"
  ``(OPT_MMAP (panSem$eval ^source_with_code) [] = SOME []) /\
    (panSem$lookup_code ^source_with_code.code (strlit "f") [] =
      SOME (^body, FEMPTY, panLang$One)) /\
    (panSem$evaluate (^body,
      ((panSem$dec_clock ^source_with_code) with locals := FEMPTY)) =
      (SOME (Return (ValWord (7w:8 word))),
       SND (panSem$evaluate (^body,
         ((panSem$dec_clock ^source_with_code) with locals := FEMPTY))))) /\
    pan_to_crepProof$state_rel ^source_with_code ^target /\
    pan_to_crepProof$locals_rel ^context ^source_with_code.locals
      ^emptyTargetLocals``;

val _ = print_eval "ret_inst2_return_result"
  ``FST (panSem$evaluate (^body,
    ((panSem$dec_clock ^source_with_code) with locals := FEMPTY)))``;
