(* Direct HOL-EVAL rows for state_rel's exact source carrier clauses. *)
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

val target = ``(t:(8,unit) crepSem$state)``;
val source = ``(s:(8,unit) panSem$state)``;
val related_source = ``(^source with <|
  memory := ^target.memory;
  memaddrs := ^target.memaddrs;
  sh_memaddrs := ^target.sh_memaddrs;
  structs := [];
  globals := FEMPTY;
  clock := ^target.clock;
  be := ^target.be;
  ffi := ^target.ffi;
  base_addr := ^target.base_addr;
  top_addr := ^target.top_addr|>)``;
val named_structs = ``[(strlit "Pair",
  <|fields := [(strlit "left", panLang$One)]; size := 1|>)]``;
val nonempty_struct_source = ``(^related_source with structs := ^named_structs)``;
val nonempty_globals_source = ``(^related_source with globals :=
  FEMPTY |+ (strlit "global", ValWord (3w:8 word)))``;

val _ = print_eval "state_rel_matching_fields"
  ``pan_to_crepProof$state_rel ^related_source ^target``;
val _ = print_eval "state_rel_rejects_nonempty_structs"
  ``pan_to_crepProof$state_rel ^nonempty_struct_source ^target``;
val _ = print_eval "state_rel_globals_equation_unreduced"
  ``pan_to_crepProof$state_rel ^nonempty_globals_source ^target``;
val _ = print_eval "state_rel_nonempty_globals_lookup"
  ``FLOOKUP (^nonempty_globals_source).globals (strlit "global") =
    SOME (ValWord (3w:8 word))``;
val _ = print_eval "state_rel_empty_globals_lookup"
  ``FLOOKUP (^related_source).globals (strlit "global") = NONE``;
val _ = print_eval "state_rel_named_struct_carrier"
  ``^named_structs = [(strlit "Pair",
    <|fields := [(strlit "left", panLang$One)]; size := 1|>)]``;
val _ = print_eval "state_rel_carrier_probe_done" ``0``;
