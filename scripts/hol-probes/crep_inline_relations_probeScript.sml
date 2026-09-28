(* Direct HOL-EVAL rows for `state_rel_def` and `locals_rel_def` in
   crep_inlineProofScript.sml:12-29. These rows distinguish finite-map
   SUBMAP from equality and check that state_rel deliberately ignores locals. *)

load "bossLib";
load "preamble";
load "crep_inlineProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_inlineProofTheory;
open crepSemTheory;

fun print_eval label q =
  let val th = SIMP_CONV (srw_ss())
    [state_rel_def, locals_rel_def, SUBMAP_DEF, FDOM_FEMPTY, FDOM_FUPDATE,
     FAPPLY_FUPDATE_THM, IN_INSERT, NOT_IN_EMPTY] q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val left = ``FEMPTY |+ (1:num, Word (7w:64 word))``;
val extended = ``^left |+ (2:num, Word (9w:64 word))``;
val missing = ``FEMPTY |+ (2:num, Word (9w:64 word))``;
val conflict = ``FEMPTY |+ (1:num, Word (8w:64 word))``;
val no_code = ``FEMPTY : (funname, num list # 64 crepLang$prog) fmap``;
val other_code = ``(FEMPTY |+ («f», ([], Skip : 64 crepLang$prog))):
  (funname, num list # 64 crepLang$prog) fmap``;

fun mkState locals code =
  ``(<| locals := ^locals;
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

val stateLeft = mkState left no_code;
val stateExtended = mkState extended no_code;
val stateDifferentCode = mkState extended other_code;

val _ = print_eval "locals_rel_extension" ``locals_rel ^stateLeft ^stateExtended``;
val _ = print_eval "locals_rel_missing_key" ``locals_rel ^stateLeft ^(mkState missing no_code)``;
val _ = print_eval "locals_rel_conflicting_value" ``locals_rel ^stateLeft ^(mkState conflict no_code)``;
val _ = print_eval "state_rel_ignores_locals" ``state_rel ^stateLeft ^stateExtended``;
val _ = print_eval "state_rel_checks_code" ``state_rel ^stateLeft ^stateDifferentCode``;

val _ = OS.Process.exit OS.Process.success;
