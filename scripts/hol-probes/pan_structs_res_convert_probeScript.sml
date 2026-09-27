(* Direct HOL-EVAL observations for pan_structsProof$convert_res,
   pan_structsProof$is_cont_res and pan_structsProof$res_vs.
   References: cakeml/pancake/proofs/pan_structsProofScript.sml:992-1009
   (is_cont_res_def, is_cont_res_eq_disj, convert_res_def) and :1028-1031
   (res_vs_def).  The paired Lean replay is
   Flapjack/Test/PanStructsResConvertParity.lean. *)
load "bossLib";
load "preamble";
load "panSemTheory";
load "pan_structsTheory";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;
open pan_structsProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* convert_res: the Break clause, the two recursive clauses (with the
   nontrivial convert_v payload), and the four catch-all constructors. *)
val _ = print_eval "convert_res_break"
  ``pan_structsProof$convert_res (SOME Break)``;
val _ = print_eval "convert_res_return_val"
  ``pan_structsProof$convert_res (SOME (Return (ValWord 7w)))``;
val _ = print_eval "convert_res_exception"
  ``pan_structsProof$convert_res
      (SOME (Exception (strlit "e") (ValWord 5w)))``;
val _ = print_eval "convert_res_none"
  ``pan_structsProof$convert_res NONE``;
val _ = print_eval "convert_res_error"
  ``pan_structsProof$convert_res (SOME Error)``;
val _ = print_eval "convert_res_timeout"
  ``pan_structsProof$convert_res (SOME TimeOut)``;
val _ = print_eval "convert_res_continue"
  ``pan_structsProof$convert_res (SOME Continue)``;
val _ = print_eval "convert_res_final_ffi"
  ``pan_structsProof$convert_res
      (SOME (FinalFFI (Final_event (ExtCall (strlit "x")) [] [] FFI_failed)))``;

(* is_cont_res: the three true clauses and three non-cont clauses. *)
val _ = print_eval "is_cont_res_none"
  ``pan_structsProof$is_cont_res NONE``;
val _ = print_eval "is_cont_res_break"
  ``pan_structsProof$is_cont_res (SOME Break)``;
val _ = print_eval "is_cont_res_continue"
  ``pan_structsProof$is_cont_res (SOME Continue)``;
val _ = print_eval "is_cont_res_error"
  ``pan_structsProof$is_cont_res (SOME Error)``;
val _ = print_eval "is_cont_res_timeout"
  ``pan_structsProof$is_cont_res (SOME TimeOut)``;
val _ = print_eval "is_cont_res_return"
  ``pan_structsProof$is_cont_res (SOME (Return (ValWord 1w)))``;

(* res_vs: the two payload-extracting clauses and the catch-alls. *)
val _ = print_eval "res_vs_return"
  ``pan_structsProof$res_vs (SOME (Return (ValWord 7w)))``;
val _ = print_eval "res_vs_exception"
  ``pan_structsProof$res_vs (SOME (Exception (strlit "e") (ValWord 5w)))``;
val _ = print_eval "res_vs_break"
  ``pan_structsProof$res_vs (SOME Break)``;
val _ = print_eval "res_vs_none"
  ``pan_structsProof$res_vs NONE``;
val _ = print_eval "res_vs_continue"
  ``pan_structsProof$res_vs (SOME Continue)``;
