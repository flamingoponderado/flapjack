load "bossLib";
load "preamble";
load "loop_liveProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loop_liveProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print_term (rconc th); print "\n"
  end;

(* Direct original-HOL rows for `domain_list_delete`
   (cakeml/pancake/proofs/loop_liveProofScript.sml:561-562):

     domain (list_delete vs s) = domain s DIFF set vs

   observed pointwise on `IN domain _`, which is what the Lean port
   `sptDomain_sptListDelete` renders. *)
val t = ``fromAList [(0:num,());(1:num,());(2:num,());(3:num,())] : unit num_map``;
print_eval "dld_kept" ``1 IN domain (list_delete [3] ^t)``;
print_eval "dld_deleted" ``3 IN domain (list_delete [3] ^t)``;
print_eval "dld_pair_kept" ``2 IN domain (list_delete [1;3] ^t)``;
print_eval "dld_pair_deleted" ``1 IN domain (list_delete [1;3] ^t)``;
print_eval "dld_absent" ``9 IN domain (list_delete [3] ^t)``;
