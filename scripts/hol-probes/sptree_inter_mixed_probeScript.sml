(*
  Direct HOL-EVAL observations for the HETEROGENEOUS HOL sptree$inter
  (`inter : 'a num_map -> 'b num_map -> 'a num_map`, HOL/src/finite_maps/
  sptreeScript.sml:272-291): the result keeps the LEFT operand's values on the
  keys present in both trees.  This is the mixed-payload oracle required by
  flapjack-pxgp.2.1 (loopSem cut_state intersects `state.locals : Spt WordLocW`
  with a `NumSet = Spt Unit`); the Lean test
  Flapjack/Test/SptreeSetOpsParity.lean consumes the checked-in .out.

  Unlike the other probes this script deliberately does NOT load the CakeML
  preamble (only bossLib + sptreeTheory), so it runs in a bare HOL session.
*)
load "bossLib";
load "sptreeTheory";
open bossLib;
open HolKernel Parse boolLib Drule;
open sptreeTheory;

fun pe label q = let val th = EVAL q in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;

pe "inter_mixed_keys"
  ``MAP FST (toAList (inter (fromAList [(0:num,7:num);(4,8:num)])
                             (fromAList [(4,());(9,())])))``;
pe "inter_mixed_vals"
  ``MAP SND (toAList (inter (fromAList [(0:num,7:num);(4,8:num)])
                             (fromAList [(4,());(9,())])))``;
pe "inter_mixed_left_only"
  ``MAP SND (toAList (inter (fromAList [(0:num,true);(4,false)])
                             (fromAList [(1,());(4,())])))``;
pe "inter_mixed_disjoint"
  ``isEmpty (inter (fromAList [(0:num,7:num)]) (fromAList [(1,())]))``;
