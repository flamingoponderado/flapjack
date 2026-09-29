(*
  Direct HOL-EVAL observations for the sptree set operations used by
  loop_live's shrink/fixedpoint (cakeml/pancake/loop_liveScript.sml:37-140):
  sptree$union/inter/delete (HOL/src/finite_maps/sptreeScript.sml),
  backend_common$list_delete (cakeml/compiler/backend/backend_commonScript.sml:181)
  and list$oEL.  Trees are observed through their key lists (toAList) and
  isEmpty; the Lean test Flapjack/Test/SptreeSetOpsParity.lean consumes the
  checked-in .out.
*)
load "bossLib";
load "preamble";
load "sptreeTheory";
load "backend_commonTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open sptreeTheory backend_commonTheory;

fun pe label q = let val th = EVAL q in print (label ^ "="); print_term (rconc th); print "\n" end;

pe "union_keys" ``MAP FST (toAList (union (fromAList [(0:num,()); (4,()); (6,())]) (fromAList [(1,()); (4,()); (9,())])))``;
pe "union_ln" ``isEmpty (union (LN:unit spt) LN)``;
pe "inter_keys" ``MAP FST (toAList (inter (fromAList [(0:num,()); (4,()); (6,()); (9,())]) (fromAList [(1,()); (4,()); (9,())])))``;
pe "inter_disjoint_empty" ``isEmpty (inter (fromAList [(0:num,()); (2,())]) (fromAList [(1,()); (3,())]))``;
pe "delete_keys" ``MAP FST (toAList (delete 4 (fromAList [(0:num,()); (4,()); (6,()); (9,())])))``;
pe "delete_last_empty" ``isEmpty (delete 5 (fromAList [(5:num,())]))``;
pe "delete_absent_keys" ``MAP FST (toAList (delete 7 (fromAList [(0:num,()); (4,())])))``;
pe "list_delete_keys" ``MAP FST (toAList (list_delete [4; 9; 11] (fromAList [(0:num,()); (4,()); (6,()); (9,())])))``;
pe "oel_hit" ``oEL 1 [10:num; 20; 30]``;
pe "oel_miss" ``oEL 3 [10:num; 20; 30]``;
pe "diff_keys" ``MAP FST (toAList (difference (fromAList [(0:num,()); (4,()); (6,())]) (fromAList [(1:num,()); (4,())])))``;
pe "diff_lookup_hit" ``lookup 0 (difference (fromAList [(0:num,()); (4,())]) (fromAList [(4:num,())]))``;
pe "diff_lookup_miss" ``lookup 4 (difference (fromAList [(0:num,()); (4,())]) (fromAList [(4:num,())]))``;
pe "diff_empty" ``isEmpty (difference (fromAList [(0:num,()); (4,())]) (fromAList [(0:num,()); (4,())]))``;
pe "diff_self_keys" ``MAP FST (toAList (difference (fromAList [(0:num,()); (4,()); (6,()); (9,())]) (fromAList [(0:num,()); (9,())])))``;
