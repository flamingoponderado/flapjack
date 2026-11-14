(* Typed statements of the HOL `bag` theory declarations ported in
   `Flapjack/Misc/Bag*.lean`, from the built HOL4 core theory (no rebuild). *)
load "bagTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = (print "bag_type=";
  print_type (type_of ``(EMPTY_BAG : 'a bag)``); print "\n");
val _ = show_thm "EMPTY_BAG_typed=" bagTheory.EMPTY_BAG;
val _ = show_thm "BAG_INN_typed=" bagTheory.BAG_INN;
val _ = show_thm "BAG_IN_typed=" bagTheory.BAG_IN;
val _ = show_thm "BAG_UNION_typed=" bagTheory.BAG_UNION;
val _ = show_thm "BAG_INSERT_typed=" bagTheory.BAG_INSERT;
val _ = show_thm "SUB_BAG_typed=" bagTheory.SUB_BAG;
val _ = show_thm "BAG_ALL_DISTINCT_typed=" bagTheory.BAG_ALL_DISTINCT;
val _ = show_thm "BAG_OF_SET_typed=" bagTheory.BAG_OF_SET;
val _ = show_thm "SET_OF_BAG_typed=" bagTheory.SET_OF_BAG;
val _ = show_thm "FINITE_BAG_typed=" bagTheory.FINITE_BAG;
val _ = show_thm "FINITE_EMPTY_BAG_typed=" bagTheory.FINITE_EMPTY_BAG;
val _ = show_thm "FINITE_BAG_INSERT_typed=" bagTheory.FINITE_BAG_INSERT;
val _ = (print "FINITE_BAG_UNION_1_typed=";
  Lib.with_flag (Globals.show_types,true) print_term
    ``!b1:'a bag. FINITE_BAG b1 ==> !b2:'a bag. FINITE_BAG b2 ==>
      FINITE_BAG (BAG_UNION b1 b2)``; print "\n");
val _ = show_thm "BAG_UNION_EMPTY_typed=" bagTheory.BAG_UNION_EMPTY;
val _ = show_thm "BAG_ALL_DISTINCT_SUB_BAG_typed=" bagTheory.BAG_ALL_DISTINCT_SUB_BAG;
val _ = show_thm "BAG_IMAGE_DEF_typed=" bagTheory.BAG_IMAGE_DEF;
val _ = show_thm "BAG_FILTER_DEF_typed=" bagTheory.BAG_FILTER_DEF;
val _ = show_thm "BAG_CARD_typed=" bagTheory.BAG_CARD;
val _ = show_thm "BAG_CARD_RELn_typed=" bagTheory.BAG_CARD_RELn;
val _ = show_thm "SUB_BAG_CARD_typed=" bagTheory.SUB_BAG_CARD;
val _ = show_thm "FINITE_SUB_BAG_typed=" bagTheory.FINITE_SUB_BAG;
val _ = show_thm "FINITE_BAG_FILTER_typed=" bagTheory.FINITE_BAG_FILTER;
