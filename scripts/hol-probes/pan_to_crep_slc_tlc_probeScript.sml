(* Direct HOL-EVAL rows for both lookup sides of slc_tlc_rw
   (pan_to_crepProofScript.sml:2321).  The Lean counterpart is
   Flapjack.Test.PanToCrepStateRelCarrierParity: slcHOL/tlcHOL lookup rows and
   the slcTlcRwHOL rewrite rows. *)
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

val vsh = ``[(strlit "x", panLang$One); (strlit "y", panLang$One)] :
  (mlstring # panLang$shape) list``;
val args = ``[panSem$Val (panSem$Word (5w:8 word)); panSem$Val (panSem$Word (7w:8 word))] : 8 panSem$v list``;
val ns = ``[0;1] : num list``;
val slc_map = ``FEMPTY |++ ZIP (MAP FST ^vsh, ^args)``;
val tlc_map = ``FEMPTY |++ ZIP (^ns, FLAT (MAP panSem$flatten ^args))``;

val _ = print_eval "slc_tlc_slc_x" ``FLOOKUP ^slc_map (strlit "x")``;
val _ = print_eval "slc_tlc_slc_y" ``FLOOKUP ^slc_map (strlit "y")``;
val _ = print_eval "slc_tlc_slc_absent" ``FLOOKUP ^slc_map (strlit "z")``;
val _ = print_eval "slc_tlc_tlc_0" ``FLOOKUP ^tlc_map 0``;
val _ = print_eval "slc_tlc_tlc_1" ``FLOOKUP ^tlc_map 1``;
val _ = print_eval "slc_tlc_tlc_absent" ``FLOOKUP ^tlc_map 2``;
val _ = print_eval "slc_tlc_rw_slc_holds"
  ``^slc_map = pan_to_crepProof$slc ^vsh ^args``;
val _ = print_eval "slc_tlc_rw_tlc_holds"
  ``^tlc_map = pan_to_crepProof$tlc ^ns ^args``;
val _ = print_eval "slc_tlc_slc_rhs_lookup"
  ``FLOOKUP (pan_to_crepProof$slc ^vsh ^args) (strlit "x")``;
val _ = print_eval "slc_tlc_tlc_rhs_lookup"
  ``FLOOKUP (pan_to_crepProof$tlc ^ns ^args) 1``;
val _ = print_eval "slc_tlc_probe_done" ``0``;
