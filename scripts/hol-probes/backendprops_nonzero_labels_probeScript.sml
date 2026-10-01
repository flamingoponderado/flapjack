load "preamble";
load "backendPropsTheory";
open bossLib HolKernel Parse preamble backendPropsTheory;
(* Set comprehensions need extensional HOL reasoning rather than EVAL alone.
   Only the original definition and standard set laws are used; none of the
   six source restriction theorems under review is supplied to the tactic. *)
fun out label q =
  let
    val negative = label = "nz_univ_zero" orelse label = "nz_false_premise"
    val assertion = if negative then mk_neg q else q
    val checked = prove (assertion,
      simp [LET_THM, pred_setTheory.BIGUNION_INSERT,
        pred_setTheory.BIGUNION_EMPTY, pred_setTheory.IMAGE_INSERT,
        pred_setTheory.IMAGE_EMPTY] >>
      rw [restrict_nonzero_def, EXTENSION, SUBSET_DEF, FORALL_PROD] >>
      fs [] >> metis_tac []);
    val normalized = if negative then EQF_INTRO checked else EQT_INTRO checked
  in
    print (label ^ "="); print_term (rconc normalized); print "\n"
  end;
val _ = out "nz_empty" ``restrict_nonzero {} = {}``;
val _ = out "nz_zero" ``restrict_nonzero {(7,0);(0,0)} = {}``;
val _ = out "nz_first_zero" ``restrict_nonzero {(0,0);(0,1)} = {(0,1)}``;
val _ = out "nz_mixed" ``restrict_nonzero {(7,0);(7,2);(8,1)} = {(7,2);(8,1)}``;
val _ = out "nz_duplicate" ``restrict_nonzero {(8,1);(8,1);(8,0)} = {(8,1)}``;
val _ = out "nz_large" ``restrict_nonzero {(1208925819614629174706176,0);(1208925819614629174706176,1208925819614629174706176)} = {(1208925819614629174706176,1208925819614629174706176)}``;
val _ = out "nz_subset" ``restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET {(7,0);(7,2);(8,1)}``;
val _ = out "nz_subset_left" ``({(7,0);(7,2);(8,1)} SUBSET ({(7,0);(7,2);(8,1)} UNION {(9,0)})) /\ (restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET ({(7,0);(7,2);(8,1)} UNION {(9,0)}))``;
val _ = out "nz_left_union" ``(restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET ({(7,0);(7,2)} UNION {(8,1);(8,0)})) /\ (restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET (restrict_nonzero {(7,0);(7,2)} UNION {(8,1);(8,0)}))``;
val _ = out "nz_right_union" ``(restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET ({(7,0);(7,2)} UNION {(8,1);(8,0)})) /\ (restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET ({(7,0);(7,2)} UNION restrict_nonzero {(8,1);(8,0)}))``;
val _ = out "nz_mono" ``({(7,0);(7,2);(8,1)} SUBSET ({(7,0);(7,2);(8,1)} UNION {(9,0);(9,3)})) /\ (restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET restrict_nonzero ({(7,0);(7,2);(8,1)} UNION {(9,0);(9,3)}))``;
val _ = out "nz_bigunion" ``let ss = {{(7,0);(8,1)};{};{(8,1);(9,2)}} in restrict_nonzero (BIGUNION ss) = BIGUNION (IMAGE restrict_nonzero ss)``;
val _ = out "nz_univ_kept" ``(1208925819614629174706176,1) IN restrict_nonzero UNIV``;
val _ = out "nz_univ_zero" ``(1208925819614629174706176,0) IN restrict_nonzero UNIV``;
val _ = out "nz_false_premise" ``restrict_nonzero {(7,0);(7,2);(8,1)} SUBSET {(7,0)}``;
