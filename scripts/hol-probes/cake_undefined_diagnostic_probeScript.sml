load "infer_cvTheory"; load "cv_transLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val emptyWfs = prove (``unify$t_wfs FEMPTY``, simp[unifyTheory.t_wfs_def, substTheory.wfs_FEMPTY]);
val th = cv_transLib.cv_eval ``
 infer$infer_e <| loc := NONE; err := Bind [] [] |>
  <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (Lannot (Var (Long «A» (Short «foo»))) (Locs (POSN 0 11) (POSN 0 15)))
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val pre = prove (fst (dest_imp (concl th)), simp[infer_cvTheory.IMP_infer_e_pre, emptyWfs]);
val _ = (print "infer="; print_term (rhs (concl (MP th pre))); print "\n");
