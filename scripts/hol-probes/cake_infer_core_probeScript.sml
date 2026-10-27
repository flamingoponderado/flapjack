load "infer_cvTheory";
load "cv_transLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val emptyWfs = prove (``unify$t_wfs FEMPTY``, simp[unifyTheory.t_wfs_def, substTheory.wfs_FEMPTY]);
val fnThm = cv_transLib.cv_eval ``
 infer$infer_e <| loc := NONE; err := Bind [] [] |>
  <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (Fun «x» (Var (Short «x»)))
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val fnPre = prove (fst (dest_imp (concl fnThm)), simp[infer_cvTheory.IMP_infer_e_pre, emptyWfs]);
val _ = (print "function="; print_term (rhs (concl (MP fnThm fnPre))); print "\n");
val patThm = cv_transLib.cv_eval ``
 infer$infer_p <| loc := NONE; err := Bind [] [] |>
  <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (Pcon NONE [Pvar «x»; Pref (Pvar «y»)])
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val patPre = prove (fst (dest_imp (concl patThm)), simp[infer_cvTheory.IMP_infer_p_pre, emptyWfs]);
val _ = (print "pattern="; print_term (rhs (concl (MP patThm patPre))); print "\n");
val appThm = cv_transLib.cv_eval ``
 infer$infer_e <| loc := NONE; err := Bind [] [] |>
  <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (App Opapp [Fun «x» (Var (Short «x»)); Lit (IntLit 1)])
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val appPre = prove (fst (dest_imp (concl appThm)), simp[infer_cvTheory.IMP_infer_e_pre, emptyWfs]);
val _ = (print "application="; print_term (rhs (concl (MP appThm appPre))); print "\n");
val recThm = cv_transLib.cv_eval ``
 infer$infer_e <| loc := NONE; err := Bind [] [] |>
  <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (Letrec [(«f»,«x»,Var (Short «x»))] (Var (Short «f»)))
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val recPre = prove (fst (dest_imp (concl recThm)), simp[infer_cvTheory.IMP_infer_e_pre, emptyWfs]);
val _ = (print "recursive="; print_term (rhs (concl (MP recThm recPre))); print "\n");
val annThm = cv_transLib.cv_eval ``
 infer$infer_e <| loc := NONE; err := Bind [] [] |>
  <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [(«int»,([],Tapp [] 5))] [] |>
  (Tannot (Lit (IntLit 3)) (Atapp [] (Short «int»)))
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val annPre = prove (fst (dest_imp (concl annThm)), simp[infer_cvTheory.IMP_infer_e_pre, emptyWfs]);
val _ = (print "annotation="; print_term (rhs (concl (MP annThm annPre))); print "\n");
