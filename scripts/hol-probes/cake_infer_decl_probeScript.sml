load "infer_cvTheory";
load "cv_transLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val emptyWfs = prove (``unify$t_wfs FEMPTY``, simp[unifyTheory.t_wfs_def, substTheory.wfs_FEMPTY]);
val idThm = cv_transLib.cv_eval ``
 infer$infer_d <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (Dlet (Locs UNKNOWNpt UNKNOWNpt) (Pvar «id») (Fun «x» (Var (Short «x»))))
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val idPre = prove (fst (dest_imp (concl idThm)), simp[infer_cvTheory.IMP_infer_d_pre, emptyWfs]);
val _ = (print "identity="; print_term (rhs (concl (MP idThm idPre))); print "\n");
val dtypeThm = cv_transLib.cv_eval ``
 infer$infer_d <| inf_v := Bind [] []; inf_c := Bind [] []; inf_t := Bind [] [] |>
  (Dtype (Locs UNKNOWNpt UNKNOWNpt) [([],«t»,[(«A»,[]);(«B»,[])])])
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``;
val dtypePre = prove (fst (dest_imp (concl dtypeThm)), simp[infer_cvTheory.IMP_infer_d_pre, emptyWfs]);
val _ = (print "datatype="; print_term (rhs (concl (MP dtypeThm dtypePre))); print "\n");
val initial = rhs (concl (EVAL ``
 let env = infer$init_config in
 (nsLookup env.inf_t (Short «int»), nsLookup env.inf_t (Short «list»),
  nsLookup env.inf_c (Short «::»), infer$start_type_id)``));
val _ = (print "initial="; print_term initial; print "\n");
