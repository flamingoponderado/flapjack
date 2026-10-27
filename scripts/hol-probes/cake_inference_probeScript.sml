load "inferTheory";
load "unifyTheory";
load "unify_cvTheory";
load "cv_transLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val subst = rhs (concl (EVAL ``
 infer$infer_deBruijn_subst [Infer_Tuvar 9; Infer_Tapp [] Tint_num]
  (Infer_Tapp [Infer_Tvar_db 0; Infer_Tvar_db 1; Infer_Tvar_db 4] Tfn_num)``));
val _ = (print "subst="; print_term subst; print "\n");
val generalise = rhs (concl (EVAL ``
 let (count,s,t) = infer$generalise 2 0 FEMPTY
   (Infer_Tapp [Infer_Tuvar 1; Infer_Tuvar 2; Infer_Tuvar 2; Infer_Tuvar 4] Ttup_num) in
 (count,FLOOKUP s 2,FLOOKUP s 4,t)``));
val _ = (print "generalise="; print_term generalise; print "\n");
val unificationThm = cv_transLib.cv_eval ``
 unify$t_unify FEMPTY (Infer_Tapp [Infer_Tuvar 0; Infer_Tuvar 1] 4)
                  (Infer_Tapp [Infer_Tapp [] 5; Infer_Tuvar 0] 4)``;
val emptyWfs = prove (``unify$t_wfs FEMPTY``, simp[unifyTheory.t_wfs_def, substTheory.wfs_FEMPTY]);
val unification = rhs (concl (MP unificationThm emptyWfs));
val _ = (print "unify="; print_term unification; print "\n");
val occursThm = cv_transLib.cv_eval ``
 unify$t_unify FEMPTY (Infer_Tuvar 0) (Infer_Tapp [Infer_Tuvar 0] 6)``;
val _ = (print "occurs="; print_term (rhs (concl (MP occursThm emptyWfs))); print "\n");
