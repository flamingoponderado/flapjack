(* Literal original full theorem and proof replay, not a reduced test.
   Source word_allocProofScript.sml:6524-6549. *)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib HolKernel Parse preamble wordSemTheory;
val _ = Globals.linewidth := 10000;
val replay = prove (``∀ls cur_ssa (cst:('a,'b,'c) wordSem$state).
    ALL_DISTINCT ls ∧
    (∀v. MEM v ls ⇒
         ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val) ⇒
    ∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
         LENGTH vs = LENGTH ls ∧
         ∀i. i < LENGTH ls ⇒
             lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)``, (
  Induct >- simp[get_vars_def] >>
  rpt strip_tac >>
  fs[] >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
        LENGTH vs = LENGTH ls ∧
        ∀i. i < LENGTH ls ⇒
            lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)`
    by (first_x_assum match_mp_tac >> rpt strip_tac >>
        last_x_assum match_mp_tac >> simp[]) >>
  `∃val. lookup (THE (lookup h cur_ssa)) cst.locals = SOME val`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  qexists_tac `val::vs` >>
  simp[get_vars_def, get_var_def] >>
  Cases >> simp[]));
val _ = print ("ssa_reconcile_get_vars_original_proof=" ^ term_to_string (concl replay) ^ "\n");
val _ = print ("ssa_reconcile_get_vars_original_type=" ^ String.concatWith " | " (map (type_to_string o type_of) (#1 (strip_forall (concl replay)))) ^ "\n");
