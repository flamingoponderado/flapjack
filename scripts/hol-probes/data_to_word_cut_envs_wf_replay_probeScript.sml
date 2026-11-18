(* Replay cut_envs_wf from the pinned assignment proof, using its source
   statement and proof against the original word semantics theory. *)
load "preamble";
load "wordSemTheory";
open HolKernel Parse boolLib bossLib preamble wordSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val lemma = Q.prove(`cut_envs kept_names t = SOME (y1,y2) ⇒ wf y1 ∧ wf y2`,
  gvs [wordSemTheory.cut_envs_def,AllCaseEqs()] >> rw [] >>
  gvs [wordSemTheory.cut_names_def]);
val _ = if null (hyp lemma) then () else raise Fail "unexpected hypotheses";
val _ = (print "cut_envs_wf_replay_typed="; print_term (concl lemma); print "\n");
val lookup_lemma = Q.prove(
  `wordSem$cut_env names t = SOME y ∧ lookup n y = SOME a ⇒ lookup n t = SOME a`,
  PairCases_on `names` >>
  gvs [wordSemTheory.cut_env_def,wordSemTheory.cut_envs_def] >>
  gvs [wordSemTheory.cut_names_def,AllCaseEqs()] >> rw [] >>
  gvs [lookup_union,AllCaseEqs(),lookup_inter_alt]);
val _ = if null (hyp lookup_lemma) then () else raise Fail "unexpected hypotheses";
val _ = (print "cut_env_lookup_replay_typed="; print_term (concl lookup_lemma); print "\n");
