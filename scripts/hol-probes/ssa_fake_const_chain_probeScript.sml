load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordLangTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
(* Literal original local statements/proof scripts; no reference-tree exports. *)
val foldr_insert_const_swap = Q.prove (`  ∀rs h (v:'a word_loc) m.
    FOLDR (λr loc. insert r v loc) (insert h v m) rs =
    insert h v (FOLDR (λr loc. insert r v loc) m rs)`,
  Induct >> rw[] >>
  Cases_on `h = h'` >> simp[insert_swap]);
val evaluate_fake_const_chain = Q.prove (`  ∀rs (cst:('a,'b,'c) wordSem$state).
    evaluate (FOLDR Seq Skip (MAP (λr. (fake_move r):'a wordLang$prog) rs), cst) =
      (NONE, cst with locals := FOLDR (λr loc. insert r (Word 0w) loc) cst.locals rs)`,
  Induct
  >- simp[evaluate_def, wordSemTheory.state_component_equality] >>
  rpt strip_tac >>
  simp[evaluate_def, fake_move_def, inst_def, assign_def, word_exp_def,
       set_var_def] >>
  first_x_assum (qspec_then `cst with locals := insert h (Word 0w) cst.locals`
                            mp_tac) >>
  simp[fake_move_def, inst_def, assign_def, word_exp_def, set_var_def] >>
  disch_then kall_tac >>
  simp[foldr_insert_const_swap]);
val evaluate_fake_const_chain_locals = Q.prove (`  ∀rs (cst:('a,'b,'c) wordSem$state).
    let rcst = SND (evaluate (FOLDR Seq Skip
      (MAP (λr. (fake_move r):'a wordLang$prog) rs), cst)) in
    word_state_eq_rel cst rcst ∧
    domain rcst.locals = domain cst.locals ∪ set rs ∧
    (∀r. ¬ MEM r rs ⇒ lookup r rcst.locals = lookup r cst.locals) ∧
    (∀r. MEM r rs ⇒ lookup r rcst.locals = SOME (Word 0w))`,
  simp[evaluate_fake_const_chain] >>
  Induct >- simp[word_state_eq_rel_def] >>
  rpt strip_tac >> rpt conj_tac
  >- fs[word_state_eq_rel_def]
  >- (fs[EXTENSION] >> metis_tac[])
  >- (rw[lookup_insert] >> fs[] >>
      first_x_assum (qspec_then `cst` mp_tac) >> simp[])
  >- (rw[lookup_insert] >> fs[] >>
      first_x_assum (qspec_then `cst` mp_tac) >> simp[]));
fun out label th = (print(label ^ "="); print_thm th; print "\n");
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl(SPEC_ALL th)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "const_swap_full" foldr_insert_const_swap;
val _ = out "fake_chain_full" evaluate_fake_const_chain;
val _ = out "fake_chain_locals_full" evaluate_fake_const_chain_locals;
val _ = ty "const_swap_type_names" "rs" foldr_insert_const_swap;
val _ = ty "const_swap_type_value" "v" foldr_insert_const_swap;
val _ = ty "const_swap_type_locals" "m" foldr_insert_const_swap;
val _ = ty "fake_chain_type_state" "cst" evaluate_fake_const_chain;
val _ = ty "fake_chain_locals_type_state" "cst" evaluate_fake_const_chain_locals;
