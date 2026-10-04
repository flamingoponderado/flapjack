load "preamble"; load "word_to_wordProofTheory";
open HolKernel Parse bossLib preamble word_to_wordTheory
  word_to_wordProofTheory wordConvsTheory word_instTheory;
val _ = Globals.linewidth := 1000000;
(* Unchanged original whole local statement and proof. *)
val fullConventions = GEN_ALL(prove(``
compile wc ac p = (_,ps) ∧
  EVERY (λ(_,_,prg). wordConvs$no_share_inst prg ∨ ac.ISA ≠ Ag32) p ==>
  MAP FST ps = MAP FST p ∧
  LIST_REL wordConvs$labels_rel
    (MAP (wordConvs$extract_labels ∘ SND ∘ SND) p)
    (MAP (wordConvs$extract_labels ∘ SND ∘ SND) ps) ∧
  EVERY (λ(n,m,prog).
    wordConvs$flat_exp_conventions prog ∧
    wordConvs$post_alloc_conventions
      (ac.reg_count - (5 + LENGTH ac.avoid_regs)) prog ∧
    (EVERY (λ(n,m,prog).
              wordConvs$every_inst (wordConvs$inst_ok_less ac) prog)
           p ∧ addr_offset_ok ac 0w ∧ hw_offset_ok ac 0w ∧
     byte_offset_ok ac 0w ⇒
               wordConvs$full_inst_ok_less ac prog) ∧
              (ac.two_reg_arith ⇒
               wordConvs$every_inst wordConvs$two_reg_inst prog) ∧
              (wordConvs$no_share_inst prog ∨ ac.ISA ≠ Ag32)) ps
``,
  rw []
  \\ mp_tac word_to_wordProofTheory.compile_to_word_conventions
  \\ simp [] \\ rw[]
));
val _ = if null(hyp fullConventions) andalso null(free_vars(concl fullConventions)) then () else raise Fail "open full conventions";
val _ = (print "fullConventions_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl fullConventions));
val _ = print("fullConventions_proved=" ^ term_to_string(rhs(concl(EQT_INTRO fullConventions))) ^ "\n");
val _ = print("fullConventions_hypotheses=" ^ Int.toString(length(hyp fullConventions)) ^ "\n");
