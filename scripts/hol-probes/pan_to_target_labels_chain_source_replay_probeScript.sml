(* Literal source-statement replay of pan_to_targetProof pan_to_stack_first_ALL_DISTINCT,
   pan_to_stack_compile_lab_pres, pan_to_lab_labels_ok, word_to_stack_good_code_lemma and
   from_pan_to_lab_no_install. The original proof theory and its backendProof ancestor are
   unbuilt, so HOL's proofs are not re-run: the script fails if the pinned source text of any
   statement, proof or used overload changes, then type-checks each statement over the loaded
   original theories and prints it. This is not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "pan_to_wordProofTheory"; load "word_to_wordProofTheory";
load "word_to_stackProofTheory"; load "stack_to_labProofTheory"; load "lab_to_targetProofTheory";
load "pan_to_targetTheory"; load "targetSemTheory"; load "labPropsTheory";
open bossLib HolKernel Parse preamble;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_targetProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
fun guard name lit = if String.isSubstring lit source_text then ()
  else raise Fail (name ^ " literal source changed");
val _ = guard "overload word_to_word_compile" "Overload word_to_word_compile[local] = ``word_to_word$compile``";
val _ = overload_on ("word_to_word_compile", ``word_to_word$compile``);
val _ = guard "overload word_to_stack_compile" "Overload word_to_stack_compile[local] = ``word_to_stack$compile``";
val _ = overload_on ("word_to_stack_compile", ``word_to_stack$compile``);
val _ = guard "overload stack_to_lab_compile" "Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``";
val _ = overload_on ("stack_to_lab_compile", ``stack_to_lab$compile``);
val _ = guard "overload pan_to_word_compile_prog" "Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog``";
val _ = overload_on ("pan_to_word_compile_prog", ``pan_to_word$compile_prog``);
fun pr_typed label tm = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term tm; print "\n");
fun pr_stmt label tm = (print (label ^ "="); print_term tm; print "\n");
val _ = Globals.linewidth := 1000000;
val _ = guard "pan_to_stack_first_ALL_DISTINCT" "Theorem pan_to_stack_first_ALL_DISTINCT:\n  pan_to_word_compile_prog mc.target.config.ISA pan_code = wprog0 \226\136\167\n  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) \226\136\167 mc.target.config.ISA \226\137\160 Ag32 \226\136\167\n  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) \226\136\167\n  ALL_DISTINCT (MAP FST (functions pan_code)) \226\135\146\n  ALL_DISTINCT (MAP FST p)\nProof\n  strip_tac>>drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>\n  strip_tac>>\n  drule backendProofTheory.compile_to_word_conventions2>>\n  impl_tac\n  >- (irule_at Any EVERY_MONOTONIC>>\n      qexists \226\128\152\206\187_. mc.target.config.ISA \226\137\160 Ag32\226\128\153>>\n      simp[FORALL_PROD])>>\n  strip_tac>>\n  gs[]>>\n  qpat_x_assum \226\128\152MAP FST wprog = _\226\128\153 $ assume_tac o GSYM>>gs[]>>\n  drule word_to_stack_compile_FST>>\n  strip_tac>>gs[]>>\n  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>\n  strip_tac>>\n  gs[GSYM EVERY_MAP]>>EVAL_TAC>>gs[EVERY_MEM]>>\n  rw[]>- (first_x_assum $ qspec_then \226\128\1525\226\128\153 assume_tac>>gs[])>>\n  first_x_assum $ qspec_then \226\128\1526\226\128\153 assume_tac>>gs[]>>\n  metis_tac[FST,SND,PAIR]\nQED";
val pan_to_stack_first_ALL_DISTINCT_tm = ``  pan_to_word_compile_prog mc.target.config.ISA pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧ mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  ALL_DISTINCT (MAP FST p)``;
val _ = pr_stmt "pan_to_stack_first_ALL_DISTINCT_replay_statement" pan_to_stack_first_ALL_DISTINCT_tm;
val _ = pr_typed "pan_to_stack_first_ALL_DISTINCT_replay_typed" pan_to_stack_first_ALL_DISTINCT_tm;
val _ = guard "pan_to_stack_compile_lab_pres" "Theorem pan_to_stack_compile_lab_pres:\n  pan_to_word$compile_prog mc.target.config.ISA pan_code = wprog0 \226\136\167\n  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 =(col,wprog) \226\136\167 mc.target.config.ISA \226\137\160 Ag32 \226\136\167\n  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) \226\136\167\n  ALL_DISTINCT (MAP FST (functions pan_code)) \226\135\146\n  ALL_DISTINCT (MAP FST p) \226\136\167\n  EVERY (\206\187n. n \226\137\160 0 \226\136\167 n \226\137\160 1 \226\136\167 n \226\137\160 2 \226\136\167 n \226\137\160 gc_stub_location) (MAP FST p) \226\136\167\n  EVERY\n  (\206\187(n,p).\n     (let\n        labs = extract_labels p\n      in\n        EVERY (\206\187(l1,l2). l1 = n \226\136\167 l2 \226\137\160 0 \226\136\167 l2 \226\137\160 1) labs \226\136\167\n        ALL_DISTINCT labs)) p\nProof\n  strip_tac>>\n  drule pan_to_wordProofTheory.pan_to_word_compile_lab_pres>>strip_tac>>\n  gs[]>>\n  drule backendProofTheory.compile_to_word_conventions2>>\n  impl_tac\n  >- (irule_at Any EVERY_MONOTONIC>>\n      qexists \226\128\152\206\187_. mc.target.config.ISA \226\137\160 Ag32\226\128\153>>\n      simp[FORALL_PROD])>>\n  strip_tac>>\n  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>\n  strip_tac>>gs[]>>\n  \226\128\152EVERY\n   (\206\187(n,m,p).\n      (let\n         labs = extract_labels p\n       in\n         EVERY (\206\187(l1,l2). l1 = n \226\136\167 l2 \226\137\160 0 \226\136\167 l2 \226\137\160 1) labs \226\136\167\n         ALL_DISTINCT labs)) wprog\226\128\153\n    by (gs[EVERY2_EVERY]>>gs[EVERY_EL]>>ntac 2 strip_tac>>\n        ntac 3 (first_x_assum $ qspec_then \226\128\152n\226\128\153 assume_tac)>>\n        pairarg_tac>>gs[EL_ZIP, wordConvsTheory.labels_rel_def]>>\n        pairarg_tac>>gs[EL_MAP]>>strip_tac>>strip_tac>>\n        \226\128\152EL n (MAP FST wprog) = EL n (MAP FST wprog0)\226\128\153 by rfs[]>>\n        gs[EL_MAP]>>\n        pairarg_tac>>gs[]>>\n        \226\128\152(l1, l2) \226\136\136 set (extract_labels p'')\226\128\153\n          by (gs[MEM_SET_TO_LIST, SUBSET_DEF]>>\n              first_assum irule>>metis_tac[MEM_EL])>>\n        gs[MEM_EL]>>\n        first_x_assum $ qspec_then \226\128\152n''''\226\128\153 assume_tac>>\n        gs[]>>pairarg_tac>>gs[])>>\n  drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_compile_lab_pres)>>\n  disch_then $ qspec_then \226\128\152mc.target.config\226\128\153 assume_tac>>\n  drule_all pan_to_stack_first_ALL_DISTINCT>>\n  strip_tac>>gs[]>>\n  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>\n  gs[backend_commonTheory.word_num_stubs_def,\n     wordLangTheory.store_consts_stub_location_def,\n     wordLangTheory.raise_stub_location_def,\n     stackLangTheory.gc_stub_location_def,\n     backend_commonTheory.stack_num_stubs_def]>>\n  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>\n  gs[GSYM EVERY_MAP, EVERY_MEM]>>ntac 3 strip_tac>>\n  first_x_assum $ qspec_then \226\128\152n\226\128\153 assume_tac>>gs[]\nQED";
val pan_to_stack_compile_lab_pres_tm = ``  pan_to_word$compile_prog mc.target.config.ISA pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 =(col,wprog) ∧ mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  ALL_DISTINCT (MAP FST p) ∧
  EVERY (λn. n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location) (MAP FST p) ∧
  EVERY
  (λ(n,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) p``;
val _ = pr_stmt "pan_to_stack_compile_lab_pres_replay_statement" pan_to_stack_compile_lab_pres_tm;
val _ = pr_typed "pan_to_stack_compile_lab_pres_replay_typed" pan_to_stack_compile_lab_pres_tm;
val _ = guard "pan_to_lab_labels_ok" "Theorem pan_to_lab_labels_ok:\n  pan_to_word_compile_prog mc.target.config.ISA pan_code = wprog0 \226\136\167\n  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) \226\136\167 mc.target.config.ISA \226\137\160 Ag32 \226\136\167\n  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) \226\136\167\n  stack_to_lab_compile c.stack_conf c.data_conf max_heap sp mc.target.config.addr_offset p = lprog \226\136\167\n  ALL_DISTINCT (MAP FST (functions pan_code)) \226\135\146\n  labels_ok lprog\nProof\n  strip_tac>>\n  qpat_x_assum \226\128\152_ = lprog\226\128\153 (assume_tac o GSYM)>>gs[]>>\n  irule stack_to_labProofTheory.stack_to_lab_compile_lab_pres>>\n  drule_all pan_to_stack_compile_lab_pres>>gs[]\nQED";
val pan_to_lab_labels_ok_tm = ``  pan_to_word_compile_prog mc.target.config.ISA pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧ mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) ∧
  stack_to_lab_compile c.stack_conf c.data_conf max_heap sp mc.target.config.addr_offset p = lprog ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  labels_ok lprog``;
val _ = pr_stmt "pan_to_lab_labels_ok_replay_statement" pan_to_lab_labels_ok_tm;
val _ = pr_typed "pan_to_lab_labels_ok_replay_typed" pan_to_lab_labels_ok_tm;
val _ = guard "word_to_stack_good_code_lemma" "Theorem word_to_stack_good_code_lemma:\n  word_to_word_compile c.word_to_word_conf mc.target.config\n  (pan_to_word_compile_prog mc.target.config.ISA pan_code) = (col,wprog) \226\136\167\n  mc.target.config.ISA \226\137\160 Ag32 \226\136\167\n  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) \226\136\167\n  LENGTH mc.target.config.avoid_regs + 13 \226\137\164 mc.target.config.reg_count \226\136\167\n  (* from backend_config_ok c *)\n  ALL_DISTINCT (MAP FST (functions pan_code)) \226\135\146\n  good_code (mc.target.config.reg_count \226\136\146\n             (LENGTH mc.target.config.avoid_regs + 3)) p\nProof\n  (* a bit slow *)\n  gs[stack_to_labProofTheory.good_code_def]>>strip_tac>>\n  qmatch_asmsub_abbrev_tac \226\128\152word_to_word_compile _ _ wprog0 = _\226\128\153>>\n  qpat_x_assum \226\128\152Abbrev (wprog0 = _)\226\128\153 (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>\n  drule_at (Pat \226\128\152word_to_word_compile _ _ _ = _\226\128\153) pan_to_stack_compile_lab_pres>>\n  disch_then drule_all>>strip_tac>>gs[]>>\n  drule backendProofTheory.compile_to_word_conventions2>>\n  impl_tac\n  >- (irule_at Any EVERY_MONOTONIC>>\n      qexists \226\128\152\206\187_. mc.target.config.ISA \226\137\160 Ag32\226\128\153>>\n      simp[FORALL_PROD])>>\n  strip_tac>>\n  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>\n  strip_tac>>gs[]>>\n  drule word_to_stack_compile_FST>>strip_tac>>\n  drule word_to_stackProofTheory.word_to_stack_stack_convs>>\n  gs[]>>impl_tac\n  >- (gs[EVERY_EL]>>\n      ntac 2 strip_tac>>\n      ntac 3 (first_x_assum $ qspec_then \226\128\152n\226\128\153 assume_tac)>>\n      gs[]>>\n      pairarg_tac>>gs[]>>\n      pairarg_tac>>gs[]>>simp[EL_MAP])>>\n  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>\n  gs[EVERY_EL]>>rpt strip_tac>>\n  pairarg_tac>>gs[EL_MAP]>>\n  qpat_x_assum \226\128\152\226\136\128n. _ \226\135\146 alloc_arg _\226\128\153 $ qspec_then \226\128\152n\226\128\153 assume_tac>>\n  gs[]>>\n\n  drule pan_to_word_compile_prog_lab_min>>\n  gs[GSYM EVERY_MAP]>>\n  qpat_x_assum \226\128\152MAP FST _ = MAP FST _\226\128\153 $ assume_tac o GSYM>>\n  gs[]>>\n  gs[GSYM EVERY_MAP, EVERY_MEM]>>strip_tac>>\n  \226\128\152MEM k (MAP FST p)\226\128\153\n    by (gs[MEM_MAP]>>gs[MEM_EL]>>gs[PULL_EXISTS]>>\n        first_assum $ irule_at (Pos last)>>gs[])>>\n  gs[backend_commonTheory.word_num_stubs_def,\n     wordLangTheory.store_consts_stub_location_def,\n     wordLangTheory.raise_stub_location_def,\n     backend_commonTheory.stack_num_stubs_def]>>\n  first_x_assum $ qspec_then \226\128\152k\226\128\153 assume_tac>>gs[]\nQED";
val word_to_stack_good_code_lemma_tm = ``  word_to_word_compile c.word_to_word_conf mc.target.config
  (pan_to_word_compile_prog mc.target.config.ISA pan_code) = (col,wprog) ∧
  mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config F wprog = (bitmaps,c'',fs,p) ∧
  LENGTH mc.target.config.avoid_regs + 13 ≤ mc.target.config.reg_count ∧
  (* from backend_config_ok c *)
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  good_code (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 3)) p``;
val _ = pr_stmt "word_to_stack_good_code_lemma_replay_statement" word_to_stack_good_code_lemma_tm;
val _ = pr_typed "word_to_stack_good_code_lemma_replay_typed" word_to_stack_good_code_lemma_tm;
val _ = guard "from_pan_to_lab_no_install" "Theorem from_pan_to_lab_no_install:\n  ALL_DISTINCT (MAP FST (functions pan_code)) \226\136\167 ac.ISA \226\137\160 Ag32 \226\136\167\n  pan_to_word_compile_prog isa pan_code = wprog0 \226\136\167\n  word_to_word_compile wc ac wprog0 = (col, wprog) \226\136\167\n  word_to_stack_compile ac F wprog = (bm, c, fs, p) \226\135\146\n  no_install (stack_to_lab_compile scc dc lim regc off p)\nProof\n  strip_tac>>\n  imp_res_tac first_compile_prog_all_distinct>>\n  first_x_assum $ qspec_then \226\128\152isa\226\128\153 assume_tac>>\n  drule pan_to_word_compile_prog_no_install_code>>strip_tac>>\n  drule pan_to_word_compile_prog_no_mt_code>>strip_tac>>\n  gs[]>>\n  drule_all word_to_word_compile_no_install_no_alloc>>strip_tac>>\n  \226\128\152MAP FST wprog0 = MAP FST wprog\226\128\153 by\n    (drule compile_to_word_conventions2>>\n     impl_tac\n     >- (irule_at Any EVERY_MONOTONIC>>\n         qexists \226\128\152\206\187_. ac.ISA \226\137\160 Ag32\226\128\153>>simp[FORALL_PROD])>>\n     gvs[])>>fs[]>>\n  drule_all word_to_stackProofTheory.word_to_stack_compile_no_install>>strip_tac>>\n  irule (SRULE[] $ stack_to_labProofTheory.stack_to_lab_compile_no_install)>>fs[]\nQED";
val from_pan_to_lab_no_install_tm = ``  ALL_DISTINCT (MAP FST (functions pan_code)) ∧ ac.ISA ≠ Ag32 ∧
  pan_to_word_compile_prog isa pan_code = wprog0 ∧
  word_to_word_compile wc ac wprog0 = (col, wprog) ∧
  word_to_stack_compile ac F wprog = (bm, c, fs, p) ⇒
  no_install (stack_to_lab_compile scc dc lim regc off p)``;
val _ = pr_stmt "from_pan_to_lab_no_install_replay_statement" from_pan_to_lab_no_install_tm;
val _ = pr_typed "from_pan_to_lab_no_install_replay_typed" from_pan_to_lab_no_install_tm;
