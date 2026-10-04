load "preamble"; load "word_depthProofTheory"; load "backendPropsTheory";
open HolKernel Parse boolLib bossLib preamble wordLangTheory wordSemTheory word_depthTheory backendPropsTheory word_depthProofTheory;
val _ = new_theory "flapjack_word_depth_helpers_replay";
val _ = Globals.linewidth := 1000000;
(* Literal source replays of the [local] lemmas (word_depthProofScript 12-31, 120-146); local theorems are not exported from word_depthProofTheory. *)

Theorem option_le_X_MAX_X[simp]:
  option_le x (OPTION_MAP2 MAX m x) /\
  option_le x (OPTION_MAP2 MAX x m)
Proof
  Cases_on `m` \\ Cases_on `x` \\ fs []
QED
val _ = if null (hyp (option_le_X_MAX_X)) then () else raise Fail "hypotheses: option_le_X_MAX_X";
val _ = (print "option_le_X_MAX_X_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (option_le_X_MAX_X)); print "\n");

Theorem OPTION_MAP2_MAX_IDEMPOT[simp]:
  OPTION_MAP2 MAX x x = x
Proof
  Cases_on `x` \\ fs []
QED
val _ = if null (hyp (OPTION_MAP2_MAX_IDEMPOT)) then () else raise Fail "hypotheses: OPTION_MAP2_MAX_IDEMPOT";
val _ = (print "OPTION_MAP2_MAX_IDEMPOT_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (OPTION_MAP2_MAX_IDEMPOT)); print "\n");

Theorem OPTION_MAP2_SOME_0[simp]:
  OPTION_MAP2 (+) x (SOME 0n) = x /\
  OPTION_MAP2 MAX x (SOME 0n) = x
Proof
  Cases_on `x` \\ fs []
QED
val _ = if null (hyp (OPTION_MAP2_SOME_0)) then () else raise Fail "hypotheses: OPTION_MAP2_SOME_0";
val _ = (print "OPTION_MAP2_SOME_0_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (OPTION_MAP2_SOME_0)); print "\n");
val _ = if null (hyp (word_depthProofTheory.max_depth_mk_Branch)) then () else raise Fail "hypotheses: max_depth_mk_Branch";
val _ = (print "max_depth_mk_Branch_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_depthProofTheory.max_depth_mk_Branch)); print "\n");
val _ = if null (hyp (word_depthProofTheory.MEM_max_depth_graphs)) then () else raise Fail "hypotheses: MEM_max_depth_graphs";
val _ = (print "MEM_max_depth_graphs_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_depthProofTheory.MEM_max_depth_graphs)); print "\n");
val _ = if null (hyp (word_depthProofTheory.option_le_max_depth_graph)) then () else raise Fail "hypotheses: option_le_max_depth_graph";
val _ = (print "option_le_max_depth_graph_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_depthProofTheory.option_le_max_depth_graph)); print "\n");
val _ = if null (hyp (word_depthProofTheory.option_le_max_depth_graphs)) then () else raise Fail "hypotheses: option_le_max_depth_graphs";
val _ = (print "option_le_max_depth_graphs_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (word_depthProofTheory.option_le_max_depth_graphs)); print "\n");
Theorem LENGTH_LESS_size:
  !name ns funs y.
    ~MEM name ns /\ set ns ⊆ domain funs /\ ALL_DISTINCT ns /\
    lookup name funs = SOME y ==>
    LENGTH ns < size funs
Proof
  rw []
  \\ `LENGTH ns = size (fromAList (MAP (\n. (n,THE (lookup n funs))) ns))` by
   (qmatch_goalsub_abbrev_tac `LENGTH _ = size (fromAList xs)`
    \\ qsuff_tac `ALL_DISTINCT (MAP FST xs) /\ LENGTH ns = LENGTH xs`
    THEN1 (rw [] \\ match_mp_tac (GSYM miscTheory.size_fromAList) \\ fs [])
    \\ qsuff_tac `MAP FST xs = ns` \\ fs [] \\ fs [Abbr`xs`]
    \\ qid_spec_tac `ns` \\ Induct \\ fs [])
  \\ fs [] \\ match_mp_tac sptreeTheory.IMP_size_LESS_size
  \\ rpt conj_tac THEN1
   (fs [subspt_lookup,lookup_fromAList]
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ last_x_assum kall_tac
    \\ Induct_on `ns`
    \\ fs [] \\ rw []
    \\ Cases_on `h = x` \\ fs []
    \\ fs [domain_lookup] \\ rfs [])
  \\ fs [domain_fromAList]
  \\ fs [EXTENSION]
  \\ qexists_tac `name`
  \\ fs [domain_lookup]
  \\ fs [MEM_MAP,FORALL_PROD]
QED
val _ = if null (hyp (LENGTH_LESS_size)) then () else raise Fail "hypotheses: LENGTH_LESS_size";
val _ = (print "LENGTH_LESS_size_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (LENGTH_LESS_size)); print "\n");
