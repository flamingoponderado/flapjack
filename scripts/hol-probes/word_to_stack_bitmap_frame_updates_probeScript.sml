load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory arithmeticTheory listTheory rich_listTheory miscTheory;
val _ = Globals.linewidth := 4000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
(* Restore original sequential simplifier context before replaying its proofs. *)
val _ = temp_delsimps ["TAKE_LUPDATE", "LENGTH_list_LUPDATE", "TAKE_list_LUPDATE", "list_LUPDATE_NIL", "list_LUPDATE_0_CONS"];
(* Before its local conditional theorem, the source uses the core DROP_LUPDATE. *)
val DROP_LUPDATE = miscTheory.DROP_LUPDATE;
val DROP_DROP_EQ = prove(``!n m xs. DROP m (DROP n xs) = DROP (m + n) xs``,    MATCH_ACCEPT_TAC DROP_DROP_T);
val TAKE_TAKE_MIN = prove(``!xs m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs``,   simp[Once MIN_COMM] >>
  MATCH_ACCEPT_TAC TAKE_TAKE_MIN);
val TAKE_DROP_EQ = prove(``!xs n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)``,   pure_rewrite_tac[Once ADD_COMM] >>
  MATCH_ACCEPT_TAC TAKE_DROP_SWAP);
val TAKE_LUPDATE = prove(``!xs n x i. TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs)``,   Induct \\ fs [LUPDATE_def] \\ Cases_on `i` \\ fs [LUPDATE_def] \\ rw [LUPDATE_def]
  >-
    (Cases_on`n`>>fs[LUPDATE_def])
  >>
    Cases_on`n'`>>fs[LUPDATE_def]);
val _ = augment_srw_ss [rewrites [TAKE_LUPDATE]];
val DROP_LUPDATE_lemma1 = prove(``!xs n m h. n <= m ==>
               DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n xs)``,   MATCH_ACCEPT_TAC DROP_LUPDATE);
val DROP_LUPDATE_lemma2 = prove(``!xs n m h. m < n ==> DROP n (LUPDATE h m xs) = DROP n xs``,   Induct \\ fs [LUPDATE_def] \\ rw []
  \\ Cases_on `m` \\ fs [LUPDATE_def]);
val DROP_LUPDATE = prove(``!n h m xs.
        DROP n (LUPDATE h m xs) =
        if m < n then DROP n xs else LUPDATE h (m - n) (DROP n xs)``,     rw [DROP_LUPDATE_lemma2]
    \\ match_mp_tac DROP_LUPDATE_lemma1
    \\ fs [NOT_LESS]);
val LENGTH_list_LUPDATE = prove(``!xs n ys. LENGTH (list_LUPDATE xs n ys) = LENGTH ys``,   Induct \\ fs [list_LUPDATE_def]);
val _ = augment_srw_ss [rewrites [LENGTH_list_LUPDATE]];
val TAKE_list_LUPDATE = prove(``!ys xs n i. TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE n xs)``,   Induct \\ fs [list_LUPDATE_def]);
val _ = augment_srw_ss [rewrites [TAKE_list_LUPDATE]];
val LLOOKUP_list_LUPDATE_IGNORE = prove(``!xs i n ys.
      i + LENGTH xs <= n ==>
      LLOOKUP (list_LUPDATE xs i ys) n = LLOOKUP ys n``,   Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `(i+1) + LENGTH xs <= n` by decide_tac \\ res_tac
  \\ `i <> n` by decide_tac \\ fs [LLOOKUP_LUPDATE]);
val DROP_list_LUPDATE = prove(``!ys n m xs.
      n <= m ==>
      DROP n (list_LUPDATE ys m xs) =
      list_LUPDATE ys (m - n) (DROP n xs)``,   Induct
  \\ fs [list_LUPDATE_def,LENGTH_NIL,PULL_FORALL]
  \\ rpt strip_tac \\ `n <= m + 1` by decide_tac
  \\ rw [] \\ `m + 1 - n = m - n + 1 /\ ~(m < n)` by decide_tac
  \\ fs [DROP_LUPDATE]);
val DROP_list_LUPDATE_IGNORE = prove(``!xs i ys n.
      LENGTH xs + i <= n ==>
      DROP n (list_LUPDATE xs i ys) = DROP n ys``,   Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `LENGTH xs + (i+1) <= n /\ i < n` by decide_tac
  \\ fs [DROP_LUPDATE]);
val list_LUPDATE_NIL = prove(``!xs i. list_LUPDATE xs i [] = []``,   Induct \\ fs [list_LUPDATE_def,LUPDATE_def]);
val _ = augment_srw_ss [rewrites [list_LUPDATE_NIL]];
val LUPDATE_TAKE_LEMMA = prove(``!xs n w. LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs)``,   Induct \\ Cases_on `n` \\ fs [LUPDATE_def]);
val list_LUPDATE_TAKE_DROP = prove(``!xs (ys:'a list) n.
       list_LUPDATE xs n ys = TAKE n ys ++ list_LUPDATE xs 0 (DROP n ys)``,   Induct \\ simp_tac std_ss [Once list_LUPDATE_def]
  \\ once_rewrite_tac [list_LUPDATE_def] THEN1 fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [DROP_LUPDATE,DROP_DROP_EQ,AC ADD_COMM ADD_ASSOC]
  \\ simp_tac std_ss [Once LUPDATE_TAKE_LEMMA,TAKE_TAKE_MIN] \\ rpt strip_tac
  \\ `MIN (n + 1) n = n`  by (fs [MIN_DEF] \\ decide_tac) \\ fs []
  \\ AP_TERM_TAC \\ fs [TAKE_DROP_EQ,AC ADD_COMM ADD_ASSOC]);
val list_LUPDATE_0_CONS = prove(``!xs x ys y. list_LUPDATE (x::xs) 0 (y::ys) = x :: list_LUPDATE xs 0 ys``,   fs [list_LUPDATE_def,LUPDATE_def]
  \\ simp_tac std_ss [Once list_LUPDATE_TAKE_DROP] \\ fs []);
val _ = augment_srw_ss [rewrites [list_LUPDATE_0_CONS]];
val list_LUPDATE_APPEND = prove(``!xs ys zs.
      LENGTH xs = LENGTH ys ==> (list_LUPDATE xs 0 (ys ++ zs) = xs ++ zs)``,   Induct \\ Cases_on `ys` \\ fs [list_LUPDATE_def]);

open word_to_stackTheory wordsTheory wordPropsTheory;
val bits_to_word_SNOC = prove(``!bs b.
  bits_to_word (SNOC b bs) =
 (if b then 1w else 0w) ≪ (LENGTH bs) ‖ (bits_to_word bs)``,   Induct
  >> simp[Once $ oneline bits_to_word_def, bits_to_word_def]
  >> qpat_abbrev_tac `bits_to_word_bs = bits_to_word bs`
  >> simp[Once $ oneline bits_to_word_def, bits_to_word_def]
  >> rw[] >> simp[ADD1]);
val replay_drop = MATCH_MP DROP_list_LUPDATE (SPEC_ALL LESS_EQ_REFL) |> SIMP_RULE std_ss [];
val word_or_eq_0 = prove(``((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)``,   srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ metis_tac []);
val replay_not_nil = prove(``8 <= dimindex (:'a) ==>
    (list_LUPDATE (MAP Word (write_bitmap names k f')) 0 xs <>
     [Word (0w:'a word)])``,   Cases_on `xs` >- fs [list_LUPDATE_NIL]
  \\ full_simp_tac(srw_ss()) [write_bitmap_def,LET_DEF,Once word_list_def]
  \\ strip_tac \\ `~(dimindex (:'a) <= 1)` by decide_tac \\ fs []
  \\ IF_CASES_TAC \\ simp[list_LUPDATE_def]
  \\ simp[GSYM SNOC_APPEND,bits_to_word_SNOC,Excl "LIST_EQ_SIMP_CONV"]
  \\ simp[word_or_eq_0,EXP_EQ_0]
  \\ simp[word_1_lsl] \\simp[dimword_def]);
val replay_append = prove(``n1 + n2 + n3 <= LENGTH xs ==>
    ?xs2 xs3. (DROP n1 xs = xs2 ++ xs3) /\ n2 = LENGTH xs2``,   rpt strip_tac
  \\ `n1 <= LENGTH xs` by decide_tac
  \\ Q.PAT_X_ASSUM `n1 + n2 + n3 <= LENGTH xs` MP_TAC
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [DROP_LENGTH_APPEND]  \\ fs []
  \\ rename [‘n2 + (n3 + LENGTH xs1) ≤ LENGTH xs1 + LENGTH xs2’]
  \\ `n2 <= LENGTH xs2` by decide_tac
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [] \\ metis_tac []);
fun theorem_row label th = (if null(hyp th) then () else raise Fail "open replay premise"; print(label ^ "="); print_thm th; print "\n");
val _ = theorem_row "bf_full_drop" replay_drop;
val _ = theorem_row "bf_full_not_nil" replay_not_nil;
val _ = theorem_row "bf_full_append" replay_append;
val _ = (print "bf_not_nil_types="; app (fn v => (print_term v; print " : "; print_type (type_of v); print "\n")) (free_varsl [concl replay_not_nil]));
fun emit label q = (print(label ^ "="); print_thm (EVAL q); print "\n");
val _ = emit "bf_overwrite_8_0_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_0_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_0_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_6_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_6_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_6_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_7_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_7_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_7_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_8_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_8_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_8_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_63_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_63_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_63_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_64_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_64_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_64_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_80_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):8 word_loc list) 0 ([]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_80_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):8 word_loc list) 0 ([Word 0w]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_8_80_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):8 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:8 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_0_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_0_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_0_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_6_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_6_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_6_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_7_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_7_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_7_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_8_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_8_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_8_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_63_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_63_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_63_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_64_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_64_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_64_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_80_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):64 word_loc list) 0 ([]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_80_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):64 word_loc list) 0 ([Word 0w]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_64_80_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):64 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:64 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_0_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_0_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_0_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 0):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_6_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_6_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_6_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 6):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_7_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_7_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_7_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 7):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_8_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_8_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_8_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 8):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_63_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_63_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_63_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 63):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_64_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_64_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_64_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 64):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_80_0" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):80 word_loc list) 0 ([]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_80_1" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):80 word_loc list) 0 ([Word 0w]:80 word_loc list) <> [Word 0w]``;
val _ = emit "bf_overwrite_80_80_2" ``list_LUPDATE (MAP Word (write_bitmap (fromAList [(2,());(4,())]) 1 80):80 word_loc list) 0 ([Loc 17 19; Word 0w; Loc 3 4]:80 word_loc list) <> [Word 0w]``;
