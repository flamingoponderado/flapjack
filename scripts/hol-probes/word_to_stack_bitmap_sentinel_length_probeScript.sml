load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory wordsTheory stackSemTheory;
val _ = Globals.linewidth := 2000;
val bits_to_word_bit = prove(``  !bs i.
      i < dimindex (:'a) /\ i < LENGTH bs ==>
      ((bits_to_word bs:'a word) ' i = EL i bs)``,   Induct \\ fs [] \\ Cases_on `i` \\ fs []
  \\ Cases \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);
val _ = (if null(hyp bits_to_word_bit) then () else raise Fail "open source premise"; print "sl_source_bits_to_word_bit="; print_thm bits_to_word_bit; print "\n");
val bits_to_word_miss = prove(``  !bs i.
      i < dimindex (:'a) /\ LENGTH bs <= i ==>
      ~((bits_to_word bs:'a word) ' i)``,   Induct \\ fs [] THEN1 (EVAL_TAC \\ fs [word_0])
  \\ Cases_on `i` \\ fs [] \\ NTAC 2 strip_tac
  \\ `n < dimindex (:'a)` by decide_tac \\ res_tac
  \\ Cases_on `h` \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);
val _ = (if null(hyp bits_to_word_miss) then () else raise Fail "open source premise"; print "sl_source_bits_to_word_miss="; print_thm bits_to_word_miss; print "\n");
val shift_shift_lemma = prove(``  ~(word_msb w) ==> (w ≪ 1 ⋙ 1 = w)``,   srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ Cases_on `i + 1 < dimindex (:α)`
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [NOT_LESS]
  \\ `i = dimindex (:'a) - 1` by decide_tac
  \\ simp []);
val _ = (if null(hyp shift_shift_lemma) then () else raise Fail "open source premise"; print "sl_source_shift_shift_lemma="; print_thm shift_shift_lemma; print "\n");
val word_or_eq_0 = prove(``  ((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)``,   srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ metis_tac []);
val _ = (if null(hyp word_or_eq_0) then () else raise Fail "open source premise"; print "sl_source_word_or_eq_0="; print_thm word_or_eq_0; print "\n");
val GENLIST_bits_to_word_alt = prove(``  LENGTH (xs ++ ys) <= dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (xs ++ ys):'a word) ' i) (LENGTH xs) = xs``,   fs[Cong GENLIST_CONG,bits_to_word_bit,EL_APPEND1] >>
  fs[GENLIST_EL_MAP]);
val _ = (if null(hyp GENLIST_bits_to_word_alt) then () else raise Fail "open source premise"; print "sl_source_GENLIST_bits_to_word_alt="; print_thm GENLIST_bits_to_word_alt; print "\n");
val bit_length_bits_to_word = prove(``  !qs.
      LENGTH qs + 1 < dimindex (:'a) ==>
      bit_length (bits_to_word (qs ++ [T]):'a word) = LENGTH qs + 1``,   Induct THEN1
   (fs [] \\ fs [Once bit_length_def] \\ fs [Once bit_length_def]
    \\ fs [bits_to_word_def] \\ EVAL_TAC)
  \\ Cases \\ fs [bits_to_word_def]
  \\ once_rewrite_tac [bit_length_def]
  \\ fs [ADD_CLAUSES]
  \\ rpt strip_tac \\ fs [EVAL ``1w >>> 1``]
  \\ `(LENGTH qs + 1) < dimindex (:'a)` by decide_tac \\ fs []
  \\ `bits_to_word (qs ++ [T]) << 1 <> 0w` by
   (fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,word_0,word_lsl_def]
    \\ Q.EXISTS_TAC `LENGTH qs + 1`
    \\ fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fs []
    \\ fs [EL_LENGTH_APPEND] \\ decide_tac)
  \\ `bits_to_word (qs ++ [T]) ≪ 1 ⋙ 1 =
      bits_to_word (qs ++ [T]):'a word` by
   (match_mp_tac shift_shift_lemma \\ fs [word_msb_def]
    \\ match_mp_tac bits_to_word_miss \\ fs [] \\ decide_tac)
  \\ fs [ADD1,word_or_eq_0]);
val _ = (if null(hyp bit_length_bits_to_word) then () else raise Fail "open source premise"; print "sl_source_bit_length_bits_to_word="; print_thm bit_length_bits_to_word; print "\n");
val GENLIST_bits_to_word = prove(``  LENGTH qs' + 1 < dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (qs' ++ [T]):'a word) ' i) (LENGTH qs') = qs'``,   fs[GENLIST_bits_to_word_alt]);
val _ = (if null(hyp GENLIST_bits_to_word) then () else raise Fail "open source premise"; print "sl_source_GENLIST_bits_to_word="; print_thm GENLIST_bits_to_word; print "\n");
fun emit label q = let val th = EVAL q in print(label ^ "="); print_thm th; print "\n" end;
val _ = emit "sl_length_0_2" ``bit_length (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_prefix_0_2" ``GENLIST (\i. (bits_to_word ([] ++ [T]):2 word) ' i) 0 = []``;
val _ = emit "sl_value_0_2" ``w2n (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_length_5_2" ``bit_length (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_prefix_5_2" ``GENLIST (\i. (bits_to_word ([] ++ [T]):2 word) ' i) 0 = []``;
val _ = emit "sl_value_5_2" ``w2n (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_length_6_2" ``bit_length (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_prefix_6_2" ``GENLIST (\i. (bits_to_word ([] ++ [T]):2 word) ' i) 0 = []``;
val _ = emit "sl_value_6_2" ``w2n (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_length_7_2" ``bit_length (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_prefix_7_2" ``GENLIST (\i. (bits_to_word ([] ++ [T]):2 word) ' i) 0 = []``;
val _ = emit "sl_value_7_2" ``w2n (bits_to_word ([] ++ [T]):2 word)``;
val _ = emit "sl_length_0_8" ``bit_length (bits_to_word ([] ++ [T]):8 word)``;
val _ = emit "sl_prefix_0_8" ``GENLIST (\i. (bits_to_word ([] ++ [T]):8 word) ' i) 0 = []``;
val _ = emit "sl_value_0_8" ``w2n (bits_to_word ([] ++ [T]):8 word)``;
val _ = emit "sl_length_1_8" ``bit_length (bits_to_word ([F] ++ [T]):8 word)``;
val _ = emit "sl_prefix_1_8" ``GENLIST (\i. (bits_to_word ([F] ++ [T]):8 word) ' i) 1 = [F]``;
val _ = emit "sl_value_1_8" ``w2n (bits_to_word ([F] ++ [T]):8 word)``;
val _ = emit "sl_length_2_8" ``bit_length (bits_to_word ([T] ++ [T]):8 word)``;
val _ = emit "sl_prefix_2_8" ``GENLIST (\i. (bits_to_word ([T] ++ [T]):8 word) ' i) 1 = [T]``;
val _ = emit "sl_value_2_8" ``w2n (bits_to_word ([T] ++ [T]):8 word)``;
val _ = emit "sl_length_3_8" ``bit_length (bits_to_word ([T;F;T] ++ [T]):8 word)``;
val _ = emit "sl_prefix_3_8" ``GENLIST (\i. (bits_to_word ([T;F;T] ++ [T]):8 word) ' i) 3 = [T;F;T]``;
val _ = emit "sl_value_3_8" ``w2n (bits_to_word ([T;F;T] ++ [T]):8 word)``;
val _ = emit "sl_length_4_8" ``bit_length (bits_to_word ([F;T;F;T] ++ [T]):8 word)``;
val _ = emit "sl_prefix_4_8" ``GENLIST (\i. (bits_to_word ([F;T;F;T] ++ [T]):8 word) ' i) 4 = [F;T;F;T]``;
val _ = emit "sl_value_4_8" ``w2n (bits_to_word ([F;T;F;T] ++ [T]):8 word)``;
val _ = emit "sl_length_5_8" ``bit_length (bits_to_word ([F;F;F;F;F;F] ++ [T]):8 word)``;
val _ = emit "sl_prefix_5_8" ``GENLIST (\i. (bits_to_word ([F;F;F;F;F;F] ++ [T]):8 word) ' i) 6 = [F;F;F;F;F;F]``;
val _ = emit "sl_value_5_8" ``w2n (bits_to_word ([F;F;F;F;F;F] ++ [T]):8 word)``;
val _ = emit "sl_length_6_8" ``bit_length (bits_to_word ([T;T;T;T;T;T] ++ [T]):8 word)``;
val _ = emit "sl_prefix_6_8" ``GENLIST (\i. (bits_to_word ([T;T;T;T;T;T] ++ [T]):8 word) ' i) 6 = [T;T;T;T;T;T]``;
val _ = emit "sl_value_6_8" ``w2n (bits_to_word ([T;T;T;T;T;T] ++ [T]):8 word)``;
val _ = emit "sl_length_7_8" ``bit_length (bits_to_word ([T;F;T;F;T;F] ++ [T]):8 word)``;
val _ = emit "sl_prefix_7_8" ``GENLIST (\i. (bits_to_word ([T;F;T;F;T;F] ++ [T]):8 word) ' i) 6 = [T;F;T;F;T;F]``;
val _ = emit "sl_value_7_8" ``w2n (bits_to_word ([T;F;T;F;T;F] ++ [T]):8 word)``;
val _ = emit "sl_length_0_64" ``bit_length (bits_to_word ([] ++ [T]):64 word)``;
val _ = emit "sl_prefix_0_64" ``GENLIST (\i. (bits_to_word ([] ++ [T]):64 word) ' i) 0 = []``;
val _ = emit "sl_value_0_64" ``w2n (bits_to_word ([] ++ [T]):64 word)``;
val _ = emit "sl_length_1_64" ``bit_length (bits_to_word ([F] ++ [T]):64 word)``;
val _ = emit "sl_prefix_1_64" ``GENLIST (\i. (bits_to_word ([F] ++ [T]):64 word) ' i) 1 = [F]``;
val _ = emit "sl_value_1_64" ``w2n (bits_to_word ([F] ++ [T]):64 word)``;
val _ = emit "sl_length_2_64" ``bit_length (bits_to_word ([T] ++ [T]):64 word)``;
val _ = emit "sl_prefix_2_64" ``GENLIST (\i. (bits_to_word ([T] ++ [T]):64 word) ' i) 1 = [T]``;
val _ = emit "sl_value_2_64" ``w2n (bits_to_word ([T] ++ [T]):64 word)``;
val _ = emit "sl_length_3_64" ``bit_length (bits_to_word ([T;F;T] ++ [T]):64 word)``;
val _ = emit "sl_prefix_3_64" ``GENLIST (\i. (bits_to_word ([T;F;T] ++ [T]):64 word) ' i) 3 = [T;F;T]``;
val _ = emit "sl_value_3_64" ``w2n (bits_to_word ([T;F;T] ++ [T]):64 word)``;
val _ = emit "sl_length_4_64" ``bit_length (bits_to_word ([F;T;F;T] ++ [T]):64 word)``;
val _ = emit "sl_prefix_4_64" ``GENLIST (\i. (bits_to_word ([F;T;F;T] ++ [T]):64 word) ' i) 4 = [F;T;F;T]``;
val _ = emit "sl_value_4_64" ``w2n (bits_to_word ([F;T;F;T] ++ [T]):64 word)``;
val _ = emit "sl_length_5_64" ``bit_length (bits_to_word ([F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F] ++ [T]):64 word)``;
val _ = emit "sl_prefix_5_64" ``GENLIST (\i. (bits_to_word ([F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F] ++ [T]):64 word) ' i) 62 = [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "sl_value_5_64" ``w2n (bits_to_word ([F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F] ++ [T]):64 word)``;
val _ = emit "sl_length_6_64" ``bit_length (bits_to_word ([T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T] ++ [T]):64 word)``;
val _ = emit "sl_prefix_6_64" ``GENLIST (\i. (bits_to_word ([T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T] ++ [T]):64 word) ' i) 62 = [T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T]``;
val _ = emit "sl_value_6_64" ``w2n (bits_to_word ([T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T] ++ [T]):64 word)``;
val _ = emit "sl_length_7_64" ``bit_length (bits_to_word ([T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F] ++ [T]):64 word)``;
val _ = emit "sl_prefix_7_64" ``GENLIST (\i. (bits_to_word ([T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F] ++ [T]):64 word) ' i) 62 = [T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F]``;
val _ = emit "sl_value_7_64" ``w2n (bits_to_word ([T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F] ++ [T]):64 word)``;
val _ = emit "sl_length_0_80" ``bit_length (bits_to_word ([] ++ [T]):80 word)``;
val _ = emit "sl_prefix_0_80" ``GENLIST (\i. (bits_to_word ([] ++ [T]):80 word) ' i) 0 = []``;
val _ = emit "sl_value_0_80" ``w2n (bits_to_word ([] ++ [T]):80 word)``;
val _ = emit "sl_length_1_80" ``bit_length (bits_to_word ([F] ++ [T]):80 word)``;
val _ = emit "sl_prefix_1_80" ``GENLIST (\i. (bits_to_word ([F] ++ [T]):80 word) ' i) 1 = [F]``;
val _ = emit "sl_value_1_80" ``w2n (bits_to_word ([F] ++ [T]):80 word)``;
val _ = emit "sl_length_2_80" ``bit_length (bits_to_word ([T] ++ [T]):80 word)``;
val _ = emit "sl_prefix_2_80" ``GENLIST (\i. (bits_to_word ([T] ++ [T]):80 word) ' i) 1 = [T]``;
val _ = emit "sl_value_2_80" ``w2n (bits_to_word ([T] ++ [T]):80 word)``;
val _ = emit "sl_length_3_80" ``bit_length (bits_to_word ([T;F;T] ++ [T]):80 word)``;
val _ = emit "sl_prefix_3_80" ``GENLIST (\i. (bits_to_word ([T;F;T] ++ [T]):80 word) ' i) 3 = [T;F;T]``;
val _ = emit "sl_value_3_80" ``w2n (bits_to_word ([T;F;T] ++ [T]):80 word)``;
val _ = emit "sl_length_4_80" ``bit_length (bits_to_word ([F;T;F;T] ++ [T]):80 word)``;
val _ = emit "sl_prefix_4_80" ``GENLIST (\i. (bits_to_word ([F;T;F;T] ++ [T]):80 word) ' i) 4 = [F;T;F;T]``;
val _ = emit "sl_value_4_80" ``w2n (bits_to_word ([F;T;F;T] ++ [T]):80 word)``;
val _ = emit "sl_length_5_80" ``bit_length (bits_to_word ([F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F] ++ [T]):80 word)``;
val _ = emit "sl_prefix_5_80" ``GENLIST (\i. (bits_to_word ([F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F] ++ [T]):80 word) ' i) 78 = [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "sl_value_5_80" ``w2n (bits_to_word ([F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F] ++ [T]):80 word)``;
val _ = emit "sl_length_6_80" ``bit_length (bits_to_word ([T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T] ++ [T]):80 word)``;
val _ = emit "sl_prefix_6_80" ``GENLIST (\i. (bits_to_word ([T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T] ++ [T]):80 word) ' i) 78 = [T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T]``;
val _ = emit "sl_value_6_80" ``w2n (bits_to_word ([T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T;T] ++ [T]):80 word)``;
val _ = emit "sl_length_7_80" ``bit_length (bits_to_word ([T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F] ++ [T]):80 word)``;
val _ = emit "sl_prefix_7_80" ``GENLIST (\i. (bits_to_word ([T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F] ++ [T]):80 word) ' i) 78 = [T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F]``;
val _ = emit "sl_value_7_80" ``w2n (bits_to_word ([T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F;T;F] ++ [T]):80 word)``;
val _ = print ("sl_type_word=" ^ type_to_string(type_of ``bits_to_word (qs ++ [T]):80 word``) ^ "\n");
val _ = print ("sl_type_length=" ^ type_to_string(type_of ``bit_length (w:80 word)``) ^ "\n");
