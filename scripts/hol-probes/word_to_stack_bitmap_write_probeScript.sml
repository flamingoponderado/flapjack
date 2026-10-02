load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory wordsTheory stackSemTheory;
val _ = Globals.linewidth := 16000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = numLib.temp_prefer_num();
val bits_to_word_bit = prove(``  !bs i.
      i < dimindex (:'a) /\ i < LENGTH bs ==>
      ((bits_to_word bs:'a word) ' i = EL i bs)``,   Induct \\ fs [] \\ Cases_on `i` \\ fs []
  \\ Cases \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);
val _ = (if null(hyp bits_to_word_bit) then () else raise Fail "open source premise"; print "bw_source_bits_to_word_bit="; print_thm bits_to_word_bit; print "\n");
val bits_to_word_miss = prove(``  !bs i.
      i < dimindex (:'a) /\ LENGTH bs <= i ==>
      ~((bits_to_word bs:'a word) ' i)``,   Induct \\ fs [] THEN1 (EVAL_TAC \\ fs [word_0])
  \\ Cases_on `i` \\ fs [] \\ NTAC 2 strip_tac
  \\ `n < dimindex (:'a)` by decide_tac \\ res_tac
  \\ Cases_on `h` \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);
val _ = (if null(hyp bits_to_word_miss) then () else raise Fail "open source premise"; print "bw_source_bits_to_word_miss="; print_thm bits_to_word_miss; print "\n");
val shift_shift_lemma = prove(``  ~(word_msb w) ==> (w ≪ 1 ⋙ 1 = w)``,   srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ Cases_on `i + 1 < dimindex (:α)`
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [NOT_LESS]
  \\ `i = dimindex (:'a) - 1` by decide_tac
  \\ simp []);
val _ = (if null(hyp shift_shift_lemma) then () else raise Fail "open source premise"; print "bw_source_shift_shift_lemma="; print_thm shift_shift_lemma; print "\n");
val word_or_eq_0 = prove(``  ((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)``,   srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ metis_tac []);
val _ = (if null(hyp word_or_eq_0) then () else raise Fail "open source premise"; print "bw_source_word_or_eq_0="; print_thm word_or_eq_0; print "\n");
val GENLIST_bits_to_word_alt = prove(``  LENGTH (xs ++ ys) <= dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (xs ++ ys):'a word) ' i) (LENGTH xs) = xs``,   fs[Cong GENLIST_CONG,bits_to_word_bit,EL_APPEND1] >>
  fs[GENLIST_EL_MAP]);
val _ = (if null(hyp GENLIST_bits_to_word_alt) then () else raise Fail "open source premise"; print "bw_source_GENLIST_bits_to_word_alt="; print_thm GENLIST_bits_to_word_alt; print "\n");
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
val _ = (if null(hyp bit_length_bits_to_word) then () else raise Fail "open source premise"; print "bw_source_bit_length_bits_to_word="; print_thm bit_length_bits_to_word; print "\n");
val GENLIST_bits_to_word = prove(``  LENGTH qs' + 1 < dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (qs' ++ [T]):'a word) ' i) (LENGTH qs') = qs'``,   fs[GENLIST_bits_to_word_alt]);
val _ = (if null(hyp GENLIST_bits_to_word) then () else raise Fail "open source premise"; print "bw_source_GENLIST_bits_to_word="; print_thm GENLIST_bits_to_word; print "\n");
val read_bitmap_word_list = prove(``  8 <= dimindex (:'a) ==>
    read_bitmap
      ((word_list (qs ++ [T]) (dimindex (:'a) - 1)) ++ (xs:'a word list)) =
    SOME qs``,   completeInduct_on `LENGTH (qs:bool list)` \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rw [] \\ once_rewrite_tac [word_list_def]
  \\ `dimindex (:'a) - 1 <> 0` by decide_tac \\ fs []
  \\ Cases_on `LENGTH qs + 1 <= dimindex (:'a) - 1` \\ fs []
  THEN1
   (fs [read_bitmap_def]
    \\ `~word_msb (bits_to_word (qs ++ [T]))` by
     (fs [word_msb_def] \\ match_mp_tac bits_to_word_miss
      \\ fs [] \\ decide_tac) \\ fs []
    \\ `LENGTH qs + 1 < dimindex (:'a)` by decide_tac
    \\ fs [bit_length_bits_to_word,GENLIST_bits_to_word])
  \\ fs [read_bitmap_def]
  \\ `dimindex (:'a) - 1 =
        LENGTH (TAKE (dimindex (:'a) - 1) (qs ++ [T]))` by
    (fs [LENGTH_TAKE_EQ,MIN_DEF] \\ decide_tac)
  \\ `word_msb (bits_to_word (TAKE (dimindex (:'a) - 1)
         (qs ++ [T]) ++ [T]) :'a word)` by
   (fsrw_tac[] [word_msb_def]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fsrw_tac[] []
    \\ reverse (rpt strip_tac) THEN1 decide_tac THEN1 decide_tac
    \\ pop_assum (fn th => simp_tac std_ss [Once th])
    \\ fsrw_tac[] [EL_LENGTH_APPEND]) \\ fs []
  \\ `DROP (dimindex (:'a) - 1) (qs ++ [T]) =
      DROP (dimindex (:'a) - 1) qs ++ [T]` by
   (match_mp_tac DROP_APPEND1 \\ fs [NOT_LESS] \\ decide_tac)
  \\ `TAKE (dimindex (:'a) - 1) (qs ++ [T]) =
      TAKE (dimindex (:'a) - 1) qs` by
   (match_mp_tac TAKE_APPEND1 \\ fs [NOT_LESS] \\ decide_tac) \\ fs []
  \\ first_x_assum (mp_tac o Q.SPEC `DROP (dimindex (:'a) - 1) qs`)
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [LENGTH_DROP] \\ decide_tac)
  \\ rpt strip_tac \\ fs []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV
        [GSYM (Q.SPEC `dimindex (:'a) - 1`
          (INST_TYPE [``:'a``|->``:bool``] TAKE_DROP))]))
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ Q.ABBREV_TAC `ts = TAKE (dimindex (:'a) - 1) qs` \\ fs []
  \\ match_mp_tac GENLIST_bits_to_word_alt \\ fs []);
val _ = (if null(hyp read_bitmap_word_list) then () else raise Fail "open source premise"; print "bw_source_read_bitmap_word_list="; print_thm read_bitmap_word_list; print "\n");
val read_bitmap_write_bitmap = prove(``   8 ≤ dimindex (:α) ⇒
   read_bitmap ((write_bitmap names k f'):α word list) =
   SOME (GENLIST (λx. MEM x (MAP (λ(r,y). f' - 1 - (r DIV 2 - k)) (toAList names))) f')``,   rw[write_bitmap_def]
  \\ imp_res_tac read_bitmap_word_list
  \\ first_x_assum(qspec_then`[]`mp_tac)
  \\ simp[]);
val _ = (if null(hyp read_bitmap_write_bitmap) then () else raise Fail "open premise"; print "bw_full="; print_thm read_bitmap_write_bitmap; print "\n");
fun emit label q = let val th = EVAL q in print(label ^ "="); print_thm th; print "\n" end;
val _ = emit "bw_decode_0_0_0_8" ``read_bitmap (write_bitmap (fromAList []) 0 0:8 word list) = SOME []``;
val _ = emit "bw_decode_0_0_1_8" ``read_bitmap (write_bitmap (fromAList []) 2 0:8 word list) = SOME []``;
val _ = emit "bw_decode_0_0_2_8" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 0:8 word list) = SOME []``;
val _ = emit "bw_decode_0_1_0_8" ``read_bitmap (write_bitmap (fromAList []) 0 1:8 word list) = SOME [F]``;
val _ = emit "bw_decode_0_1_1_8" ``read_bitmap (write_bitmap (fromAList []) 2 1:8 word list) = SOME [F]``;
val _ = emit "bw_decode_0_1_2_8" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 1:8 word list) = SOME [F]``;
val _ = emit "bw_decode_0_2_0_8" ``read_bitmap (write_bitmap (fromAList []) 0 7:8 word list) = SOME [F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_2_1_8" ``read_bitmap (write_bitmap (fromAList []) 2 7:8 word list) = SOME [F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_2_2_8" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 7:8 word list) = SOME [F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_0_8" ``read_bitmap (write_bitmap (fromAList []) 0 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_1_8" ``read_bitmap (write_bitmap (fromAList []) 2 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_2_8" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_1_0_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 0:8 word list) = SOME []``;
val _ = emit "bw_decode_1_0_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 0:8 word list) = SOME []``;
val _ = emit "bw_decode_1_0_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 0:8 word list) = SOME []``;
val _ = emit "bw_decode_1_1_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_1_1_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_1_1_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_1_2_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_2_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_2_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_0_0_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 0:8 word list) = SOME []``;
val _ = emit "bw_decode_2_0_1_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 0:8 word list) = SOME []``;
val _ = emit "bw_decode_2_0_2_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 0:8 word list) = SOME []``;
val _ = emit "bw_decode_2_1_0_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_2_1_1_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_2_1_2_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_2_2_0_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 7:8 word list) = SOME [F;F;F;F;T;T;F]``;
val _ = emit "bw_decode_2_2_1_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_2_2_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_3_0_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T;F]``;
val _ = emit "bw_decode_2_3_1_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_3_2_8" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_0_0_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 0:8 word list) = SOME []``;
val _ = emit "bw_decode_3_0_1_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 0:8 word list) = SOME []``;
val _ = emit "bw_decode_3_0_2_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 0:8 word list) = SOME []``;
val _ = emit "bw_decode_3_1_0_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_3_1_1_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_3_1_2_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_3_2_0_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 7:8 word list) = SOME [T;F;F;F;F;T;T]``;
val _ = emit "bw_decode_3_2_1_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 7:8 word list) = SOME [T;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_2_2_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_3_0_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 17:8 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_3_3_1_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 17:8 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_3_2_8" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_0_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 0:8 word list) = SOME []``;
val _ = emit "bw_decode_4_0_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 0:8 word list) = SOME []``;
val _ = emit "bw_decode_4_0_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 0:8 word list) = SOME []``;
val _ = emit "bw_decode_4_1_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_4_1_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_4_1_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_4_2_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 7:8 word list) = SOME [F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_4_2_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_2_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_3_0_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_4_3_1_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_3_2_8" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_5_0_0_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 0:8 word list) = SOME []``;
val _ = emit "bw_decode_5_0_1_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 0:8 word list) = SOME []``;
val _ = emit "bw_decode_5_0_2_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 0:8 word list) = SOME []``;
val _ = emit "bw_decode_5_1_0_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_5_1_1_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_5_1_2_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 1:8 word list) = SOME [T]``;
val _ = emit "bw_decode_5_2_0_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 7:8 word list) = SOME [T;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_2_1_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 7:8 word list) = SOME [T;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_2_2_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 7:8 word list) = SOME [F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_5_3_0_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 17:8 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_3_1_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 17:8 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_3_2_8" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 17:8 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_0_0_0_64" ``read_bitmap (write_bitmap (fromAList []) 0 0:64 word list) = SOME []``;
val _ = emit "bw_decode_0_0_1_64" ``read_bitmap (write_bitmap (fromAList []) 2 0:64 word list) = SOME []``;
val _ = emit "bw_decode_0_0_2_64" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 0:64 word list) = SOME []``;
val _ = emit "bw_decode_0_1_0_64" ``read_bitmap (write_bitmap (fromAList []) 0 1:64 word list) = SOME [F]``;
val _ = emit "bw_decode_0_1_1_64" ``read_bitmap (write_bitmap (fromAList []) 2 1:64 word list) = SOME [F]``;
val _ = emit "bw_decode_0_1_2_64" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 1:64 word list) = SOME [F]``;
val _ = emit "bw_decode_0_2_0_64" ``read_bitmap (write_bitmap (fromAList []) 0 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_2_1_64" ``read_bitmap (write_bitmap (fromAList []) 2 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_2_2_64" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_0_64" ``read_bitmap (write_bitmap (fromAList []) 0 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_1_64" ``read_bitmap (write_bitmap (fromAList []) 2 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_2_64" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_1_0_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 0:64 word list) = SOME []``;
val _ = emit "bw_decode_1_0_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 0:64 word list) = SOME []``;
val _ = emit "bw_decode_1_0_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 0:64 word list) = SOME []``;
val _ = emit "bw_decode_1_1_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_1_1_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_1_1_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_1_2_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_2_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_2_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_0_0_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 0:64 word list) = SOME []``;
val _ = emit "bw_decode_2_0_1_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 0:64 word list) = SOME []``;
val _ = emit "bw_decode_2_0_2_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 0:64 word list) = SOME []``;
val _ = emit "bw_decode_2_1_0_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_2_1_1_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_2_1_2_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_2_2_0_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T;F]``;
val _ = emit "bw_decode_2_2_1_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_2_2_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_3_0_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T;F]``;
val _ = emit "bw_decode_2_3_1_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_3_2_64" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_0_0_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 0:64 word list) = SOME []``;
val _ = emit "bw_decode_3_0_1_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 0:64 word list) = SOME []``;
val _ = emit "bw_decode_3_0_2_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 0:64 word list) = SOME []``;
val _ = emit "bw_decode_3_1_0_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_3_1_1_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_3_1_2_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_3_2_0_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 63:64 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_3_2_1_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 63:64 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_2_2_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_3_0_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_3_3_1_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_3_2_64" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_0_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 0:64 word list) = SOME []``;
val _ = emit "bw_decode_4_0_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 0:64 word list) = SOME []``;
val _ = emit "bw_decode_4_0_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 0:64 word list) = SOME []``;
val _ = emit "bw_decode_4_1_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_4_1_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_4_1_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_4_2_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_4_2_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_2_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_3_0_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_4_3_1_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_3_2_64" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_5_0_0_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 0:64 word list) = SOME []``;
val _ = emit "bw_decode_5_0_1_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 0:64 word list) = SOME []``;
val _ = emit "bw_decode_5_0_2_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 0:64 word list) = SOME []``;
val _ = emit "bw_decode_5_1_0_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_5_1_1_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_5_1_2_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 1:64 word list) = SOME [T]``;
val _ = emit "bw_decode_5_2_0_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 63:64 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_2_1_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 63:64 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_2_2_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 63:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_5_3_0_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 129:64 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_3_1_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 129:64 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_3_2_64" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 129:64 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_0_0_0_80" ``read_bitmap (write_bitmap (fromAList []) 0 0:80 word list) = SOME []``;
val _ = emit "bw_decode_0_0_1_80" ``read_bitmap (write_bitmap (fromAList []) 2 0:80 word list) = SOME []``;
val _ = emit "bw_decode_0_0_2_80" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 0:80 word list) = SOME []``;
val _ = emit "bw_decode_0_1_0_80" ``read_bitmap (write_bitmap (fromAList []) 0 1:80 word list) = SOME [F]``;
val _ = emit "bw_decode_0_1_1_80" ``read_bitmap (write_bitmap (fromAList []) 2 1:80 word list) = SOME [F]``;
val _ = emit "bw_decode_0_1_2_80" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 1:80 word list) = SOME [F]``;
val _ = emit "bw_decode_0_2_0_80" ``read_bitmap (write_bitmap (fromAList []) 0 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_2_1_80" ``read_bitmap (write_bitmap (fromAList []) 2 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_2_2_80" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_0_80" ``read_bitmap (write_bitmap (fromAList []) 0 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_1_80" ``read_bitmap (write_bitmap (fromAList []) 2 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_0_3_2_80" ``read_bitmap (write_bitmap (fromAList []) 1208925819614629174706176 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_1_0_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 0:80 word list) = SOME []``;
val _ = emit "bw_decode_1_0_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 0:80 word list) = SOME []``;
val _ = emit "bw_decode_1_0_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 0:80 word list) = SOME []``;
val _ = emit "bw_decode_1_1_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_1_1_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_1_1_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_1_2_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_2_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_2_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 0 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 2 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_1_3_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,0:num)]) 1208925819614629174706176 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_0_0_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 0:80 word list) = SOME []``;
val _ = emit "bw_decode_2_0_1_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 0:80 word list) = SOME []``;
val _ = emit "bw_decode_2_0_2_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 0:80 word list) = SOME []``;
val _ = emit "bw_decode_2_1_0_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_2_1_1_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_2_1_2_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_2_2_0_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T;F]``;
val _ = emit "bw_decode_2_2_1_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_2_2_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_3_0_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 0 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T;F]``;
val _ = emit "bw_decode_2_3_1_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 2 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_2_3_2_80" ``read_bitmap (write_bitmap (fromAList [(2:num,7:num);(4:num,9:num)]) 1208925819614629174706176 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_0_0_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 0:80 word list) = SOME []``;
val _ = emit "bw_decode_3_0_1_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 0:80 word list) = SOME []``;
val _ = emit "bw_decode_3_0_2_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 0:80 word list) = SOME []``;
val _ = emit "bw_decode_3_1_0_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_3_1_1_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_3_1_2_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_3_2_0_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_3_2_1_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_2_2_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_3_0_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 0 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_3_3_1_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 2 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_3_3_2_80" ``read_bitmap (write_bitmap (fromAList [(1:num,10:num);(2:num,11:num);(130:num,12:num)]) 1208925819614629174706176 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_0_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 0:80 word list) = SOME []``;
val _ = emit "bw_decode_4_0_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 0:80 word list) = SOME []``;
val _ = emit "bw_decode_4_0_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 0:80 word list) = SOME []``;
val _ = emit "bw_decode_4_1_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_4_1_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_4_1_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_4_2_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_4_2_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_2_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_3_0_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 0 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T;T]``;
val _ = emit "bw_decode_4_3_1_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 2 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_4_3_2_80" ``read_bitmap (write_bitmap (fromAList [(0:num,1:num);(0:num,99:num);(2:num,3:num)]) 1208925819614629174706176 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_5_0_0_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 0:80 word list) = SOME []``;
val _ = emit "bw_decode_5_0_1_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 0:80 word list) = SOME []``;
val _ = emit "bw_decode_5_0_2_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 0:80 word list) = SOME []``;
val _ = emit "bw_decode_5_1_0_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_5_1_1_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_5_1_2_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 1:80 word list) = SOME [T]``;
val _ = emit "bw_decode_5_2_0_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 79:80 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_2_1_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 79:80 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_2_2_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 79:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = emit "bw_decode_5_3_0_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 0 161:80 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_3_1_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 2 161:80 word list) = SOME [T;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F]``;
val _ = emit "bw_decode_5_3_2_80" ``read_bitmap (write_bitmap (fromAList [(1208925819614629174706176:num,5:num);(1208925819614629174706178:num,8:num)]) 1208925819614629174706176 161:80 word list) = SOME [F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;F;T]``;
val _ = print ("bw_type_names=" ^ type_to_string(type_of ``names:num num_map``) ^ "\n");
val _ = print ("bw_type_output=" ^ type_to_string(type_of ``write_bitmap (names:num num_map) k f:80 word list``) ^ "\n");
