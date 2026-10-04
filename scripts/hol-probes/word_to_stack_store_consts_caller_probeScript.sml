load "preamble";
load "word_to_stackTheory";
open HolKernel Parse bossLib preamble word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th =
  let val full = GEN_ALL th in
    if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
    print(label ^ "=" ^ term_to_string(concl full) ^ "\n")
  end;
val clauses = List.filter
  (fn th => String.isSubstring "StoreConsts" (term_to_string (concl th)))
  (CONJUNCTS comp_def);
val _ = if List.length clauses = 1 then () else raise Fail "StoreConsts clause count";
val _ = emit "source_clause" (hd clauses);
val _ = emit "below8" (EVAL ``comp (ARB:8 asm_config) F
  (StoreConsts 9 10 11 12 [(T,255w);(F,1w)]) (List [4w],255) (22,0,0)``);
val _ = emit "wrap8" (EVAL ``comp (ARB:8 asm_config) F
  (StoreConsts 9 10 11 12 [(T,255w);(F,1w)]) (List [4w],256) (22,0,0)``);
val _ = emit "wrap64" (EVAL ``comp (ARB:64 asm_config) F
  (StoreConsts 9 10 11 12 [(T,255w);(F,1w)])
  (List [4w],18446744073709551616) (22,0,0)``);
val _ = emit "exact_chunk8" (EVAL ``comp (ARB:8 asm_config) F
  (StoreConsts 9 10 11 12 (REPLICATE 7 (T,255w))) (List [4w],0) (22,0,0)``);
val _ = emit "width1" (EVAL ``comp (ARB:1 asm_config) F
  (StoreConsts 9 10 11 12 [(T,1w);(F,0w)]) (List [4w],2) (22,0,0)``);
val _ = emit "index_below8" (EVAL ``w2n (255w:8 word)``);
val _ = emit "index_wrap8" (EVAL ``w2n (256w:8 word)``);
val _ = emit "index_wrap64" (EVAL ``w2n (18446744073709551616w:64 word)``);
