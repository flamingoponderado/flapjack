(* Original wordSem inst_def Div signed-quotient audit, bead .18.5.10.1.
   wordSemScript729-736 uses word / = wordsTheory.word_quot, not //.
   Observe original evaluator projections over a free width8 state. *)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib HolKernel Parse preamble wordSemTheory;
fun print_eval label q =
  (print (label ^ "="); print_term (rhs (concl (EVAL q))); print "\n");
val s = ``s:(8,'c,'ffi) wordSem$state``;
fun pd label a b dest left right =
  let val st = ``^s with locals := fromAList [(2,Word ^a);(3,Word ^b)]`` in
    print_eval label
      ``OPTION_MAP (\t:(8,'c,'ffi) wordSem$state.
          MAP (\k. lookup k t.locals) [1;2;3])
        (inst (Arith (Div ^dest ^left ^right)) ^st)``
  end;
val _ = pd "positive" ``17w:word8`` ``5w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "negative_small" ``250w:word8`` ``10w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "negative_dividend" ``239w:word8`` ``5w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "negative_divisor" ``17w:word8`` ``251w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "both_negative" ``239w:word8`` ``251w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "min_overflow" ``128w:word8`` ``255w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "min_half" ``128w:word8`` ``2w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "positive_minus_one" ``127w:word8`` ``255w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "zero_divisor" ``239w:word8`` ``0w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "zero_dividend" ``0w:word8`` ``251w:word8`` ``1:num`` ``2:num`` ``3:num``;
val _ = pd "alias_dividend" ``239w:word8`` ``5w:word8`` ``2:num`` ``2:num`` ``3:num``;
val _ = pd "alias_divisor" ``239w:word8`` ``5w:word8`` ``3:num`` ``2:num`` ``3:num``;
val _ = pd "same_source" ``239w:word8`` ``5w:word8`` ``1:num`` ``2:num`` ``2:num``;
val _ = print_eval "missing_dividend"
  ``inst (Arith (Div 1 2 3)) (^s with locals := fromAList [(3,Word 5w)]) = NONE``;
val _ = print_eval "location_divisor"
  ``inst (Arith (Div 1 2 3)) (^s with locals := fromAList [(2,Word 239w);(3,Loc 4 5)]) = NONE``;
val s64 = ``s64:(64,'c,'ffi) wordSem$state``;
val _ = print_eval "min64_overflow"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. lookup 1 t.locals)
    (inst (Arith (Div 1 2 3)) (^s64 with locals := fromAList
      [(2,Word 0x8000000000000000w);(3,Word 0xFFFFFFFFFFFFFFFFw)]))``;
val s1 = ``s1:(1,'c,'ffi) wordSem$state``;
val _ = print_eval "min1_overflow"
  ``OPTION_MAP (\t:(1,'c,'ffi) wordSem$state. lookup 1 t.locals)
    (inst (Arith (Div 1 2 3)) (^s1 with locals := fromAList [(2,Word 1w);(3,Word 1w)]))``;
