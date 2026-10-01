load "bossLib";
load "preamble";
load "miscTheory";
open bossLib HolKernel Parse preamble miscTheory;
fun observe label left right target offset =
  let val tm = ``(find_index ^target (^left ++ ^right) ^offset,
    case find_index ^target ^left ^offset of
      NONE => find_index ^target ^right (^offset + LENGTH ^left)
    | SOME i => SOME i)``;
      val th = EVAL tm
  in print(label ^ "="); print_term(rhs(concl th)); print "\n" end;
val _ = observe "fia_empty" ``[]:num list`` ``[]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_empty_left" ``[]:num list`` ``[1;2]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_empty_right" ``[1;2]:num list`` ``[]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_left_head" ``[2;1]:num list`` ``[2]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_duplicates" ``[1;2;2]:num list`` ``[2]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_right_last" ``[1;3]:num list`` ``[4;2]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_absent" ``[1;3]:num list`` ``[4;5]:num list`` ``2:num`` ``7:num``;
val _ = observe "fia_zero" ``[1;3]:num list`` ``[2]:num list`` ``2:num`` ``0:num``;
val _ = observe "fia_bool" ``[F]:bool list`` ``[F;T]:bool list`` ``T`` ``9:num``;
val _ = observe "fia_large" ``[1]:num list`` ``[3;2]:num list`` ``2:num`` ``100000000000000000000:num``;
