load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "lim_safe_part=" dataSemTheory.lim_safe_part_def;
val _ = show "lim_safe=" dataSemTheory.lim_safe_def;
val _ = show "ref_array_inside=" (EVAL ``dataSem$lim_safe
  ((l:dataSem$limits) with <|arch_64_bit := T; length_limit := 3|>)
  (closLang$MemOp closLang$RefArray) [dataSem$Number 7; dataSem$Number 0]``);
val _ = show "ref_array_boundary=" (EVAL ``dataSem$lim_safe
  ((l:dataSem$limits) with <|arch_64_bit := T; length_limit := 3|>)
  (closLang$MemOp closLang$RefArray) [dataSem$Number 8; dataSem$Number 0]``);
val _ = show "ref_array_negative=" (EVAL ``dataSem$lim_safe
  ((l:dataSem$limits) with <|arch_64_bit := T; length_limit := 3|>)
  (closLang$MemOp closLang$RefArray) [dataSem$Number (-1); dataSem$Number 0]``);
val _ = show "ref_array_malformed=" (EVAL ``dataSem$lim_safe
  ((l:dataSem$limits) with <|arch_64_bit := T; length_limit := 3|>)
  (closLang$MemOp closLang$RefArray) [dataSem$Number (-1)]``);
val _ = show "nullary_tag_boundary=" (EVAL ``dataSem$lim_safe
  ((l:dataSem$limits) with <|arch_64_bit := T; length_limit := 3|>)
  (closLang$BlockOp (closLang$Cons (2 ** 60))) []``);
