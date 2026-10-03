load "binary_ieeeTheory";
open HolKernel Parse boolLib binary_ieeeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
val _ = capture "float_to_int_def" float_to_int_def;
val _ = capture "real_to_float_def" real_to_float_def;
