load "binary_ieeeTheory";
open HolKernel Parse boolLib binary_ieeeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
val _ = capture "real_to_float_def" real_to_float_def;
val _ = capture "real_to_float_with_flags_def" real_to_float_with_flags_def;
val _ = capture "float_sqrt_def" float_sqrt_def;
