load "preamble";
load "word_allocTheory";
open HolKernel Parse bossLib preamble word_allocTheory sptreeTheory;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "rename_empty" ``let (ns,t,n) = list_next_var_rename [] (fromAList [(9,99)]) 5 in (ns,MAP (\k.THE(lookup k t)) [],MAP (\k.lookup k t) [0;1;2;9],n)``;
val _ = out "rename_overwrite" ``let (ns,t,n) = list_next_var_rename [1;2] (fromAList [(9,99);(1,88)]) 5 in (ns,MAP (\k.THE(lookup k t)) [1;2],MAP (\k.lookup k t) [0;1;2;9],n)``;
val _ = out "rename_invalid" ``let (ns,t,n) = list_next_var_rename [0;4] (BN LN LN) 0 in (ns,MAP (\k.THE(lookup k t)) [0;4],MAP (\k.lookup k t) [0;1;4],n)``;
val _ = out "rename_order" ``let (ns,t,n) = list_next_var_rename [4;0;2] (fromAList [(9,99)]) 101 in (ns,MAP (\k.THE(lookup k t)) [4;0;2],MAP (\k.lookup k t) [0;2;4;9],n)``;
val _ = out "rename_large" ``let (ns,t,n) = list_next_var_rename [18446744073709551616;3] LN 18446744073709551616 in (ns,MAP (\k.THE(lookup k t)) [18446744073709551616;3],MAP (\k.lookup k t) [0;3;18446744073709551616],n)``;
