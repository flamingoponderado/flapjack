(* Direct original ml_monadBase fixed-array primitives and reg_alloc st_ex_MAP; CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble ml_monadBaseTheory reg_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "msub_hit" ``Msub (0:num) 1 [5;6;7:num] = M_success 6``;
val _ = print_eval "msub_miss" ``Msub (0:num) 3 [5;6;7:num] = M_failure 0``;
val _ = print_eval "mupdate_hit" ``Mupdate (0:num) 9 1 [5;6;7:num] = M_success [5;9;7]``;
val _ = print_eval "mupdate_miss" ``Mupdate (0:num) 9 3 [5;6;7:num] = M_failure 0``;
val _ = print_eval "marray_length" ``Marray_length FST ([1;2:num], T) = (M_success 2 : (num, num) exc, ([1;2], T))``;
val _ = print_eval "marray_sub_hit" ``Marray_sub FST (0:num) 1 ([1;2:num], T) = (M_success 2, ([1;2], T))``;
val _ = print_eval "marray_sub_miss" ``Marray_sub FST (0:num) 2 ([1;2:num], T) = (M_failure 0, ([1;2], T))``;
val _ = print_eval "marray_update_hit" ``Marray_update FST (\a s. (a, SND s)) (0:num) 1 9 ([1;2:num], T) = (M_success (), ([1;9], T))``;
val _ = print_eval "marray_update_miss" ``Marray_update FST (\a s. (a, SND s)) (0:num) 5 9 ([1;2:num], T) = (M_failure 0, ([1;2], T))``;
val _ = print_eval "st_ex_map_ok" ``st_ex_MAP (\x (s:num). (M_success (x + 1) : (num, num) exc, s + 1)) [1;2;3:num] 0 = (M_success [2;3;4], 3)``;
val _ = print_eval "st_ex_map_fail" ``st_ex_MAP (\x (s:num). if x = 2 then (M_failure (7:num), s + 10) else (M_success (x:num), s + 1)) [1;2;3:num] 0 = (M_failure 7, 11)``;
