(* Actual applications of all six original asmProps assertion theorems. *)
load "bossLib";
load "preamble";
load "asmPropsTheory";
open bossLib HolKernel Parse preamble asmPropsTheory;
val _ = computeLib.add_funs [asserts_eval, asserts2_def];

fun original_instance name goal substitutions =
  let
    val th0 = PART_MATCH (snd o strip_imp) (DB.fetch "asmProps" name) goal
    val th = Q.INST substitutions th0
    fun discharge t =
      if is_imp (concl t) then
        let
          val premise = fst (dest_imp (concl t))
          val hp =
            if is_forall premise then prove (premise, rw [FUN_EQ_THM] >> DECIDE_TAC)
            else if name = "asserts2_change_interfer" then
              prove (premise, CONJ_TAC >- EVAL_TAC >> rw [FUN_EQ_THM])
            else EQT_ELIM (EVAL premise)
        in discharge (MATCH_MP t hp) end
      else t
    val result = discharge th
    val _ = if null (hyp result) then () else raise Fail "undischarged original premise"
    val _ = if aconv (concl result) goal then () else raise Fail "wrong original conclusion"
  in result end;
fun print_original label th =
  (print (label ^ "="); print_term (rconc (EVAL (concl th))); print "\n");

val fold = original_instance "asserts_IMP_FOLDR_COUNT_LIST"
  ``(\s:num. s=13210) (FOLDR (\k s:num. 10*s+k) ((\k s:num. 10*s+k) 3 1) (COUNT_LIST 3))``
  [`P` |-> `\s:num. s<=1321`];
val _ = print_original "assert_theorem_fold" fold;

val less = original_instance "asserts_IMP_FOLDR_COUNT_LIST_LESS"
  ``(\s:num. s<=1321) (FOLDR (\k s:num. 10*s+k) 1 (REVERSE (GENLIST ((-) 3) (SUC 2))))``
  [`Q` |-> `\s:num. s=13210`];
val _ = print_original "assert_theorem_less" less;

val weak = original_instance "asserts_WEAKEN"
  ``asserts 3 (\k s:num. if k<=3 then 10*s+k else 0) 1 (\s. s<=2000) (\s. s=13210)``
  [`next` |-> `\k s:num. 10*s+k`, `P` |-> `\s:num. s<=1321`];
val _ = print_original "assert_theorem_weaken" weak;

val change = original_instance "asserts2_change_interfer"
  ``asserts2 2 (\k b:bool. if k<=2 then (if b then k else k+10) else 99)
      (\s:num. EVEN s) 0 (\s b. b=EVEN s)``
  [`fi` |-> `\k b:bool. if b then k else k+10`];
val _ = print_original "assert_theorem_change" change;

val first = original_instance "asserts2_first"
  ``(\s:num b:bool. b=EVEN s) 0 ((\s:num. EVEN s) 0)``
  [`n` |-> `2:num`, `fi` |-> `\k b:bool. if b then k else k+10`];
val _ = print_original "assert_theorem_first" first;

val every = original_instance "asserts2_every"
  ``(\s:num b:bool. b=EVEN s)
      (FUNPOW ((\b:bool. if b then 1 else 2) o (\s:num. EVEN s)) 2 0)
      ((\s:num. EVEN s) (FUNPOW ((\b:bool. if b then 1 else 2) o (\s:num. EVEN s)) 2 0))``
  [`n` |-> `4:num`];
val _ = print_original "assert_theorem_every" every;
