load "preamble";
load "dataLangTheory";
load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "op_space_reset=" dataLangTheory.op_space_reset_def;
val _ = show "size_of=" dataSemTheory.size_of_def;
(* The theory later rebinds size_of_def after proving that check_res is
   redundant. Replay the local lemma and the original cons clause with types. *)
val checkResSizeOf = ``!lims vs refs seen.
  dataSem$check_res refs (dataSem$size_of lims vs refs seen) = dataSem$size_of lims vs refs seen``;
val checkResSizeReplay = prove (checkResSizeOf,
  qsuff_tac `!lims vs refs seen. sptree$size ((\(n,rs,ss). rs) (dataSem$size_of lims vs refs seen)) <= sptree$size refs`
  >- (rw [] \\ pop_assum (assume_tac o SPEC_ALL) \\ pairarg_tac \\ fs [dataSemTheory.check_res_def])
  \\ ho_match_mp_tac dataSemTheory.size_of_ind \\ fs [dataSemTheory.size_of_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [dataSemTheory.check_res_def,bool_case_eq,option_case_eq,pair_case_eq,CaseEq"ref"]
  \\ rveq \\ fs [] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ fs [sptreeTheory.size_delete]);
val originalSizeCons = ``!lims x y ys refs seen.
  dataSem$size_of lims (x::y::ys) refs seen =
    let (n1,refs1,seen1) = dataSem$check_res refs (dataSem$size_of lims (y::ys) refs seen) in
    let (n2,refs2,seen2) = dataSem$size_of lims [x] refs1 seen1 in
      (n1+n2,refs2,seen2)``;
val _ = show "check_res_size_of_replay=" checkResSizeReplay;
val _ = show "size_of_initial_cons_replay="
  (prove (originalSizeCons, simp [dataSemTheory.size_of_def, checkResSizeReplay]));
val sizeOfOriginal = ``
  (size_of lims [] refs seen = (0, refs, seen)) /\
  (size_of lims (x::y::ys) refs seen =
    let (n1,refs1,seen1) = check_res refs (size_of lims (y::ys) refs seen) in
    let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
      (n1+n2,refs2,seen2)) /\
  (size_of lims [Word64 _] refs seen = (3, refs, seen)) /\
  (size_of lims [Number i] refs seen =
    (if small_num lims.arch_64_bit i then 0 else bignum_size lims.arch_64_bit i, refs, seen)) /\
  (size_of lims [CodePtr _] refs seen = (0, refs, seen)) /\
  (size_of lims [RefPtr _ r] refs seen =
     case sptree$lookup r refs of
     | NONE => (0, refs, seen)
     | SOME (ByteArray _ bs) => (LENGTH bs DIV (arch_size lims DIV 8) + 2, delete r refs, seen)
     | SOME (ValueArray vs) => let (n,refs,seen) = size_of lims vs (delete r refs) seen in
                                 (n + LENGTH vs + 1, refs, seen)
     | SOME (Thunk _ v) => let (n,refs,seen) = size_of lims [v] (delete r refs) seen in
                             (n + 2, refs, seen)
     | SOME (MutBlock tg fin ls c rs) =>
         let (n,refs,seen) = size_of lims (ls ++ [c] ++ rs) (delete r refs) seen in
           (n + LENGTH ls + LENGTH rs + 2, refs, seen)) /\
  (size_of lims [Block ts tag []]) refs seen = (0, refs, seen) /\
  (size_of lims [Block ts tag (v::vs)] refs seen =
     if IS_SOME (sptree$lookup ts seen) then (0, refs, seen) else
       let (n,refs,seen) = size_of lims (v::vs) refs (insert ts () seen) in
         (n + LENGTH (v::vs) + 1, refs, seen))``;
val _ = show "size_of_original_typed_replay="
  (prove (sizeOfOriginal, rw [dataSemTheory.size_of_def, checkResSizeReplay]));
val _ = show "stack_to_vs=" dataSemTheory.stack_to_vs_def;
val _ = show "size_of_heap=" dataSemTheory.size_of_heap_def;
val _ = show "size_of_heap_args=" dataSemTheory.size_of_heap_args_def;
val _ = show "space_consumed=" dataSemTheory.space_consumed_def;
val _ = show "do_space=" dataSemTheory.do_space_def;
