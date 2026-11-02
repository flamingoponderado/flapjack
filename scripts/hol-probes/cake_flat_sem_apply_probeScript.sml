load "flatSemTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
fun show_word_eval label tm = (print label; print_term (rhs (concl
  ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV) THENC EVAL) tm))); print "\n");
val _ = show_thm "do_app_typed=" flatSemTheory.do_app_def;
val _ = show_eval "global_alloc=" ``OPTION_MAP (λ(s,r). (s.globals,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := []) (GlobalVarAlloc 2) [])``;
val _ = show_eval "global_init=" ``OPTION_MAP (λ(s,r). (s.globals,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [NONE]) (GlobalVarInit 0) [Litv (IntLit 7)])``;
val _ = show_eval "global_reinit=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [SOME (Litv (IntLit 3))]) (GlobalVarInit 0) [Litv (IntLit 7)])``;
val _ = show_eval "global_lookup=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [SOME (Litv (IntLit 7))]) (GlobalVarLookup 0) [])``;
val _ = show_eval "global_missing=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with globals := [NONE]) (GlobalVarLookup 0) [])``;
val _ = show_eval "tag_match=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (TagLenEq 2 1) [Conv (SOME (2,NONE)) [Litv (IntLit 7)]])``;
val _ = show_eval "tag_mismatch=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (TagLenEq 3 1) [Conv (SOME (2,NONE)) [Litv (IntLit 7)]])``;
val _ = show_eval "tuple_length=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (LenEq 1) [Conv NONE [Litv (IntLit 7)]])``;
val _ = show_eval "field_index=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (El 0) [Conv NONE [Litv (IntLit 7)]])``;
val _ = show_eval "ref_field=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 7))]) (El 0) [Loc T 0])``;
val _ = show_eval "ref_bad_index=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 7))]) (El 1) [Loc T 0])``;
val _ = show_eval "identity=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) Id [Litv (IntLit 7)])``;
val _ = show_eval "ref_alloc=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 2))])
    (Src Opref) [Litv (IntLit 7)])``;
val _ = show_eval "ref_assign=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 2))])
    (Src Opassign) [Loc T 0; Litv (IntLit 7)])``;
val _ = show_eval "byte_safe_oob=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w]])
    (Src Aw8sub) [Loc T 0; Litv (IntLit 2)])``;
val _ = show_eval "byte_unsafe_oob=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w]])
    (Src Aw8sub_unsafe) [Loc T 0; Litv (IntLit 2)])``;
val _ = show_eval "array_negative=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Aalloc) [Litv (IntLit ~1); Litv (IntLit 7)])``;
val _ = show_eval "array_update=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Varray [Litv (IntLit 2)]])
    (Src Aupdate) [Loc T 0; Litv (IntLit 0); Litv (IntLit 7)])``;
val _ = show_eval "array_wrong_store=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w]])
    (Src Aupdate) [Loc T 0; Litv (IntLit 0); Litv (IntLit 7)])``;
val _ = show_eval "data_strlen=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Strlen) [Litv (StrLit «abc»)])``;
val _ = show_eval "data_strsub_negative=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Strsub) [Litv (StrLit «abc»); Litv (IntLit (-1))])``;
val _ = show_eval "data_vector_sub=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Vsub) [Vectorv [Litv (IntLit 4)]; Litv (IntLit 0)])``;
val _ = show_eval "data_vector_unsafe=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src Vsub_unsafe) [Vectorv [Litv (IntLit 4)]; Litv (IntLit 1)])``;
val _ = show_eval "data_copy=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src CopyStrStr) [Litv (StrLit «abcd»); Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = show_eval "data_copy_oob=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src CopyStrStr) [Litv (StrLit «abcd»); Litv (IntLit 3); Litv (IntLit 2)])``;
val _ = show_eval "data_thunk_alloc=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [])
    (Src (ThunkOp (AllocThunk NotEvaluated))) [Litv (IntLit 5)])``;
val _ = show_eval "numeric_shift=" ``OPTION_MAP SND
  (flatSem$do_app (ARB : (unit,unit) flatSem$state) (Src (Shift W8 Lsl 2)) [Litv (Word8 7w)])``;
val _ = show_eval "data_copy_overlap=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [1w;2w;3w;4w]])
    (Src CopyAw8Aw8) [Loc T 0; Litv (IntLit 0); Litv (IntLit 3); Loc T 0; Litv (IntLit 1)])``;
val _ = show_word_eval "data_copy_string_to_bytes=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [0w;0w;0w]])
    (Src CopyStrAw8) [Litv (StrLit «ABC»); Litv (IntLit 1); Litv (IntLit 2); Loc T 0; Litv (IntLit 1)])``;
val _ = show_word_eval "data_copy_bytes_to_string=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [0w;65w;255w]])
    (Src CopyAw8Str) [Loc T 0; Litv (IntLit 1); Litv (IntLit 2)])``;
val _ = show_eval "data_copy_negative_dest=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [0w]])
    (Src CopyStrAw8) [Litv (StrLit «A»); Litv (IntLit 0); Litv (IntLit 1); Loc T 0; Litv (IntLit (-1))])``;
val _ = show_eval "data_copy_wrong_store=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [Refv (Litv (IntLit 1))])
    (Src CopyAw8Str) [Loc T 0; Litv (IntLit 0); Litv (IntLit 1)])``;
val _ = show_word_eval "data_xor_bytes=" ``OPTION_MAP (λ(s,r). (s.refs,r))
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [3w;5w;7w]])
    (Src XorAw8Str_unsafe) [Loc T 0; Litv (StrLit «AB»)])``;
val _ = show_eval "data_xor_short=" ``OPTION_MAP SND
  (flatSem$do_app ((ARB : (unit,unit) flatSem$state) with refs := [W8array [3w]])
    (Src XorAw8Str_unsafe) [Loc T 0; Litv (StrLit «AB»)])``;
