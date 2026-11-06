load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "concat_choice_typed=" (prove (
  ``∀lv (s : ('c,'ffi) closSem$state).
      closSem$do_app (MemOp ConcatByteVec) [lv] s =
        (case (some wss. closSem$v_to_list lv = SOME (MAP ByteVector wss)) of
         | SOME wss => Rval (ByteVector (FLAT wss),s)
         | NONE => Rerr (Rabort Rtype_error))``,
  simp [closSemTheory.do_app_def]));
val _ = show_thm "from_list_choice_typed=" (prove (
  ``∀lv (s : ('c,'ffi) closSem$state).
      closSem$do_app (MemOp FromListByte) [lv] s =
        (case (some ns. closSem$v_to_list lv = SOME (MAP (Number o $&) ns) ∧ EVERY (λn. n < 256) ns) of
         | SOME ns => Rval (ByteVector (MAP n2w ns),s)
         | NONE => Rerr (Rabort Rtype_error))``,
  simp [closSemTheory.do_app_def]));
val _ = show_eval "array_element=" ``case closSem$do_app (MemOp El) [RefPtr T 0; Number 1]
  ((ARB : (unit,unit) closSem$state) with refs := FEMPTY |+ (0,ValueArray [Number 4; Number 9])) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "negative_index=" ``case closSem$do_app (MemOp El) [RefPtr T 0; Number (-1)]
  ((ARB : (unit,unit) closSem$state) with refs := FEMPTY |+ (0,ValueArray [Number 4])) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "byte_update=" ``case closSem$do_app (MemOp UpdateByte) [RefPtr T 0; Number 1; Number 7]
  ((ARB : (unit,unit) closSem$state) with refs := FEMPTY |+ (0,ByteArray [1w;2w;3w])) of Rval (_,s) => FLOOKUP s.refs 0 | _ => NONE``;
val _ = show_eval "overlap_copy=" ``case closSem$do_app (MemOp (CopyByte F)) [RefPtr T 0; Number 0; Number 3; RefPtr T 0; Number 1]
  ((ARB : (unit,unit) closSem$state) with refs := FEMPTY |+ (0,ByteArray [1w;2w;3w;4w])) of Rval (_,s) => FLOOKUP s.refs 0 | _ => NONE``;
val _ = show_eval "loose_end=" ``case closSem$do_app (MemOp (BoundsCheckByte T)) [ByteVector [1w;2w]; Number 2]
  (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "strict_end=" ``case closSem$do_app (MemOp (BoundsCheckByte F)) [ByteVector [1w;2w]; Number 2]
  (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
