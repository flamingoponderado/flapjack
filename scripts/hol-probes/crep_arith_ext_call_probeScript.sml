(*
  Direct HOL observations for the ExtCall case of
  crep_arithProofScript.sml:184-212 `simp_prog_correct`.

  HOL `simp_prog` leaves an `ExtCall` unchanged (the catch-all
  `simp_prog p = p`, crep_arithScript.sml:113), and
  `evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s)` reads the four
  configuration/array indices through `FLOOKUP s.locals`, loads the two byte
  windows with `read_bytearray`/`mem_load_byte`, and calls `call_FFI`
  (crepSemScript.sml:367-379).  When any of the four locals is absent the
  clause returns `(SOME Error, s)`.  The local `mapc` overload is inlined as
  `fun f st. st with code := FMAP_MAP2 f st.code`.

  Rows `simp_prog_extcall` and `extcall_mapcs_code` pin the source identity and
  the code-only `mapc` rendering; the two `evaluate_extcall_*_locals` rows pin
  the missing-locals `(SOME Error, s)` failure branch, directly and under the
  code-only `mapc` rewrite.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val s = ``(s:(8,unit) crepSem$state)``;
val call = ``(crepLang$ExtCall (strlit "foo") 1 2 3 4 : 8 crepLang$prog)``;
val sEmpty = ``(^s with locals := FEMPTY)``;
val mapcF = ``\(st : (8,unit) crepSem$state).
    st with code := FMAP_MAP2 f st.code``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "simp_prog_extcall"
  ``crep_arith$simp_prog ^call = ^call``;
val _ = print_eval "extcall_mapcs_code"
  ``(^mapcF ^s).code = FMAP_MAP2 f s.code``;
val _ = print_eval "evaluate_extcall_missing_locals"
  ``crepSem$evaluate (^call, ^sEmpty) = (SOME crepSem$Error, ^sEmpty)``;
val _ = print_eval "evaluate_extcall_mapc_missing_locals"
  ``crepSem$evaluate (^call, ^mapcF ^sEmpty) = (SOME crepSem$Error, ^mapcF ^sEmpty)``;
