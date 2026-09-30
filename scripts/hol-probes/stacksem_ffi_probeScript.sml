(*
  Direct HOL-EVAL fixture for the StackSem evaluate_def FFI clause.
  Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:945-960.

  The observations cover a successful ExtCall whose returned bytes are written
  back with write_bytearray while regs is DRESTRICTed by ffi_save_regs and
  fp_regs is emptied, a terminal oracle result that becomes FinalFFI with the
  state unchanged, a byte read outside mdomain that yields Error, and a
  non-Word length register that yields Error.

  State type (64,'c,num): 64-bit words, a num oracle state.  The oracle used by
  the successful row returns three constant bytes so the length check against
  the three-byte array read passes; the terminal oracle diverges.
*)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun print_eval label q =
  let
    val th0 = EVAL q
    (* stackSem's FFI return branch restricts registers with DRESTRICT, a
       non-computational finite-map specification, so EVAL leaves
       `FLOOKUP (DRESTRICT ...)`.  Rewrite it with FLOOKUP_DRESTRICT and
       evaluate the resulting membership test. *)
    val th = QCONV (REWRITE_CONV [FLOOKUP_DRESTRICT] THENC EVAL) (rhs (concl th0))
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,num) stackSem$state``;
val ret_ffi =
  ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) [0x11w; 0x22w; 0x33w]);
      ffi_state := 0; io_events := [] |>``;
val final_ffi =
  ``<| oracle := (\n (st:num) conf bytes. Oracle_final FFI_diverged);
      ffi_state := 0; io_events := [] |>``;
val base =
  ``^s with <|
      regs := (FEMPTY |+ (1, Word (2w:64 word)) |+ (2, Word (2w:64 word))
                    |+ (3, Word (3w:64 word)) |+ (4, Word (4w:64 word))
                    |+ (6, Word (0x99w:64 word)) |+ (7, Word (0x77w:64 word))
                    |+ (8, Word (0x88w:64 word)));
      memory := (0w =+ Word (0xAABBCCDDEEFF0011w:64 word)) (K (Word (0w:64 word)));
      mdomain := {0w};
      ffi_save_regs := {1; 6};
      fp_regs := FEMPTY |+ (9, (0x66w:64 word));
      be := F;
      ffi := ^ret_ffi;
      clock := 5 |>``;
val proj =
  ``\(r:(64) stackSem$result option, t:(64,'c,num) stackSem$state).
      (r, t.memory 0w, FLOOKUP t.regs 1, FLOOKUP t.regs 2, FLOOKUP t.regs 6,
       FLOOKUP t.regs 7, FLOOKUP t.fp_regs 9, t.ffi.ffi_state,
       t.ffi.io_events, t.clock)``;

val _ = print_eval "ffi_return"
  ``^proj (let s0 = ^base in stackSem$evaluate (FFI (strlit "x") 2 1 4 3 5, s0))``;
val _ = print_eval "ffi_final"
  ``^proj (let s0 = ^base in stackSem$evaluate (FFI (strlit "x") 2 1 4 3 5, s0 with ffi := ^final_ffi))``;
val _ = print_eval "ffi_read_failure"
  ``^proj (let s0 = ^base in stackSem$evaluate (FFI (strlit "x") 2 1 4 3 5, s0 with mdomain := {}))``;
val _ = print_eval "ffi_non_word_length"
  ``^proj (let s0 = ^base in stackSem$evaluate (FFI (strlit "x") 2 1 4 3 5,
      s0 with regs := s0.regs |+ (1, Loc 1 0)))``;
