(*
  Direct HOL-EVAL fixture for the StackSem evaluate_def Install clause.
  Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:893-921.

  The state type is (8,'c,num): 8-bit words, a num compiler configuration, and
  a num oracle state.  The compiler and compiler oracle are concrete closures so
  HOL EVAL reduces the clause: the oracle at step n returns (n, [(3,Skip)],
  [0xAA;0xBB]), and compile cfg progs returns ([0x11;0x22], cfg+1).  The code
  buffer holds the two bytes [0x11;0x22] at position 0 and the data buffer holds
  [0xAA;0xBB] at position 0, matching the four operand registers 1..4.

  Observations cover a successful install with use_stack = T (bitmaps, code
  union, the DRESTRICT/FUPDATE register update, the emptied fp_regs and the
  advanced compile oracle), a compile byte mismatch (SOME Error, state
  unchanged), an empty `progs` list (SOME Error), a compiler NONE (SOME Error),
  the use_stack = F arm (the data bytes are the oracle bitmap and the data
  buffer is left unflushed), and a non-Word first operand (SOME Error).
*)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun print_eval label q =
  let
    val th0 = EVAL q
    (* The register update restricts with DRESTRICT, a non-computational
       finite-map specification, and then applies FUPDATE, which EVAL leaves as
       FLOOKUP (DRESTRICT ... |+ ...).  Rewrite with the two finite-map lookup
       lemmas and finish with EVAL. *)
    val th = QCONV (REWRITE_CONV [FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] THENC EVAL)
                     (rhs (concl th0))
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(8,num,num) stackSem$state``;
val cb = ``<| position := (0w:8 word); buffer := [0x11w; 0x22w]; space_left := 2 |>
            :(8,8) buffer``;
val db = ``<| position := (0w:8 word); buffer := [0xAAw; 0xBBw]; space_left := 2 |>
            :(8,8) buffer``;
val comp = ``\cfg:num progs:(num # 8 stackLang$prog) list.
               SOME ([0x11w; 0x22w]:8 word list, cfg + 1)``;
val orac = ``\n:num. (n, [(3:num, Skip):(num # 8 stackLang$prog)],
                          [0xAAw; 0xBBw]:8 word list)``;
val base =
  ``^s with <|
      regs := (FEMPTY |+ (1, Word (0w:8 word)) |+ (2, Word (2w:8 word))
                    |+ (3, Word (0w:8 word)) |+ (4, Word (2w:8 word))
                    |+ (5, Word (0x55w:8 word)));
      fp_regs := (FEMPTY |+ (9, (0x66w:64 word)));
      ffi_save_regs := {1; 5};
      bitmaps := [0x01w:8 word];
      code := insert 7 (Return 0) LN;
      code_buffer := ^cb;
      data_buffer := ^db;
      compile := ^comp;
      compile_oracle := ^orac;
      use_stack := T;
      clock := 5 |>``;
val proj =
  ``\(r:8 stackSem$result option, t:(8,num,num) stackSem$state).
      (r, t.bitmaps, lookup 3 t.code, lookup 7 t.code,
       FLOOKUP t.regs 1, FLOOKUP t.regs 2, FLOOKUP t.regs 5,
       FLOOKUP t.fp_regs 9, t.code_buffer.position,
       t.data_buffer.position, LENGTH t.data_buffer.buffer,
       FST (t.compile_oracle 0))``;

val _ = print_eval "install_success"
  ``^proj (let s0 = ^base in stackSem$evaluate (Install 1 2 3 4 5, s0))``;
val _ = print_eval "install_bytes_mismatch"
  ``^proj (let s0 = ^base with compile :=
              (\cfg:num progs:(num # 8 stackLang$prog) list.
                 SOME ([0x12w; 0x22w]:8 word list, cfg + 1))
            in stackSem$evaluate (Install 1 2 3 4 5, s0))``;
val _ = print_eval "install_progs_empty"
  ``^proj (let s0 = ^base with compile_oracle :=
              (\n:num. (n, []:(num # 8 stackLang$prog) list,
                          [0xAAw; 0xBBw]:8 word list))
            in stackSem$evaluate (Install 1 2 3 4 5, s0))``;
val _ = print_eval "install_compile_none"
  ``^proj (let s0 = ^base with compile :=
              (\cfg:num progs:(num # 8 stackLang$prog) list.
                 NONE:(8 word list # num) option)
            in stackSem$evaluate (Install 1 2 3 4 5, s0))``;
val _ = print_eval "install_use_stack_false"
  ``^proj (let s0 = ^base with use_stack := F
            in stackSem$evaluate (Install 1 2 3 4 5, s0))``;
val _ = print_eval "install_non_word_operand"
  ``^proj (let s0 = ^base in
             let s1 = s0 with regs := s0.regs |+ (1, Loc 1 0) in
               stackSem$evaluate (Install 1 2 3 4 5, s1))``;
