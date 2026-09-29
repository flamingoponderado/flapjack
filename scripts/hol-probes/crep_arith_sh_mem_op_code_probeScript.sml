(*
  Direct HOL observations for crep_arithProofScript.sml:173-180
  `sh_mem_op_code`: the proof-script-local `mapc` code rewrite commutes with
  the shared-memory operation.  `mapc` is overloaded `[local]` in the proof
  script, so it is inlined here as `fun f s. s with code := FMAP_MAP2 f s.code`
  (bound below as `mapcF`, with `f` free), and the HOL pair map `I ## mapc f`
  as `I ## (^mapcF)`.  The rows pin the shared-memory domain to the empty set
  so that the domain checks decide and both sides reduce to syntactically
  identical terms; the underlying load/store/FFI outcomes of `sh_mem_op` are
  separately evidenced by scripts/hol-probes/crep_sh_mem_op_probe.out.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val sEmpty = ``^s with sh_memaddrs := {}``;
val sStore = ``(^s with <|
    sh_memaddrs := {};
    locals := FEMPTY |+ (1, Word (0w:8 word)) |>)``;
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

val _ = print_eval "sh_mem_op_code_code"
  ``(^mapcF ^s).code = FMAP_MAP2 f s.code``;
val _ = print_eval "sh_mem_op_code_load_err"
  ``crepSem$sh_mem_op Load 1 (3w:8 word) (^mapcF ^sEmpty) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Load 1 (3w:8 word) ^sEmpty)``;
val _ = print_eval "sh_mem_op_code_store_err"
  ``crepSem$sh_mem_op Store 1 (3w:8 word) (^mapcF ^sStore) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Store 1 (3w:8 word) ^sStore)``;
val _ = print_eval "sh_mem_op_code_load8_err"
  ``crepSem$sh_mem_op Load8 1 (3w:8 word) (^mapcF ^sEmpty) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Load8 1 (3w:8 word) ^sEmpty)``;
val _ = print_eval "sh_mem_op_code_store8_err"
  ``crepSem$sh_mem_op Store8 1 (3w:8 word) (^mapcF ^sStore) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Store8 1 (3w:8 word) ^sStore)``;
val _ = print_eval "sh_mem_op_code_load16_err"
  ``crepSem$sh_mem_op Load16 1 (3w:8 word) (^mapcF ^sEmpty) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Load16 1 (3w:8 word) ^sEmpty)``;
val _ = print_eval "sh_mem_op_code_store16_err"
  ``crepSem$sh_mem_op Store16 1 (3w:8 word) (^mapcF ^sStore) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Store16 1 (3w:8 word) ^sStore)``;
val _ = print_eval "sh_mem_op_code_load32_err"
  ``crepSem$sh_mem_op Load32 1 (3w:8 word) (^mapcF ^sEmpty) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Load32 1 (3w:8 word) ^sEmpty)``;
val _ = print_eval "sh_mem_op_code_store32_err"
  ``crepSem$sh_mem_op Store32 1 (3w:8 word) (^mapcF ^sStore) =
      (I ## (^mapcF)) (crepSem$sh_mem_op Store32 1 (3w:8 word) ^sStore)``;
