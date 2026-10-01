(* The original targetProps proof theory has no prebuilt object here. Read and
   re-elaborate its two unchanged Definition bodies in-memory, then observe
   those source-derived operations. No substitute clauses or theory exports. *)
load "bossLib";
load "tautLib";
load "preamble";
load "targetSemTheory";
open bossLib HolKernel Parse preamble targetSemTheory;
val _ = new_theory "target_props_interference_probe";
val cake = case OS.Process.getEnv "CAKEML" of SOME s => s
  | NONE => "/home/zksecurity/pancake-lean/cakeml";
val input = TextIO.openIn (cake ^ "/compiler/backend/semantics/targetPropsScript.sml");
val source = TextIO.inputAll input;
val _ = TextIO.closeIn input;
fun source_definition name = let
  val marker = "Definition " ^ name ^ ":\n"
  val (_, suffix) = Substring.position marker (Substring.full source)
  val (body, _) = Substring.position "\nEnd" (Substring.triml (String.size marker) suffix)
  val _ = if Substring.isEmpty body then raise Fail ("Missing original " ^ name) else ()
  in Define [QUOTE (Substring.string body)] end;
val shift_def = source_definition "shift_interfer_def";
val disjoint_def = source_definition "ffi_entry_pcs_disjoint_def";
val contrapos = prove (``(P ==> ~Q) = (Q ==> ~P)``, tautLib.TAUT_TAC);
fun print_eval label q = let
  val th = (SIMP_CONV (srw_ss()) [shift_def, disjoint_def, miscTheory.shift_seq_def,
    pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
    pred_setTheory.IN_INTER, pred_setTheory.NOT_IN_EMPTY] THENC EVAL THENC
    DEPTH_CONV ((BINDER_CONV (REWR_CONV contrapos) THENC
      SIMP_CONV (srw_ss()) [] THENC numLib.BOUNDED_FORALL_CONV EVAL) ORELSEC
      (BINDER_CONV (REWR_CONV boolTheory.CONJ_COMM) THENC
        numLib.BOUNDED_EXISTS_CONV EVAL)) THENC EVAL THENC
    REPEATC (CHANGED_CONV (DEPTH_CONV
      (numLib.BOUNDED_FORALL_CONV EVAL ORELSEC numLib.BOUNDED_EXISTS_CONV EVAL)
      THENC EVAL))) q
  val _ = if aconv (rconc th) ``T`` then () else raise Fail (label ^ ": unresolved observation")
  in print (label ^ "="); print_term (rconc th); print "\n" end;
val config = ``(ARB:(8,num,unit) machine_config) with
  <|next_interfer := (\i s. i + s); ffi_entry_pcs := [0w;0w];
    ffi_interfer := (\i (n,bs,s). i+n+s)|>``;
val state = ``(ARB:8 asmSem$asm_state) with pc := 254w``;
val _ = print_eval "shift_zero" ``(shift_interfer 0 ^config).next_interfer 2 7 = 9``;
val _ = print_eval "shift_three" ``(shift_interfer 3 ^config).next_interfer 2 7 = 12``;
val _ = print_eval "shift_composition" ``(shift_interfer 4 (shift_interfer 3 ^config)).next_interfer 2 7 = 16``;
val _ = print_eval "shift_ffi_unchanged" ``(shift_interfer 3 ^config).ffi_interfer 2 (4,[],7) = 13``;
val _ = print_eval "shift_target_unchanged" ``(shift_interfer 3 ^config).target = (^config).target``;
val _ = print_eval "region_empty" ``ffi_entry_pcs_disjoint ^config ^state 0``;
val _ = print_eval "region_safe_before_wrap" ``ffi_entry_pcs_disjoint ^config ^state 2``;
val _ = print_eval "region_wrap_hits_entry" ``~ffi_entry_pcs_disjoint ^config ^state 3``;
