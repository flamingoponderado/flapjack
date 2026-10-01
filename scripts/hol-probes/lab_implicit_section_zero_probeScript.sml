(* Original implicit section-zero and ignored explicit-zero observations.
   Production static positions use actual instruction counts, so no complete
   compute_labels_alt port is asserted by this untagged repair. *)
(* The canonical driver runs from compiler/encoders/riscv. *)
loadPath := OS.Path.concat (OS.FileSys.getDir (), "../../backend") :: !loadPath;
load "bossLib";
load "preamble";
load "lab_to_targetTheory";
open bossLib HolKernel Parse preamble;
val _ = Globals.linewidth := 10000;
fun emit label tm = print (label ^ "=" ^ term_to_string (rconc (EVAL tm)) ^ "\n");
val lines = ``[Asm (Asmi (Inst (Const 2 17w))) [] 4; Label 123 0 0; Label 7 2 0] : 64 labLang$line list``;
val code = ``[Section 7 [Asm (Asmi (Inst (Const 2 17w))) [] 4]; Section 17 [Asm (Asmi (Inst (Const 3 29w))) [] 4; Label 999 0 0; Label 17 2 0]] : 64 labLang$sec list``;
val _ = emit "zero_original_skip_late_zero" ``lab_to_target$section_labels 1000 ^lines []``;
val _ = emit "zero_original_section_base" ``lab_to_target$find_pos (Lab 7 0) (lab_to_target$compute_labels_alt 1000 ^code LN)``;
val _ = emit "zero_original_second_base" ``lab_to_target$find_pos (Lab 17 0) (lab_to_target$compute_labels_alt 1000 ^code LN)``;
val _ = emit "zero_original_second_label" ``lab_to_target$find_pos (Lab 17 2) (lab_to_target$compute_labels_alt 1000 ^code LN)``;
val _ = emit "zero_original_empty_section" ``lab_to_target$find_pos (Lab 7 0) (lab_to_target$compute_labels_alt 17 [Section 7 [] : 64 labLang$sec] LN)``;

load "bitstringLib";
load "riscvTheory";
load "riscv_targetTheory";
open riscvTheory riscv_targetTheory;
fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []};
val riscv_tys =
  List.map riscv_type
    ["instruction", "Shift", "ArithI", "ArithR", "MulDiv", "Branch",
     "Load", "Store"];
val riscv_bytes_conv =
  computeLib.compset_conv (wordsLib.words_compset)
    [computeLib.Defs
      [riscv_ast_def, riscv_encode_def, riscv_const32_def,
       riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_memop_def,
       Encode_def, opc_def, Itype_def, Rtype_def, Stype_def, SBtype_def,
       Utype_def, UJtype_def],
     computeLib.Convs
       [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
     computeLib.Tys
       ([sumSyntax.mk_sum(alpha,beta),
         mk_thy_type{Thy="asm",Tyop="cmp",Args=[]}] @ riscv_tys),
     computeLib.Extenders [pairLib.add_pair_compset]];
val _ = print ("zero_original_crosssection_bytes=" ^
  term_to_string (rconc (riscv_bytes_conv
    ``MAP w2n (FLAT (MAP riscv_encode (riscv_ast (Jump 4w) ++ riscv_ast (Inst (Const 1 7w)))))``)) ^ "\n");
