(* Native constructor evidence for the untagged executed-output codec.
   No HOL codec or compiler simulation theorem is asserted by these rows. *)
load "bossLib";
load "preamble";
load "stack_to_labTheory";
load "lab_to_targetTheory";
load "mlstringTheory";
open bossLib HolKernel Parse preamble;
val _ = Globals.linewidth := 10000;
fun emit label tm = print (label ^ "=" ^ term_to_string (rconc (EVAL tm)) ^ "\n");
val _ = emit "codec_source_addcarry" ``stack_to_lab$flatten F (Inst (Arith (AddCarry 1 2 3 4)) : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "codec_source_addoverflow" ``stack_to_lab$flatten F (Inst (Arith (AddOverflow 1 2 3 4)) : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "codec_source_memoffset" ``stack_to_lab$flatten F (Inst (Mem Store8 2 (Addr 3 255w)) : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "codec_source_cbw" ``stack_to_lab$flatten F (CodeBufferWrite 3 4 : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "codec_source_cbw_store_order" ``lab_to_target$cbw_to_asm (Cbw 3 4 : 64 labLang$asm_or_cbw)``;
val _ = emit "codec_source_name_bytes" ``MAP ORD (mlstring$explode (mlstring$implode (MAP CHR [0;128;255;65])))``;
val _ = emit "codec_source_ffi" ``stack_to_lab$flatten F (FFI (mlstring$implode (MAP CHR [0;128;255;65])) 1 2 3 4 5 : 64 stackLang$prog) 7 2 [] []``;
val _ = emit "codec_source_nonzero_position" ``(LabAsm (Jump (Lab 17 29)) 1w [0w;128w;255w] 23 : 64 labLang$line)``;
val _ = emit "codec_source_wide_constant" ``stack_to_lab$flatten F (Inst (Const 999 (n2w (2**79+1))) : 80 stackLang$prog) 7 2 [] []``;
