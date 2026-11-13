(* Typed source declarations for riscv_step (task 154). Free variables of a
   theorem conclusion are printed as a ∀* prefix; HOL stores them as
   implicitly universally quantified, so their order is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/common") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/lib") ::
  !loadPath;
load "riscv_stepTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th =
  let val fvs = free_vars (concl th) in
    (print (label ^ "=");
     if null fvs then ()
     else (print "∀*";
           app (fn v =>
             let val ts = type_to_string (type_of v)
                 val ts = if String.sub (ts, 0) = #":"
                          then String.extract (ts, 1, NONE) else ts
             in print "("; print (#1 (dest_var v));
                print " :"; print ts; print ") " end) fvs;
           print ". ");
     app (fn h => (print_term h; print " ==> ")) (hyp th);
     print_term (concl th); print "\n")
  end;

val thy = "riscv_step";
val datatypeNames =
  List.map (fn n => String.substring (n, 0, String.size n - 6))
    (List.filter (fn n => String.isSuffix "_Axiom" n)
      (List.map #1 (DB.theorems thy)));

fun ctorsOf d =
  let
    fun try n =
      (TypeBase.constructors_of
         (mk_type (d, List.tabulate (n, fn _ => alpha)))
       handle _ => [])
    fun first [] = []
      | first (n :: ns) =
          let val cs = try n in if null cs then first ns else cs end
  in first [0, 1, 2, 3, 4] end;

val allCtors = List.concat (List.map ctorsOf datatypeNames);

fun emitDatatype label name =
  let val cs = ctorsOf name in
    if null cs then false
    else
      (print (label ^ "=");
       print (String.concatWith "; "
         (List.map (fn c =>
            let val (n, t) = dest_const c
            in n ^ ":" ^ type_to_string t end) cs));
       print "\n"; true)
  end;

fun ctorType name =
  case List.filter (fn c => #1 (dest_const c) = name) allCtors of
    [] => NONE
  | c :: _ => SOME (type_to_string (#2 (dest_const c)));

fun emit label name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE =>
      if emitDatatype label name then ()
      else case ctorType name of
        SOME s => (print (label ^ "="); print s; print "\n")
      | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

val _ = emit "avoid_signalAddressException_typed" "avoid_signalAddressException";
val _ = emit "v2w_0_rwts_typed" "v2w_0_rwts";
val _ = emit "word_bit_0_lemmas_typed" "word_bit_0_lemmas";
val _ = emit "word_bit_1_0_typed" "word_bit_1_0";
val _ = emit "word_bit_add_lsl_simp_typed" "word_bit_add_lsl_simp";
val _ = emit "BEQ_typed" "BEQ";
val _ = emit "BGE_typed" "BGE";
val _ = emit "BGEU_typed" "BGEU";
val _ = emit "BLT_typed" "BLT";
val _ = emit "BLTU_typed" "BLTU";
val _ = emit "BNE_typed" "BNE";
val _ = emit "DecodeAny_def_typed" "DecodeAny_def";
val _ = emit "DecodeRVC_IMP_DecodeAny_typed" "DecodeRVC_IMP_DecodeAny";
val _ = emit "Decode_IMP_DecodeAny_typed" "Decode_IMP_DecodeAny";
val _ = emit "NextRISCV_typed" "NextRISCV";
val _ = emit "NextRISCV_branch_typed" "NextRISCV_branch";
val _ = emit "NextRISCV_cond_branch_typed" "NextRISCV_cond_branch";
val _ = emit "Fetch_def_typed" "Fetch_def";
val _ = emit "Fetch16_typed" "Fetch16";
val _ = emit "Fetch32_typed" "Fetch32";
val _ = emit "ADDI_typed" "ADDI";
val _ = emit "ADDI_NOP_typed" "ADDI_NOP";
val _ = emit "ANDI_typed" "ANDI";
val _ = emit "ANDI_NOP_typed" "ANDI_NOP";
val _ = emit "ORI_typed" "ORI";
val _ = emit "ORI_NOP_typed" "ORI_NOP";
val _ = emit "XORI_typed" "XORI";
val _ = emit "XORI_NOP_typed" "XORI_NOP";
val _ = emit "SLTI_typed" "SLTI";
val _ = emit "SLTIU_typed" "SLTIU";
val _ = emit "SLLI_typed" "SLLI";
val _ = emit "SLLI_NOP_typed" "SLLI_NOP";
val _ = emit "SRAI_typed" "SRAI";
val _ = emit "SRAI_NOP_typed" "SRAI_NOP";
val _ = emit "SRLI_typed" "SRLI";
val _ = emit "SRLI_NOP_typed" "SRLI_NOP";
val _ = emit "JAL_typed" "JAL";
val _ = emit "JAL_NOP_typed" "JAL_NOP";
val _ = emit "JALR_typed" "JALR";
val _ = emit "JALR_NOP_typed" "JALR_NOP";
val _ = emit "LB_typed" "LB";
val _ = emit "LB_NOP_typed" "LB_NOP";
val _ = emit "LBU_typed" "LBU";
val _ = emit "LBU_NOP_typed" "LBU_NOP";
val _ = emit "LD_typed" "LD";
val _ = emit "LD_NOP_typed" "LD_NOP";
val _ = emit "LH_typed" "LH";
val _ = emit "LH_NOP_typed" "LH_NOP";
val _ = emit "LHU_typed" "LHU";
val _ = emit "LHU_NOP_typed" "LHU_NOP";
val _ = emit "LW_typed" "LW";
val _ = emit "LW_NOP_typed" "LW_NOP";
val _ = emit "LWU_typed" "LWU";
val _ = emit "LWU_NOP_typed" "LWU_NOP";
val _ = emit "DIV_typed" "DIV";
val _ = emit "MUL_typed" "MUL";
val _ = emit "REM_typed" "REM";
val _ = emit "REMU_typed" "REMU";
val _ = emit "MULH_typed" "MULH";
val _ = emit "MULH_NOP_typed" "MULH_NOP";
val _ = emit "MULHSU_typed" "MULHSU";
val _ = emit "MULHSU_NOP_typed" "MULHSU_NOP";
val _ = emit "MULHU_typed" "MULHU";
val _ = emit "MULHU_NOP_typed" "MULHU_NOP";
val _ = emit "NextRISCV_def_typed" "NextRISCV_def";
val _ = emit "ADD_typed" "ADD";
val _ = emit "ADD_NOP_typed" "ADD_NOP";
val _ = emit "AND_typed" "AND";
val _ = emit "AND_NOP_typed" "AND_NOP";
val _ = emit "OR_typed" "OR";
val _ = emit "OR_NOP_typed" "OR_NOP";
val _ = emit "SUB_typed" "SUB";
val _ = emit "SUB_NOP_typed" "SUB_NOP";
val _ = emit "XOR_typed" "XOR";
val _ = emit "XOR_NOP_typed" "XOR_NOP";
val _ = emit "SLT_typed" "SLT";
val _ = emit "SLT_NOP_typed" "SLT_NOP";
val _ = emit "SLTU_typed" "SLTU";
val _ = emit "SLTU_NOP_typed" "SLTU_NOP";
val _ = emit "SLL_typed" "SLL";
val _ = emit "SLL_NOP_typed" "SLL_NOP";
val _ = emit "SRA_typed" "SRA";
val _ = emit "SRA_NOP_typed" "SRA_NOP";
val _ = emit "SRL_typed" "SRL";
val _ = emit "SRL_NOP_typed" "SRL_NOP";
val _ = emit "SB_typed" "SB";
val _ = emit "SD_typed" "SD";
val _ = emit "SH_typed" "SH";
val _ = emit "SW_typed" "SW";
val _ = emit "update_pc_typed" "update_pc";
val _ = emit "update_pc_def_typed" "update_pc_def";
val _ = emit "AUIPC_typed" "AUIPC";
val _ = emit "AUIPC_NOP_typed" "AUIPC_NOP";
val _ = emit "LUI_typed" "LUI";
val _ = emit "LUI_NOP_typed" "LUI_NOP";
val _ = emit "DIVUW_typed" "DIVUW";
val _ = emit "DIVUW_NOP_typed" "DIVUW_NOP";
val _ = emit "DIVW_typed" "DIVW";
val _ = emit "DIVW_NOP_typed" "DIVW_NOP";
val _ = emit "MULW_typed" "MULW";
val _ = emit "MULW_NOP_typed" "MULW_NOP";
val _ = emit "REMUW_typed" "REMUW";
val _ = emit "REMUW_NOP_typed" "REMUW_NOP";
val _ = emit "REMW_typed" "REMW";
val _ = emit "REMW_NOP_typed" "REMW_NOP";
val _ = emit "SLLIW_typed" "SLLIW";
val _ = emit "SLLIW_NOP_typed" "SLLIW_NOP";
val _ = emit "SLLW_typed" "SLLW";
val _ = emit "SLLW_NOP_typed" "SLLW_NOP";
val _ = emit "SRAIW_typed" "SRAIW";
val _ = emit "SRAIW_NOP_typed" "SRAIW_NOP";
val _ = emit "SRAW_typed" "SRAW";
val _ = emit "SRAW_NOP_typed" "SRAW_NOP";
val _ = emit "SRLIW_typed" "SRLIW";
val _ = emit "SRLIW_NOP_typed" "SRLIW_NOP";
val _ = emit "SRLW_typed" "SRLW";
val _ = emit "SRLW_NOP_typed" "SRLW_NOP";
val _ = emit "ADDIW_typed" "ADDIW";
val _ = emit "ADDIW_NOP_typed" "ADDIW_NOP";
val _ = emit "ADDW_typed" "ADDW";
val _ = emit "ADDW_NOP_typed" "ADDW_NOP";
val _ = emit "SUBW_typed" "SUBW";
val _ = emit "SUBW_NOP_typed" "SUBW_NOP";
val _ = emit "Skip_typed" "Skip";
val _ = emit "DIVU_typed" "DIVU";
val _ = emit "DIVU_NOP_typed" "DIVU_NOP";
val _ = emit "MUL_NOP_typed" "MUL_NOP";
val _ = emit "DIV_NOP_typed" "DIV_NOP";
val _ = emit "REM_NOP_typed" "REM_NOP";
val _ = emit "REMU_NOP_typed" "REMU_NOP";
val _ = emit "SLTI_NOP_typed" "SLTI_NOP";
val _ = emit "SLTIU_NOP_typed" "SLTIU_NOP";

val _ = OS.Process.exit OS.Process.success;
