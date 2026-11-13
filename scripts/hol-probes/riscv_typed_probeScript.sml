(* Typed source declarations for riscv (task 154). Free variables of a
   theorem conclusion are printed as a ∀* prefix; HOL stores them as
   implicitly universally quantified, so their order is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/common") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/lib") ::
  !loadPath;
load "riscvTheory";
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

val thy = "riscv";
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

val _ = emit "Delta_def_typed" "Delta_def";
val _ = emit "FP32_IsSignalingNan_def_typed" "FP32_IsSignalingNan_def";
val _ = emit "FP32_Sign_def_typed" "FP32_Sign_def";
val _ = emit "FP64_IsSignalingNan_def_typed" "FP64_IsSignalingNan_def";
val _ = emit "FP64_Sign_def_typed" "FP64_Sign_def";
val _ = emit "FPRD_def_typed" "FPRD_def";
val _ = emit "FPRS_def_typed" "FPRS_def";
val _ = emit "GPR_def_typed" "GPR_def";
val _ = emit "MCSR_def_typed" "MCSR_def";
val _ = emit "NextFetch_def_typed" "NextFetch_def";
val _ = emit "RV32_CanonicalNan_def_typed" "RV32_CanonicalNan_def";
val _ = emit "RV64_CanonicalNan_def_typed" "RV64_CanonicalNan_def";
val _ = emit "ext_status_def_typed" "ext_status_def";
val _ = emit "fcsr_def_typed" "fcsr_def";
val _ = emit "fpr_def_typed" "fpr_def";
val _ = emit "gpr_def_typed" "gpr_def";
val _ = emit "l3round_def_typed" "l3round_def";
val _ = emit "rnd_mode_dynamic_def_typed" "rnd_mode_dynamic_def";
val _ = emit "rnd_mode_static_def_typed" "rnd_mode_static_def";
val _ = emit "round_def_typed" "round_def";
val _ = emit "setFP_Invalid_def_typed" "setFP_Invalid_def";
val _ = emit "setTrap_def_typed" "setTrap_def";
val _ = emit "signalException_def_typed" "signalException_def";
val _ = emit "writeFPRD_def_typed" "writeFPRD_def";
val _ = emit "writeFPRS_def_typed" "writeFPRS_def";
val _ = emit "dfn_primeFADD_D_def_typed" "dfn'FADD_D_def";
val _ = emit "dfn_primeFADD_S_def_typed" "dfn'FADD_S_def";
val _ = emit "dfn_primeFCLASS_D_def_typed" "dfn'FCLASS_D_def";
val _ = emit "dfn_primeFCLASS_S_def_typed" "dfn'FCLASS_S_def";
val _ = emit "dfn_primeFCVT_D_LU_def_typed" "dfn'FCVT_D_LU_def";
val _ = emit "dfn_primeFCVT_D_L_def_typed" "dfn'FCVT_D_L_def";
val _ = emit "dfn_primeFCVT_D_S_def_typed" "dfn'FCVT_D_S_def";
val _ = emit "dfn_primeFCVT_D_WU_def_typed" "dfn'FCVT_D_WU_def";
val _ = emit "dfn_primeFCVT_D_W_def_typed" "dfn'FCVT_D_W_def";
val _ = emit "dfn_primeFCVT_LU_D_def_typed" "dfn'FCVT_LU_D_def";
val _ = emit "dfn_primeFCVT_LU_S_def_typed" "dfn'FCVT_LU_S_def";
val _ = emit "dfn_primeFCVT_L_D_def_typed" "dfn'FCVT_L_D_def";
val _ = emit "dfn_primeFCVT_L_S_def_typed" "dfn'FCVT_L_S_def";
val _ = emit "dfn_primeFCVT_S_D_def_typed" "dfn'FCVT_S_D_def";
val _ = emit "dfn_primeFCVT_S_LU_def_typed" "dfn'FCVT_S_LU_def";
val _ = emit "dfn_primeFCVT_S_L_def_typed" "dfn'FCVT_S_L_def";
val _ = emit "dfn_primeFCVT_S_WU_def_typed" "dfn'FCVT_S_WU_def";
val _ = emit "dfn_primeFCVT_S_W_def_typed" "dfn'FCVT_S_W_def";
val _ = emit "dfn_primeFCVT_WU_D_def_typed" "dfn'FCVT_WU_D_def";
val _ = emit "dfn_primeFCVT_WU_S_def_typed" "dfn'FCVT_WU_S_def";
val _ = emit "dfn_primeFCVT_W_D_def_typed" "dfn'FCVT_W_D_def";
val _ = emit "dfn_primeFCVT_W_S_def_typed" "dfn'FCVT_W_S_def";
val _ = emit "dfn_primeFDIV_D_def_typed" "dfn'FDIV_D_def";
val _ = emit "dfn_primeFDIV_S_def_typed" "dfn'FDIV_S_def";
val _ = emit "dfn_primeFEQ_D_def_typed" "dfn'FEQ_D_def";
val _ = emit "dfn_primeFEQ_S_def_typed" "dfn'FEQ_S_def";
val _ = emit "dfn_primeFLE_D_def_typed" "dfn'FLE_D_def";
val _ = emit "dfn_primeFLE_S_def_typed" "dfn'FLE_S_def";
val _ = emit "dfn_primeFLT_D_def_typed" "dfn'FLT_D_def";
val _ = emit "dfn_primeFLT_S_def_typed" "dfn'FLT_S_def";
val _ = emit "dfn_primeFMADD_D_def_typed" "dfn'FMADD_D_def";
val _ = emit "dfn_primeFMADD_S_def_typed" "dfn'FMADD_S_def";
val _ = emit "dfn_primeFMAX_D_def_typed" "dfn'FMAX_D_def";
val _ = emit "dfn_primeFMAX_S_def_typed" "dfn'FMAX_S_def";
val _ = emit "dfn_primeFMIN_D_def_typed" "dfn'FMIN_D_def";
val _ = emit "dfn_primeFMIN_S_def_typed" "dfn'FMIN_S_def";
val _ = emit "dfn_primeFMSUB_D_def_typed" "dfn'FMSUB_D_def";
val _ = emit "dfn_primeFMSUB_S_def_typed" "dfn'FMSUB_S_def";
val _ = emit "dfn_primeFMUL_D_def_typed" "dfn'FMUL_D_def";
val _ = emit "dfn_primeFMUL_S_def_typed" "dfn'FMUL_S_def";
val _ = emit "dfn_primeFNMADD_D_def_typed" "dfn'FNMADD_D_def";
val _ = emit "dfn_primeFNMADD_S_def_typed" "dfn'FNMADD_S_def";
val _ = emit "dfn_primeFNMSUB_D_def_typed" "dfn'FNMSUB_D_def";
val _ = emit "dfn_primeFNMSUB_S_def_typed" "dfn'FNMSUB_S_def";
val _ = emit "dfn_primeFSQRT_D_def_typed" "dfn'FSQRT_D_def";
val _ = emit "dfn_primeFSQRT_S_def_typed" "dfn'FSQRT_S_def";
val _ = emit "dfn_primeFSUB_D_def_typed" "dfn'FSUB_D_def";
val _ = emit "dfn_primeFSUB_S_def_typed" "dfn'FSUB_S_def";
val _ = emit "write_primeDelta_def_typed" "write'Delta_def";
val _ = emit "write_primeFPRD_def_typed" "write'FPRD_def";
val _ = emit "write_primeFPRS_def_typed" "write'FPRS_def";
val _ = emit "write_primeGPR_def_typed" "write'GPR_def";
val _ = emit "write_primeMCSR_def_typed" "write'MCSR_def";
val _ = emit "write_primeNextFetch_def_typed" "write'NextFetch_def";
val _ = emit "write_primefcsr_def_typed" "write'fcsr_def";
val _ = emit "write_primefpr_def_typed" "write'fpr_def";
val _ = emit "write_primegpr_def_typed" "write'gpr_def";
val _ = emit "dfn_primeAMOADD_D_def_typed" "dfn'AMOADD_D_def";
val _ = emit "dfn_primeAMOADD_W_def_typed" "dfn'AMOADD_W_def";
val _ = emit "dfn_primeAMOAND_D_def_typed" "dfn'AMOAND_D_def";
val _ = emit "dfn_primeAMOAND_W_def_typed" "dfn'AMOAND_W_def";
val _ = emit "dfn_primeAMOOR_D_def_typed" "dfn'AMOOR_D_def";
val _ = emit "dfn_primeAMOOR_W_def_typed" "dfn'AMOOR_W_def";
val _ = emit "dfn_primeAMOXOR_D_def_typed" "dfn'AMOXOR_D_def";
val _ = emit "dfn_primeAMOXOR_W_def_typed" "dfn'AMOXOR_W_def";
val _ = emit "dfn_primeAMOMAXU_D_def_typed" "dfn'AMOMAXU_D_def";
val _ = emit "dfn_primeAMOMAXU_W_def_typed" "dfn'AMOMAXU_W_def";
val _ = emit "dfn_primeAMOMAX_D_def_typed" "dfn'AMOMAX_D_def";
val _ = emit "dfn_primeAMOMAX_W_def_typed" "dfn'AMOMAX_W_def";
val _ = emit "dfn_primeAMOMINU_D_def_typed" "dfn'AMOMINU_D_def";
val _ = emit "dfn_primeAMOMINU_W_def_typed" "dfn'AMOMINU_W_def";
val _ = emit "dfn_primeAMOMIN_D_def_typed" "dfn'AMOMIN_D_def";
val _ = emit "dfn_primeAMOMIN_W_def_typed" "dfn'AMOMIN_W_def";
val _ = emit "dfn_primeAMOSWAP_D_def_typed" "dfn'AMOSWAP_D_def";
val _ = emit "dfn_primeAMOSWAP_W_def_typed" "dfn'AMOSWAP_W_def";
val _ = emit "signalAddressException_def_typed" "signalAddressException_def";
val _ = emit "checkCSROp_def_typed" "checkCSROp_def";
val _ = emit "check_CSR_access_def_typed" "check_CSR_access_def";
val _ = emit "csrPR_def_typed" "csrPR_def";
val _ = emit "csrRW_def_typed" "csrRW_def";
val _ = emit "curPrivilege_def_typed" "curPrivilege_def";
val _ = emit "is_CSR_defined_def_typed" "is_CSR_defined_def";
val _ = emit "privLevel_def_typed" "privLevel_def";
val _ = emit "CSR_def_typed" "CSR_def";
val _ = emit "CSRMap_def_typed" "CSRMap_def";
val _ = emit "sendIPI_def_typed" "sendIPI_def";
val _ = emit "writeCSR_def_typed" "writeCSR_def";
val _ = emit "rec_primeFPCSR_def_typed" "rec'FPCSR_def";
val _ = emit "reg_primeFPCSR_def_typed" "reg'FPCSR_def";
val _ = emit "write_primeCSRMap_def_typed" "write'CSRMap_def";
val _ = emit "write_primeCSR_def_typed" "write'CSR_def";
val _ = emit "write_primerec_primeFPCSR_def_typed" "write'rec'FPCSR_def";
val _ = emit "write_primereg_primeFPCSR_def_typed" "write'reg'FPCSR_def";
val _ = emit "dfn_primeCSRRCI_def_typed" "dfn'CSRRCI_def";
val _ = emit "dfn_primeCSRRC_def_typed" "dfn'CSRRC_def";
val _ = emit "dfn_primeCSRRSI_def_typed" "dfn'CSRRSI_def";
val _ = emit "dfn_primeCSRRS_def_typed" "dfn'CSRRS_def";
val _ = emit "dfn_primeCSRRWI_def_typed" "dfn'CSRRWI_def";
val _ = emit "dfn_primeCSRRW_def_typed" "dfn'CSRRW_def";
val _ = emit "dfn_primeBEQ_def_typed" "dfn'BEQ_def";
val _ = emit "dfn_primeBGEU_def_typed" "dfn'BGEU_def";
val _ = emit "dfn_primeBGE_def_typed" "dfn'BGE_def";
val _ = emit "dfn_primeBLTU_def_typed" "dfn'BLTU_def";
val _ = emit "dfn_primeBLT_def_typed" "dfn'BLT_def";
val _ = emit "dfn_primeBNE_def_typed" "dfn'BNE_def";
val _ = emit "dfn_primeFETCH_FAULT_def_typed" "dfn'FETCH_FAULT_def";
val _ = emit "dfn_primeFETCH_MISALIGNED_def_typed" "dfn'FETCH_MISALIGNED_def";
val _ = emit "dfn_primeMRTS_def_typed" "dfn'MRTS_def";
val _ = emit "write_primeSCSR_def_typed" "write'SCSR_def";
val _ = emit "Decode_def_typed" "Decode_def";
val _ = emit "DecodeRVC_def_typed" "DecodeRVC_def";
val _ = emit "boolify16_def_typed" "boolify16_def";
val _ = emit "boolify32_def_typed" "boolify32_def";
val _ = emit "boolify8_def_typed" "boolify8_def";
val _ = emit "asImm12_def_typed" "asImm12_def";
val _ = emit "asImm20_def_typed" "asImm20_def";
val _ = emit "asSImm12_def_typed" "asSImm12_def";
val _ = emit "dfn_primeDIVUW_def_typed" "dfn'DIVUW_def";
val _ = emit "dfn_primeDIVU_def_typed" "dfn'DIVU_def";
val _ = emit "dfn_primeDIVW_def_typed" "dfn'DIVW_def";
val _ = emit "dfn_primeDIV_def_typed" "dfn'DIV_def";
val _ = emit "dfn_primeREMUW_def_typed" "dfn'REMUW_def";
val _ = emit "dfn_primeREMU_def_typed" "dfn'REMU_def";
val _ = emit "dfn_primeREMW_def_typed" "dfn'REMW_def";
val _ = emit "dfn_primeREM_def_typed" "dfn'REM_def";
val _ = emit "Encode_def_typed" "Encode_def";
val _ = emit "Itype_def_typed" "Itype_def";
val _ = emit "R4type_def_typed" "R4type_def";
val _ = emit "Rtype_def_typed" "Rtype_def";
val _ = emit "SBtype_def_typed" "SBtype_def";
val _ = emit "Stype_def_typed" "Stype_def";
val _ = emit "UJtype_def_typed" "UJtype_def";
val _ = emit "Utype_def_typed" "Utype_def";
val _ = emit "amofunc_def_typed" "amofunc_def";
val _ = emit "opc_def_typed" "opc_def";
val _ = emit "dfn_primeFMV_D_X_def_typed" "dfn'FMV_D_X_def";
val _ = emit "dfn_primeFMV_S_X_def_typed" "dfn'FMV_S_X_def";
val _ = emit "dfn_primeFMV_X_D_def_typed" "dfn'FMV_X_D_def";
val _ = emit "dfn_primeFMV_X_S_def_typed" "dfn'FMV_X_S_def";
val _ = emit "dfn_primeFSGNJN_D_def_typed" "dfn'FSGNJN_D_def";
val _ = emit "dfn_primeFSGNJN_S_def_typed" "dfn'FSGNJN_S_def";
val _ = emit "dfn_primeFSGNJX_D_def_typed" "dfn'FSGNJX_D_def";
val _ = emit "dfn_primeFSGNJX_S_def_typed" "dfn'FSGNJX_S_def";
val _ = emit "dfn_primeFSGNJ_D_def_typed" "dfn'FSGNJ_D_def";
val _ = emit "dfn_primeFSGNJ_S_def_typed" "dfn'FSGNJ_S_def";
val _ = emit "dfn_primeFLD_def_typed" "dfn'FLD_def";
val _ = emit "dfn_primeFLW_def_typed" "dfn'FLW_def";
val _ = emit "dfn_primeFSD_def_typed" "dfn'FSD_def";
val _ = emit "dfn_primeFSW_def_typed" "dfn'FSW_def";
val _ = emit "Fetch_def_typed" "Fetch_def";
val _ = emit "dfn_primeADDI_def_typed" "dfn'ADDI_def";
val _ = emit "dfn_primeANDI_def_typed" "dfn'ANDI_def";
val _ = emit "dfn_primeORI_def_typed" "dfn'ORI_def";
val _ = emit "dfn_primeXORI_def_typed" "dfn'XORI_def";
val _ = emit "dfn_primeSLLIW_def_typed" "dfn'SLLIW_def";
val _ = emit "dfn_primeSLLI_def_typed" "dfn'SLLI_def";
val _ = emit "dfn_primeSRAIW_def_typed" "dfn'SRAIW_def";
val _ = emit "dfn_primeSRAI_def_typed" "dfn'SRAI_def";
val _ = emit "dfn_primeSRLIW_def_typed" "dfn'SRLIW_def";
val _ = emit "dfn_primeSRLI_def_typed" "dfn'SRLI_def";
val _ = emit "dfn_primeLBU_def_typed" "dfn'LBU_def";
val _ = emit "dfn_primeLB_def_typed" "dfn'LB_def";
val _ = emit "dfn_primeLD_def_typed" "dfn'LD_def";
val _ = emit "dfn_primeLHU_def_typed" "dfn'LHU_def";
val _ = emit "dfn_primeLH_def_typed" "dfn'LH_def";
val _ = emit "dfn_primeLWU_def_typed" "dfn'LWU_def";
val _ = emit "dfn_primeLW_def_typed" "dfn'LW_def";
val _ = emit "architecture_def_typed" "architecture_def";
val _ = emit "curArch_def_typed" "curArch_def";
val _ = emit "in32BitMode_def_typed" "in32BitMode_def";
val _ = emit "dfn_primeSB_def_typed" "dfn'SB_def";
val _ = emit "dfn_primeSD_def_typed" "dfn'SD_def";
val _ = emit "dfn_primeSH_def_typed" "dfn'SH_def";
val _ = emit "dfn_primeSW_def_typed" "dfn'SW_def";
val _ = emit "dfn_primeLR_D_def_typed" "dfn'LR_D_def";
val _ = emit "dfn_primeLR_W_def_typed" "dfn'LR_W_def";
val _ = emit "dfn_primeSC_D_def_typed" "dfn'SC_D_def";
val _ = emit "dfn_primeSC_W_def_typed" "dfn'SC_W_def";
val _ = emit "checkMemPermission_def_typed" "checkMemPermission_def";
val _ = emit "curASID_def_typed" "curASID_def";
val _ = emit "rawReadData_def_typed" "rawReadData_def";
val _ = emit "rawWriteData_def_typed" "rawWriteData_def";
val _ = emit "vmType_def_typed" "vmType_def";
val _ = emit "raise_primeexception_def_typed" "raise'exception_def";
val _ = emit "flushTLB_def_typed" "flushTLB_def";
val _ = emit "dfn_primeSFENCE_VM_def_typed" "dfn'SFENCE_VM_def";
val _ = emit "addToTLB_def_typed" "addToTLB_def";
val _ = emit "ASID_SIZE_def_typed" "ASID_SIZE_def";
val _ = emit "LEVEL_BITS_def_typed" "LEVEL_BITS_def";
val _ = emit "MEM_def_typed" "MEM_def";
val _ = emit "PAGESIZE_BITS_def_typed" "PAGESIZE_BITS_def";
val _ = emit "SCSR_def_typed" "SCSR_def";
val _ = emit "TLB_def_typed" "TLB_def";
val _ = emit "TLBEntries_def_typed" "TLBEntries_def";
val _ = emit "isGlobal_def_typed" "isGlobal_def";
val _ = emit "privilege_def_typed" "privilege_def";
val _ = emit "rec_primeSV_PTE_def_typed" "rec'SV_PTE_def";
val _ = emit "rec_primeSV_Vaddr_def_typed" "rec'SV_Vaddr_def";
val _ = emit "reg_primeSV_PTE_def_typed" "reg'SV_PTE_def";
val _ = emit "write_primeMEM_def_typed" "write'MEM_def";
val _ = emit "write_primeTLB_def_typed" "write'TLB_def";
val _ = emit "lookupTLB_def_typed" "lookupTLB_def";
val _ = emit "mkTLBEntry_def_typed" "mkTLBEntry_def";
val _ = emit "translate64_def_typed" "translate64_def";
val _ = emit "translateAddr_def_typed" "translateAddr_def";
val _ = emit "walk64_def_typed" "walk64_def";
val _ = emit "rec_primemcause_def_typed" "rec'mcause_def";
val _ = emit "rec_primemcpuid_def_typed" "rec'mcpuid_def";
val _ = emit "rec_primemie_def_typed" "rec'mie_def";
val _ = emit "rec_primemimpid_def_typed" "rec'mimpid_def";
val _ = emit "rec_primemip_def_typed" "rec'mip_def";
val _ = emit "rec_primemstatus_def_typed" "rec'mstatus_def";
val _ = emit "rec_primemtdeleg_def_typed" "rec'mtdeleg_def";
val _ = emit "reg_primemcause_def_typed" "reg'mcause_def";
val _ = emit "reg_primemcpuid_def_typed" "reg'mcpuid_def";
val _ = emit "reg_primemie_def_typed" "reg'mie_def";
val _ = emit "reg_primemimpid_def_typed" "reg'mimpid_def";
val _ = emit "reg_primemip_def_typed" "reg'mip_def";
val _ = emit "reg_primemstatus_def_typed" "reg'mstatus_def";
val _ = emit "reg_primemtdeleg_def_typed" "reg'mtdeleg_def";
val _ = emit "dfn_primeMULHSU_def_typed" "dfn'MULHSU_def";
val _ = emit "dfn_primeMULHU_def_typed" "dfn'MULHU_def";
val _ = emit "dfn_primeMULH_def_typed" "dfn'MULH_def";
val _ = emit "dfn_primeMULW_def_typed" "dfn'MULW_def";
val _ = emit "dfn_primeMUL_def_typed" "dfn'MUL_def";
val _ = emit "PC_def_typed" "PC_def";
val _ = emit "rawReadInst_def_typed" "rawReadInst_def";
val _ = emit "write_primeSkip_def_typed" "write'Skip_def";
val _ = emit "dfn_primeADD_def_typed" "dfn'ADD_def";
val _ = emit "dfn_primeAND_def_typed" "dfn'AND_def";
val _ = emit "dfn_primeOR_def_typed" "dfn'OR_def";
val _ = emit "dfn_primeSUB_def_typed" "dfn'SUB_def";
val _ = emit "dfn_primeXOR_def_typed" "dfn'XOR_def";
val _ = emit "dfn_primeSLLW_def_typed" "dfn'SLLW_def";
val _ = emit "dfn_primeSLL_def_typed" "dfn'SLL_def";
val _ = emit "dfn_primeSRAW_def_typed" "dfn'SRAW_def";
val _ = emit "dfn_primeSRA_def_typed" "dfn'SRA_def";
val _ = emit "dfn_primeSRLW_def_typed" "dfn'SRLW_def";
val _ = emit "dfn_primeSRL_def_typed" "dfn'SRL_def";
val _ = emit "ReserveLoad_def_typed" "ReserveLoad_def";
val _ = emit "matchLoadReservation_def_typed" "matchLoadReservation_def";
val _ = emit "write_primeReserveLoad_def_typed" "write'ReserveLoad_def";
val _ = emit "Run_def_typed" "Run_def";
val _ = emit "dfn_primeSLTIU_def_typed" "dfn'SLTIU_def";
val _ = emit "dfn_primeSLTI_def_typed" "dfn'SLTI_def";
val _ = emit "dfn_primeSLTU_def_typed" "dfn'SLTU_def";
val _ = emit "dfn_primeSLT_def_typed" "dfn'SLT_def";
val _ = emit "extStatus_def_typed" "extStatus_def";
val _ = emit "isValidVM_def_typed" "isValidVM_def";
val _ = emit "lift_mie_sie_def_typed" "lift_mie_sie_def";
val _ = emit "lift_mip_sip_def_typed" "lift_mip_sip_def";
val _ = emit "lift_mstatus_sstatus_def_typed" "lift_mstatus_sstatus_def";
val _ = emit "lower_sie_mie_def_typed" "lower_sie_mie_def";
val _ = emit "lower_sip_mip_def_typed" "lower_sip_mip_def";
val _ = emit "lower_sstatus_mstatus_def_typed" "lower_sstatus_mstatus_def";
val _ = emit "update_mstatus_def_typed" "update_mstatus_def";
val _ = emit "rec_primesie_def_typed" "rec'sie_def";
val _ = emit "rec_primesip_def_typed" "rec'sip_def";
val _ = emit "rec_primesstatus_def_typed" "rec'sstatus_def";
val _ = emit "reg_primesie_def_typed" "reg'sie_def";
val _ = emit "reg_primesip_def_typed" "reg'sip_def";
val _ = emit "reg_primesstatus_def_typed" "reg'sstatus_def";
val _ = emit "signalEnvCall_def_typed" "signalEnvCall_def";
val _ = emit "dfn_primeEBREAK_def_typed" "dfn'EBREAK_def";
val _ = emit "dfn_primeECALL_def_typed" "dfn'ECALL_def";
val _ = emit "dfn_primeERET_def_typed" "dfn'ERET_def";
val _ = emit "dfn_primeUnknownInstruction_def_typed" "dfn'UnknownInstruction_def";
val _ = emit "Skip_def_typed" "Skip_def";
val _ = emit "branchTo_def_typed" "branchTo_def";
val _ = emit "dfn_primeAUIPC_def_typed" "dfn'AUIPC_def";
val _ = emit "dfn_primeJALR_def_typed" "dfn'JALR_def";
val _ = emit "dfn_primeJAL_def_typed" "dfn'JAL_def";
val _ = emit "dfn_primeLUI_def_typed" "dfn'LUI_def";
val _ = emit "dfn_primeADDIW_def_typed" "dfn'ADDIW_def";
val _ = emit "dfn_primeADDW_def_typed" "dfn'ADDW_def";
val _ = emit "dfn_primeSUBW_def_typed" "dfn'SUBW_def";
val _ = emit "write_primePC_def_typed" "write'PC_def";
val _ = emit "AMO_typed" "AMO";
val _ = emit "Architecture_typed" "Architecture";
val _ = emit "ArithI_typed" "ArithI";
val _ = emit "ArithR_typed" "ArithR";
val _ = emit "Branch_typed" "Branch";
val _ = emit "ExceptionType_typed" "ExceptionType";
val _ = emit "ExtStatus_typed" "ExtStatus";
val _ = emit "FArith_typed" "FArith";
val _ = emit "FConv_typed" "FConv";
val _ = emit "FPCSR_typed" "FPCSR";
val _ = emit "FPLoad_typed" "FPLoad";
val _ = emit "FPStore_typed" "FPStore";
val _ = emit "FetchResult_typed" "FetchResult";
val _ = emit "HypervisorCSR_typed" "HypervisorCSR";
val _ = emit "Internal_typed" "Internal";
val _ = emit "Interrupt_typed" "Interrupt";
val _ = emit "Load_typed" "Load";
val _ = emit "MachineCSR_typed" "MachineCSR";
val _ = emit "MulDiv_typed" "MulDiv";
val _ = emit "Privilege_typed" "Privilege";
val _ = emit "Rounding_typed" "Rounding";
val _ = emit "SV_PTE_typed" "SV_PTE";
val _ = emit "SV_Vaddr_typed" "SV_Vaddr";
val _ = emit "Shift_typed" "Shift";
val _ = emit "StateDelta_typed" "StateDelta";
val _ = emit "Store_typed" "Store";
val _ = emit "SupervisorCSR_typed" "SupervisorCSR";
val _ = emit "SynchronousTrap_typed" "SynchronousTrap";
val _ = emit "System_typed" "System";
val _ = emit "TLBEntry_typed" "TLBEntry";
val _ = emit "TransferControl_typed" "TransferControl";
val _ = emit "UserCSR_typed" "UserCSR";
val _ = emit "VM_Mode_typed" "VM_Mode";
val _ = emit "accessType_typed" "accessType";
val _ = emit "exception_typed" "exception";
val _ = emit "fetchType_typed" "fetchType";
val _ = emit "instruction_typed" "instruction";
val _ = emit "mcause_typed" "mcause";
val _ = emit "mcpuid_typed" "mcpuid";
val _ = emit "mie_typed" "mie";
val _ = emit "mimpid_typed" "mimpid";
val _ = emit "mip_typed" "mip";
val _ = emit "mstatus_typed" "mstatus";
val _ = emit "mtdeleg_typed" "mtdeleg";
val _ = emit "rawInstType_typed" "rawInstType";
val _ = emit "riscv_state_typed" "riscv_state";
val _ = emit "rvc_typed" "rvc";
val _ = emit "sie_typed" "sie";
val _ = emit "sip_typed" "sip";
val _ = emit "sstatus_typed" "sstatus";

val _ = OS.Process.exit OS.Process.success;
