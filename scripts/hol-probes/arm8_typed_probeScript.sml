(* Typed source declarations for arm8 (task 154). Free variables of a
   theorem conclusion are printed as a ∀* prefix; HOL stores them as
   implicitly universally quantified, so their order is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/examples/l3-machine-code/arm8/model") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/common") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/lib") ::
  !loadPath;
load "arm8Theory";
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

val thy = "arm8";
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

val _ = emit "ShiftType_typed" "ShiftType";
val _ = emit "MoveWideOp_typed" "MoveWideOp";
val _ = emit "ProcState_typed" "ProcState";
val _ = emit "TCR_EL1_typed" "TCR_EL1";
val _ = emit "TCR_EL2_EL3_typed" "TCR_EL2_EL3";
val _ = emit "SCTLRType_typed" "SCTLRType";
val _ = emit "BranchType_typed" "BranchType";
val _ = emit "exception_typed" "exception";
val _ = emit "arm8_state_typed" "arm8_state";
val _ = emit "AccType_typed" "AccType";
val _ = emit "ExtendType_typed" "ExtendType";
val _ = emit "LogicalOp_typed" "LogicalOp";
val _ = emit "MemOp_typed" "MemOp";
val _ = emit "MemBarrierOp_typed" "MemBarrierOp";
val _ = emit "RevOp_typed" "RevOp";
val _ = emit "SystemHintOp_typed" "SystemHintOp";
val _ = emit "PSTATEField_typed" "PSTATEField";
val _ = emit "System_typed" "System";
val _ = emit "Debug_typed" "Debug";
val _ = emit "LoadStore_typed" "LoadStore";
val _ = emit "Branch_typed" "Branch";
val _ = emit "CRCExt_typed" "CRCExt";
val _ = emit "Data_typed" "Data";
val _ = emit "instruction_typed" "instruction";
val _ = emit "MachineCode_typed" "MachineCode";
val _ = emit "raise_primeexception_def_typed" "raise'exception_def";
val _ = emit "TranslationRegime_def_typed" "TranslationRegime_def";
val _ = emit "SCTLR_def_typed" "SCTLR_def";
val _ = emit "Align_def_typed" "Align_def";
val _ = emit "Aligned_def_typed" "Aligned_def";
val _ = emit "CheckAlignment_def_typed" "CheckAlignment_def";
val _ = emit "ByteList_def_typed" "ByteList_def";
val _ = emit "BigEndianReverse_def_typed" "BigEndianReverse_def";
val _ = emit "BigEndian_def_typed" "BigEndian_def";
val _ = emit "Mem_def_typed" "Mem_def";
val _ = emit "Fetch_def_typed" "Fetch_def";
val _ = emit "NoOperation_def_typed" "NoOperation_def";
val _ = emit "LoadStoreAcquireN_def_typed" "LoadStoreAcquireN_def";
val _ = emit "LoadStoreAcquire_def_typed" "LoadStoreAcquire_def";
val _ = emit "LoadStorePairN_def_typed" "LoadStorePairN_def";
val _ = emit "LoadStorePair_def_typed" "LoadStorePair_def";
val _ = emit "DecodeRegExtend_def_typed" "DecodeRegExtend_def";
val _ = emit "LoadStoreRegister_def_typed" "LoadStoreRegister_def";
val _ = emit "LoadStoreImmediateN_def_typed" "LoadStoreImmediateN_def";
val _ = emit "LoadStoreImmediate_def_typed" "LoadStoreImmediate_def";
val _ = emit "HighestSetBit_def_typed" "HighestSetBit_def";
val _ = emit "Ones_def_typed" "Ones_def";
val _ = emit "Replicate_def_typed" "Replicate_def";
val _ = emit "DecodeBitMasks_def_typed" "DecodeBitMasks_def";
val _ = emit "DecodeShift_def_typed" "DecodeShift_def";
val _ = emit "DecodeLogicalOp_def_typed" "DecodeLogicalOp_def";
val _ = emit "Decode_def_typed" "Decode_def";
val _ = emit "dfn_primeUnallocated_def_typed" "dfn'Unallocated_def";
val _ = emit "dfn_primeSystemInstruction_def_typed" "dfn'SystemInstruction_def";
val _ = emit "dfn_primeSupervisorCall_def_typed" "dfn'SupervisorCall_def";
val _ = emit "dfn_primeSecureMonitorCall_def_typed" "dfn'SecureMonitorCall_def";
val _ = emit "dfn_primeMoveSystemRegister_def_typed" "dfn'MoveSystemRegister_def";
val _ = emit "dfn_primeMoveImmediateProcState_def_typed" "dfn'MoveImmediateProcState_def";
val _ = emit "dfn_primeHypervisorCall_def_typed" "dfn'HypervisorCall_def";
val _ = emit "dfn_primeExceptionReturn_def_typed" "dfn'ExceptionReturn_def";
val _ = emit "dfn_primeReserved_def_typed" "dfn'Reserved_def";
val _ = emit "dfn_primeMemoryBarrier_def_typed" "dfn'MemoryBarrier_def";
val _ = emit "X_def_typed" "X_def";
val _ = emit "Extend_def_typed" "Extend_def";
val _ = emit "ExtendValue_def_typed" "ExtendValue_def";
val _ = emit "ExtendReg_def_typed" "ExtendReg_def";
val _ = emit "SP_def_typed" "SP_def";
val _ = emit "CheckSPAlignment_def_typed" "CheckSPAlignment_def";
val _ = emit "write_primeMem_def_typed" "write'Mem_def";
val _ = emit "ExtendWord_def_typed" "ExtendWord_def";
val _ = emit "write_primeX_def_typed" "write'X_def";
val _ = emit "write_primeSP_def_typed" "write'SP_def";
val _ = emit "LoadStoreSingle_def_typed" "LoadStoreSingle_def";
val _ = emit "dfn_primeLoadStoreRegister_def_typed" "dfn'LoadStoreRegister_def";
val _ = emit "dfn_primeLoadStorePair_def_typed" "dfn'LoadStorePair_def";
val _ = emit "dfn_primeLoadStoreImmediate_def_typed" "dfn'LoadStoreImmediate_def";
val _ = emit "ExclusiveMonitorStatus_def_typed" "ExclusiveMonitorStatus_def";
val _ = emit "ExclusiveMonitorPass_def_typed" "ExclusiveMonitorPass_def";
val _ = emit "dfn_primeLoadStoreAcquirePair_def_typed" "dfn'LoadStoreAcquirePair_def";
val _ = emit "dfn_primeLoadStoreAcquire_def_typed" "dfn'LoadStoreAcquire_def";
val _ = emit "dfn_primeLoadLiteral_def_typed" "dfn'LoadLiteral_def";
val _ = emit "dfn_primeHint_def_typed" "dfn'Hint_def";
val _ = emit "dfn_primeHalt_def_typed" "dfn'Halt_def";
val _ = emit "dfn_primeDebugSwitch_def_typed" "dfn'DebugSwitch_def";
val _ = emit "dfn_primeDebugRestore_def_typed" "dfn'DebugRestore_def";
val _ = emit "dfn_primeBreakpoint_def_typed" "dfn'Breakpoint_def";
val _ = emit "ShiftValue_def_typed" "ShiftValue_def";
val _ = emit "ShiftReg_def_typed" "ShiftReg_def";
val _ = emit "dfn_primeShift_def_typed" "dfn'Shift_def";
val _ = emit "dfn_primeReverse_def_typed" "dfn'Reverse_def";
val _ = emit "dfn_primeMultiplyHigh_def_typed" "dfn'MultiplyHigh_def";
val _ = emit "dfn_primeMultiplyAddSubLong_def_typed" "dfn'MultiplyAddSubLong_def";
val _ = emit "dfn_primeMultiplyAddSub_def_typed" "dfn'MultiplyAddSub_def";
val _ = emit "dfn_primeMoveWide_def_typed" "dfn'MoveWide_def";
val _ = emit "SetTheFlags_def_typed" "SetTheFlags_def";
val _ = emit "dfn_primeLogicalShiftedRegister_def_typed" "dfn'LogicalShiftedRegister_def";
val _ = emit "dfn_primeLogicalImmediate_def_typed" "dfn'LogicalImmediate_def";
val _ = emit "dfn_primeExtractRegister_def_typed" "dfn'ExtractRegister_def";
val _ = emit "dfn_primeDivision_def_typed" "dfn'Division_def";
val _ = emit "CountLeadingZeroBits_def_typed" "CountLeadingZeroBits_def";
val _ = emit "CountLeadingSignBits_def_typed" "CountLeadingSignBits_def";
val _ = emit "dfn_primeCountLeading_def_typed" "dfn'CountLeading_def";
val _ = emit "ConditionTest_def_typed" "ConditionTest_def";
val _ = emit "ConditionHolds_def_typed" "ConditionHolds_def";
val _ = emit "dfn_primeConditionalSelect_def_typed" "dfn'ConditionalSelect_def";
val _ = emit "AddWithCarry_def_typed" "AddWithCarry_def";
val _ = emit "dfn_primeConditionalCompareRegister_def_typed" "dfn'ConditionalCompareRegister_def";
val _ = emit "dfn_primeConditionalCompareImmediate_def_typed" "dfn'ConditionalCompareImmediate_def";
val _ = emit "dfn_primeBitfieldMove_def_typed" "dfn'BitfieldMove_def";
val _ = emit "dfn_primeAddSubShiftedRegister_def_typed" "dfn'AddSubShiftedRegister_def";
val _ = emit "dfn_primeAddSubImmediate_def_typed" "dfn'AddSubImmediate_def";
val _ = emit "dfn_primeAddSubExtendRegister_def_typed" "dfn'AddSubExtendRegister_def";
val _ = emit "dfn_primeAddSubCarry_def_typed" "dfn'AddSubCarry_def";
val _ = emit "dfn_primeClearExclusive_def_typed" "dfn'ClearExclusive_def";
val _ = emit "Zeros_def_typed" "Zeros_def";
val _ = emit "Poly32Mod2_loop_def_typed" "Poly32Mod2_loop_def";
val _ = emit "Poly32Mod2_def_typed" "Poly32Mod2_def";
val _ = emit "dfn_primeCRC_def_typed" "dfn'CRC_def";
val _ = emit "Hint_Branch_def_typed" "Hint_Branch_def";
val _ = emit "BranchTo_def_typed" "BranchTo_def";
val _ = emit "dfn_primeTestBitAndBranch_def_typed" "dfn'TestBitAndBranch_def";
val _ = emit "dfn_primeCompareAndBranch_def_typed" "dfn'CompareAndBranch_def";
val _ = emit "dfn_primeBranchRegister_def_typed" "dfn'BranchRegister_def";
val _ = emit "dfn_primeBranchImmediate_def_typed" "dfn'BranchImmediate_def";
val _ = emit "dfn_primeBranchConditional_def_typed" "dfn'BranchConditional_def";
val _ = emit "dfn_primeAddress_def_typed" "dfn'Address_def";
val _ = emit "Run_def_typed" "Run_def";
val _ = emit "Next_def_typed" "Next_def";
val _ = emit "e_system_def_typed" "e_system_def";
val _ = emit "e_LoadStoreRegister_def_typed" "e_LoadStoreRegister_def";
val _ = emit "e_LoadStoreImmediate_def_typed" "e_LoadStoreImmediate_def";
val _ = emit "e_load_store_def_typed" "e_load_store_def";
val _ = emit "e_debug_def_typed" "e_debug_def";
val _ = emit "e_sf_def_typed" "e_sf_def";
val _ = emit "EncodeLogicalOp_def_typed" "EncodeLogicalOp_def";
val _ = emit "CountTrailing_def_typed" "CountTrailing_def";
val _ = emit "EncodeBitMaskAux_def_typed" "EncodeBitMaskAux_def";
val _ = emit "EncodeBitMask_def_typed" "EncodeBitMask_def";
val _ = emit "e_data_def_typed" "e_data_def";
val _ = emit "e_crc_def_typed" "e_crc_def";
val _ = emit "e_branch_def_typed" "e_branch_def";
val _ = emit "Encode_def_typed" "Encode_def";

val _ = OS.Process.exit OS.Process.success;
