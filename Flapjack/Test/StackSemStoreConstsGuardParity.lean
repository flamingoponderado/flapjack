import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsGuard

open Flapjack Flapjack.StackSemStoreConstsGuard
open Flapjack.Compiler.Backend.StackLang

-- Original HOL rows: scripts/hol-probes/stacksem_store_consts_guard_probe.out.
example (code : Spt (HolProg 8)) : checkStoreConstsOpt 4 5 none code = true := rfl
example : checkStoreConstsOpt 4 5 (some 7) (Spt.ln : Spt (HolProg 8)) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.seq (.storeConsts 4 5 none) (.ret 0) : HolProg 8) .ln) = true := by cbv
example : checkStoreConstsOpt 4 5 (some 8)
    (sptInsert 7 (.seq (.storeConsts 4 5 none) (.ret 0) : HolProg 8) .ln) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.seq (.storeConsts 6 5 none) (.ret 0) : HolProg 8) .ln) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.seq (.storeConsts 4 6 none) (.ret 0) : HolProg 8) .ln) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.seq (.storeConsts 4 5 (some 9)) (.ret 0) : HolProg 8) .ln) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.seq (.storeConsts 4 5 none) (.ret 1) : HolProg 8) .ln) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.storeConsts 4 5 none : HolProg 8) .ln) = false := by cbv
example : checkStoreConstsOpt 4 5 (some 7)
    (sptInsert 7 (.seq (.ret 0) (.storeConsts 4 5 none) : HolProg 8) .ln) = false := by cbv
