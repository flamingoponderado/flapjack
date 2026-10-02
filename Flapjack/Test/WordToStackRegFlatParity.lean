import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundFlat

namespace Flapjack.Test.WordToStackRegFlatParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.RegisterBoundFlat
/- Same-input original guard EVALs and direct compiler-predicate EVALs.
Alloc uses original case applications to avoid computing irrelevant bitmaps.
Fresh outputs: word_to_stack_reg_flat_probe.out; regression evidence, not equivalence. -/

-- rbf_1_0_negative_odd
example : postAllocConventionsHOL (width := 1) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_1_0_negative_raise_bad
example : postAllocConventionsHOL (width := 1) 4 (.raise 0) = false := by cbv

-- rbf_1_0_negative_return_bad
example : postAllocConventionsHOL (width := 1) 4 (.return 2 [0]) = false := by cbv

-- rbf_1_0_negative_alloc_bad
example : postAllocConventionsHOL (width := 1) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_1_0_negative_alloc_cutset
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_1_0_negative_consts_bad
example : postAllocConventionsHOL (width := 1) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_1_0_negative_install_bad
example : postAllocConventionsHOL (width := 1) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_1_0_negative_ffi_bad
example : postAllocConventionsHOL (width := 1) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_1_1_negative_odd
example : postAllocConventionsHOL (width := 1) 8 (.get 3 .currHeap) = false := by cbv

-- rbf_1_1_negative_raise_bad
example : postAllocConventionsHOL (width := 1) 8 (.raise 0) = false := by cbv

-- rbf_1_1_negative_return_bad
example : postAllocConventionsHOL (width := 1) 8 (.return 2 [0]) = false := by cbv

-- rbf_1_1_negative_alloc_bad
example : postAllocConventionsHOL (width := 1) 8 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_1_1_negative_alloc_cutset
example : postAllocConventionsHOL (width := 1) 8 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_1_1_negative_consts_bad
example : postAllocConventionsHOL (width := 1) 8 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_1_1_negative_install_bad
example : postAllocConventionsHOL (width := 1) 8 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_1_1_negative_ffi_bad
example : postAllocConventionsHOL (width := 1) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_1_2_negative_odd
example : postAllocConventionsHOL (width := 1) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_1_2_negative_raise_bad
example : postAllocConventionsHOL (width := 1) 4 (.raise 0) = false := by cbv

-- rbf_1_2_negative_return_bad
example : postAllocConventionsHOL (width := 1) 4 (.return 2 [0]) = false := by cbv

-- rbf_1_2_negative_alloc_bad
example : postAllocConventionsHOL (width := 1) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_1_2_negative_alloc_cutset
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_1_2_negative_consts_bad
example : postAllocConventionsHOL (width := 1) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_1_2_negative_install_bad
example : postAllocConventionsHOL (width := 1) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_1_2_negative_ffi_bad
example : postAllocConventionsHOL (width := 1) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_2_0_negative_odd
example : postAllocConventionsHOL (width := 2) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_2_0_negative_raise_bad
example : postAllocConventionsHOL (width := 2) 4 (.raise 0) = false := by cbv

-- rbf_2_0_negative_return_bad
example : postAllocConventionsHOL (width := 2) 4 (.return 2 [0]) = false := by cbv

-- rbf_2_0_negative_alloc_bad
example : postAllocConventionsHOL (width := 2) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_2_0_negative_alloc_cutset
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_2_0_negative_consts_bad
example : postAllocConventionsHOL (width := 2) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_2_0_negative_install_bad
example : postAllocConventionsHOL (width := 2) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_2_0_negative_ffi_bad
example : postAllocConventionsHOL (width := 2) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_2_1_negative_odd
example : postAllocConventionsHOL (width := 2) 8 (.get 3 .currHeap) = false := by cbv

-- rbf_2_1_negative_raise_bad
example : postAllocConventionsHOL (width := 2) 8 (.raise 0) = false := by cbv

-- rbf_2_1_negative_return_bad
example : postAllocConventionsHOL (width := 2) 8 (.return 2 [0]) = false := by cbv

-- rbf_2_1_negative_alloc_bad
example : postAllocConventionsHOL (width := 2) 8 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_2_1_negative_alloc_cutset
example : postAllocConventionsHOL (width := 2) 8 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_2_1_negative_consts_bad
example : postAllocConventionsHOL (width := 2) 8 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_2_1_negative_install_bad
example : postAllocConventionsHOL (width := 2) 8 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_2_1_negative_ffi_bad
example : postAllocConventionsHOL (width := 2) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_2_2_negative_odd
example : postAllocConventionsHOL (width := 2) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_2_2_negative_raise_bad
example : postAllocConventionsHOL (width := 2) 4 (.raise 0) = false := by cbv

-- rbf_2_2_negative_return_bad
example : postAllocConventionsHOL (width := 2) 4 (.return 2 [0]) = false := by cbv

-- rbf_2_2_negative_alloc_bad
example : postAllocConventionsHOL (width := 2) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_2_2_negative_alloc_cutset
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_2_2_negative_consts_bad
example : postAllocConventionsHOL (width := 2) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_2_2_negative_install_bad
example : postAllocConventionsHOL (width := 2) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_2_2_negative_ffi_bad
example : postAllocConventionsHOL (width := 2) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_8_0_negative_odd
example : postAllocConventionsHOL (width := 8) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_8_0_negative_raise_bad
example : postAllocConventionsHOL (width := 8) 4 (.raise 0) = false := by cbv

-- rbf_8_0_negative_return_bad
example : postAllocConventionsHOL (width := 8) 4 (.return 2 [0]) = false := by cbv

-- rbf_8_0_negative_alloc_bad
example : postAllocConventionsHOL (width := 8) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_8_0_negative_alloc_cutset
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_8_0_negative_consts_bad
example : postAllocConventionsHOL (width := 8) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_8_0_negative_install_bad
example : postAllocConventionsHOL (width := 8) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_8_0_negative_ffi_bad
example : postAllocConventionsHOL (width := 8) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_8_1_negative_odd
example : postAllocConventionsHOL (width := 8) 8 (.get 3 .currHeap) = false := by cbv

-- rbf_8_1_negative_raise_bad
example : postAllocConventionsHOL (width := 8) 8 (.raise 0) = false := by cbv

-- rbf_8_1_negative_return_bad
example : postAllocConventionsHOL (width := 8) 8 (.return 2 [0]) = false := by cbv

-- rbf_8_1_negative_alloc_bad
example : postAllocConventionsHOL (width := 8) 8 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_8_1_negative_alloc_cutset
example : postAllocConventionsHOL (width := 8) 8 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_8_1_negative_consts_bad
example : postAllocConventionsHOL (width := 8) 8 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_8_1_negative_install_bad
example : postAllocConventionsHOL (width := 8) 8 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_8_1_negative_ffi_bad
example : postAllocConventionsHOL (width := 8) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_8_2_negative_odd
example : postAllocConventionsHOL (width := 8) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_8_2_negative_raise_bad
example : postAllocConventionsHOL (width := 8) 4 (.raise 0) = false := by cbv

-- rbf_8_2_negative_return_bad
example : postAllocConventionsHOL (width := 8) 4 (.return 2 [0]) = false := by cbv

-- rbf_8_2_negative_alloc_bad
example : postAllocConventionsHOL (width := 8) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_8_2_negative_alloc_cutset
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_8_2_negative_consts_bad
example : postAllocConventionsHOL (width := 8) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_8_2_negative_install_bad
example : postAllocConventionsHOL (width := 8) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_8_2_negative_ffi_bad
example : postAllocConventionsHOL (width := 8) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_64_0_negative_odd
example : postAllocConventionsHOL (width := 64) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_64_0_negative_raise_bad
example : postAllocConventionsHOL (width := 64) 4 (.raise 0) = false := by cbv

-- rbf_64_0_negative_return_bad
example : postAllocConventionsHOL (width := 64) 4 (.return 2 [0]) = false := by cbv

-- rbf_64_0_negative_alloc_bad
example : postAllocConventionsHOL (width := 64) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_64_0_negative_alloc_cutset
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_64_0_negative_consts_bad
example : postAllocConventionsHOL (width := 64) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_64_0_negative_install_bad
example : postAllocConventionsHOL (width := 64) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_64_0_negative_ffi_bad
example : postAllocConventionsHOL (width := 64) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_64_1_negative_odd
example : postAllocConventionsHOL (width := 64) 8 (.get 3 .currHeap) = false := by cbv

-- rbf_64_1_negative_raise_bad
example : postAllocConventionsHOL (width := 64) 8 (.raise 0) = false := by cbv

-- rbf_64_1_negative_return_bad
example : postAllocConventionsHOL (width := 64) 8 (.return 2 [0]) = false := by cbv

-- rbf_64_1_negative_alloc_bad
example : postAllocConventionsHOL (width := 64) 8 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_64_1_negative_alloc_cutset
example : postAllocConventionsHOL (width := 64) 8 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_64_1_negative_consts_bad
example : postAllocConventionsHOL (width := 64) 8 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_64_1_negative_install_bad
example : postAllocConventionsHOL (width := 64) 8 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_64_1_negative_ffi_bad
example : postAllocConventionsHOL (width := 64) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_64_2_negative_odd
example : postAllocConventionsHOL (width := 64) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_64_2_negative_raise_bad
example : postAllocConventionsHOL (width := 64) 4 (.raise 0) = false := by cbv

-- rbf_64_2_negative_return_bad
example : postAllocConventionsHOL (width := 64) 4 (.return 2 [0]) = false := by cbv

-- rbf_64_2_negative_alloc_bad
example : postAllocConventionsHOL (width := 64) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_64_2_negative_alloc_cutset
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_64_2_negative_consts_bad
example : postAllocConventionsHOL (width := 64) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_64_2_negative_install_bad
example : postAllocConventionsHOL (width := 64) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_64_2_negative_ffi_bad
example : postAllocConventionsHOL (width := 64) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_80_0_negative_odd
example : postAllocConventionsHOL (width := 80) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_80_0_negative_raise_bad
example : postAllocConventionsHOL (width := 80) 4 (.raise 0) = false := by cbv

-- rbf_80_0_negative_return_bad
example : postAllocConventionsHOL (width := 80) 4 (.return 2 [0]) = false := by cbv

-- rbf_80_0_negative_alloc_bad
example : postAllocConventionsHOL (width := 80) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_80_0_negative_alloc_cutset
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_80_0_negative_consts_bad
example : postAllocConventionsHOL (width := 80) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_80_0_negative_install_bad
example : postAllocConventionsHOL (width := 80) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_80_0_negative_ffi_bad
example : postAllocConventionsHOL (width := 80) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_80_1_negative_odd
example : postAllocConventionsHOL (width := 80) 8 (.get 3 .currHeap) = false := by cbv

-- rbf_80_1_negative_raise_bad
example : postAllocConventionsHOL (width := 80) 8 (.raise 0) = false := by cbv

-- rbf_80_1_negative_return_bad
example : postAllocConventionsHOL (width := 80) 8 (.return 2 [0]) = false := by cbv

-- rbf_80_1_negative_alloc_bad
example : postAllocConventionsHOL (width := 80) 8 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_80_1_negative_alloc_cutset
example : postAllocConventionsHOL (width := 80) 8 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_80_1_negative_consts_bad
example : postAllocConventionsHOL (width := 80) 8 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_80_1_negative_install_bad
example : postAllocConventionsHOL (width := 80) 8 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_80_1_negative_ffi_bad
example : postAllocConventionsHOL (width := 80) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_80_2_negative_odd
example : postAllocConventionsHOL (width := 80) 4 (.get 3 .currHeap) = false := by cbv

-- rbf_80_2_negative_raise_bad
example : postAllocConventionsHOL (width := 80) 4 (.raise 0) = false := by cbv

-- rbf_80_2_negative_return_bad
example : postAllocConventionsHOL (width := 80) 4 (.return 2 [0]) = false := by cbv

-- rbf_80_2_negative_alloc_bad
example : postAllocConventionsHOL (width := 80) 4 (.alloc 0 (.ln,.ln)) = false := by cbv

-- rbf_80_2_negative_alloc_cutset
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.ln,.ls ())) = false := by cbv

-- rbf_80_2_negative_consts_bad
example : postAllocConventionsHOL (width := 80) 4 (.storeConsts 0 2 4 8 []) = false := by cbv

-- rbf_80_2_negative_install_bad
example : postAllocConventionsHOL (width := 80) 4 (.install 4 2 2 4 (.ln,.ln)) = false := by cbv

-- rbf_80_2_negative_ffi_bad
example : postAllocConventionsHOL (width := 80) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 8 6 (.ln,.ln)) = false := by cbv

-- rbf_1_0_skip_guard
example : postAllocConventionsHOL (width := 1) 4 (.skip) = true := by cbv
-- rbf_1_0_skip_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_1_0_move_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 []) = true := by cbv
-- rbf_1_0_move_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_0_move_cycle_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_1_0_move_cycle_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_0_move_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_1_0_move_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_0_move_self_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_1_0_move_self_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_0_assign_guard
example : postAllocConventionsHOL (width := 1) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_1_0_assign_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_1_0_get_guard
example : postAllocConventionsHOL (width := 1) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_1_0_get_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_1_0_set_guard
example : postAllocConventionsHOL (width := 1) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_1_0_set_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_0_set_bitmap_guard
example : postAllocConventionsHOL (width := 1) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_1_0_set_bitmap_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_0_set_invalid_guard
example : postAllocConventionsHOL (width := 1) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_1_0_set_invalid_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_0_store_guard
example : postAllocConventionsHOL (width := 1) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_1_0_store_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_1_0_alloc_guard
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_1_0_alloc_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_0_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_1_0_alloc_nonempty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_0_alloc_malformed_guard
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_1_0_alloc_malformed_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_0_consts_guard
example : postAllocConventionsHOL (width := 1) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_1_0_consts_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_1_0_consts_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_1_0_consts_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_1_0_raise_guard
example : postAllocConventionsHOL (width := 1) 4 (.raise 2) = true := by cbv
-- rbf_1_0_raise_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_1_0_return_guard
example : postAllocConventionsHOL (width := 1) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_1_0_return_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_1_0_return_zero_guard
example : postAllocConventionsHOL (width := 1) 4 (.return 2 []) = true := by cbv
-- rbf_1_0_return_zero_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_1_0_break_guard
example : postAllocConventionsHOL (width := 1) 4 (.break 777) = true := by cbv
-- rbf_1_0_break_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_1_0_continue_guard
example : postAllocConventionsHOL (width := 1) 4 (.continue 777) = true := by cbv
-- rbf_1_0_continue_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_1_0_tick_guard
example : postAllocConventionsHOL (width := 1) 4 (.tick) = true := by cbv
-- rbf_1_0_tick_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_1_0_heap_guard
example : postAllocConventionsHOL (width := 1) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_1_0_heap_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_1_0_loc_guard
example : postAllocConventionsHOL (width := 1) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_1_0_loc_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_1_0_install_guard
example : postAllocConventionsHOL (width := 1) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_1_0_install_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_1_0_code_guard
example : postAllocConventionsHOL (width := 1) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_1_0_code_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_1_0_data_guard
example : postAllocConventionsHOL (width := 1) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_1_0_data_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_1_0_ffi_guard
example : postAllocConventionsHOL (width := 1) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_1_0_ffi_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_1_1_skip_guard
example : postAllocConventionsHOL (width := 1) 8 (.skip) = true := by cbv
-- rbf_1_1_skip_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_1_1_move_empty_guard
example : postAllocConventionsHOL (width := 1) 8 (.move 17 []) = true := by cbv
-- rbf_1_1_move_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_1_move_cycle_guard
example : postAllocConventionsHOL (width := 1) 8 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_1_1_move_cycle_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_1_move_spill_guard
example : postAllocConventionsHOL (width := 1) 8 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_1_1_move_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_1_move_self_guard
example : postAllocConventionsHOL (width := 1) 8 (.move 17 [(2,2)]) = true := by cbv
-- rbf_1_1_move_self_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_1_assign_guard
example : postAllocConventionsHOL (width := 1) 8 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_1_1_assign_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_1_1_get_guard
example : postAllocConventionsHOL (width := 1) 8 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_1_1_get_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_1_1_set_guard
example : postAllocConventionsHOL (width := 1) 8 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_1_1_set_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_1_set_bitmap_guard
example : postAllocConventionsHOL (width := 1) 8 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_1_1_set_bitmap_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_1_set_invalid_guard
example : postAllocConventionsHOL (width := 1) 8 (.set .handler (.const 7)) = true := by cbv
-- rbf_1_1_set_invalid_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_1_store_guard
example : postAllocConventionsHOL (width := 1) 8 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_1_1_store_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_1_1_alloc_guard
example : postAllocConventionsHOL (width := 1) 8 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_1_1_alloc_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_1_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 1) 8 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_1_1_alloc_nonempty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_1_alloc_malformed_guard
example : postAllocConventionsHOL (width := 1) 8 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_1_1_alloc_malformed_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_1_consts_guard
example : postAllocConventionsHOL (width := 1) 8 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_1_1_consts_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_1_1_consts_empty_guard
example : postAllocConventionsHOL (width := 1) 8 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_1_1_consts_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_1_1_raise_guard
example : postAllocConventionsHOL (width := 1) 8 (.raise 2) = true := by cbv
-- rbf_1_1_raise_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_1_1_return_guard
example : postAllocConventionsHOL (width := 1) 8 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_1_1_return_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_1_1_return_zero_guard
example : postAllocConventionsHOL (width := 1) 8 (.return 2 []) = true := by cbv
-- rbf_1_1_return_zero_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_1_1_break_guard
example : postAllocConventionsHOL (width := 1) 8 (.break 777) = true := by cbv
-- rbf_1_1_break_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_1_1_continue_guard
example : postAllocConventionsHOL (width := 1) 8 (.continue 777) = true := by cbv
-- rbf_1_1_continue_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_1_1_tick_guard
example : postAllocConventionsHOL (width := 1) 8 (.tick) = true := by cbv
-- rbf_1_1_tick_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_1_1_heap_guard
example : postAllocConventionsHOL (width := 1) 8 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_1_1_heap_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_1_1_loc_guard
example : postAllocConventionsHOL (width := 1) 8 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_1_1_loc_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_1_1_install_guard
example : postAllocConventionsHOL (width := 1) 8 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_1_1_install_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_1_1_code_guard
example : postAllocConventionsHOL (width := 1) 8 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_1_1_code_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_1_1_data_guard
example : postAllocConventionsHOL (width := 1) 8 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_1_1_data_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_1_1_ffi_guard
example : postAllocConventionsHOL (width := 1) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_1_1_ffi_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_1_2_skip_guard
example : postAllocConventionsHOL (width := 1) 4 (.skip) = true := by cbv
-- rbf_1_2_skip_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_1_2_move_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 []) = true := by cbv
-- rbf_1_2_move_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_2_move_cycle_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_1_2_move_cycle_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_2_move_spill_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_1_2_move_spill_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_2_move_self_guard
example : postAllocConventionsHOL (width := 1) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_1_2_move_self_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_1_2_assign_guard
example : postAllocConventionsHOL (width := 1) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_1_2_assign_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_1_2_get_guard
example : postAllocConventionsHOL (width := 1) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_1_2_get_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_1_2_set_guard
example : postAllocConventionsHOL (width := 1) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_1_2_set_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_2_set_bitmap_guard
example : postAllocConventionsHOL (width := 1) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_1_2_set_bitmap_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_2_set_invalid_guard
example : postAllocConventionsHOL (width := 1) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_1_2_set_invalid_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_1_2_store_guard
example : postAllocConventionsHOL (width := 1) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_1_2_store_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_1_2_alloc_guard
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_1_2_alloc_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_2_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_1_2_alloc_nonempty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_2_alloc_malformed_guard
example : postAllocConventionsHOL (width := 1) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_1_2_alloc_malformed_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_1_2_consts_guard
example : postAllocConventionsHOL (width := 1) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_1_2_consts_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_1_2_consts_empty_guard
example : postAllocConventionsHOL (width := 1) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_1_2_consts_empty_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_1_2_raise_guard
example : postAllocConventionsHOL (width := 1) 4 (.raise 2) = true := by cbv
-- rbf_1_2_raise_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_1_2_return_guard
example : postAllocConventionsHOL (width := 1) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_1_2_return_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_1_2_return_zero_guard
example : postAllocConventionsHOL (width := 1) 4 (.return 2 []) = true := by cbv
-- rbf_1_2_return_zero_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_1_2_break_guard
example : postAllocConventionsHOL (width := 1) 4 (.break 777) = true := by cbv
-- rbf_1_2_break_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_1_2_continue_guard
example : postAllocConventionsHOL (width := 1) 4 (.continue 777) = true := by cbv
-- rbf_1_2_continue_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_1_2_tick_guard
example : postAllocConventionsHOL (width := 1) 4 (.tick) = true := by cbv
-- rbf_1_2_tick_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_1_2_heap_guard
example : postAllocConventionsHOL (width := 1) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_1_2_heap_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_1_2_loc_guard
example : postAllocConventionsHOL (width := 1) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_1_2_loc_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_1_2_install_guard
example : postAllocConventionsHOL (width := 1) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_1_2_install_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_1_2_code_guard
example : postAllocConventionsHOL (width := 1) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_1_2_code_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_1_2_data_guard
example : postAllocConventionsHOL (width := 1) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_1_2_data_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_1_2_ffi_guard
example : postAllocConventionsHOL (width := 1) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_1_2_ffi_target
example (conf : AsmConfigExact 1) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_2_0_skip_guard
example : postAllocConventionsHOL (width := 2) 4 (.skip) = true := by cbv
-- rbf_2_0_skip_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_2_0_move_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 []) = true := by cbv
-- rbf_2_0_move_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_0_move_cycle_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_2_0_move_cycle_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_0_move_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_2_0_move_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_0_move_self_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_2_0_move_self_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_0_assign_guard
example : postAllocConventionsHOL (width := 2) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_2_0_assign_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_2_0_get_guard
example : postAllocConventionsHOL (width := 2) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_2_0_get_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_2_0_set_guard
example : postAllocConventionsHOL (width := 2) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_2_0_set_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_0_set_bitmap_guard
example : postAllocConventionsHOL (width := 2) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_2_0_set_bitmap_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_0_set_invalid_guard
example : postAllocConventionsHOL (width := 2) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_2_0_set_invalid_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_0_store_guard
example : postAllocConventionsHOL (width := 2) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_2_0_store_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_2_0_alloc_guard
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_2_0_alloc_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_0_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_2_0_alloc_nonempty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_0_alloc_malformed_guard
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_2_0_alloc_malformed_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_0_consts_guard
example : postAllocConventionsHOL (width := 2) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_2_0_consts_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_2_0_consts_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_2_0_consts_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_2_0_raise_guard
example : postAllocConventionsHOL (width := 2) 4 (.raise 2) = true := by cbv
-- rbf_2_0_raise_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_2_0_return_guard
example : postAllocConventionsHOL (width := 2) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_2_0_return_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_2_0_return_zero_guard
example : postAllocConventionsHOL (width := 2) 4 (.return 2 []) = true := by cbv
-- rbf_2_0_return_zero_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_2_0_break_guard
example : postAllocConventionsHOL (width := 2) 4 (.break 777) = true := by cbv
-- rbf_2_0_break_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_2_0_continue_guard
example : postAllocConventionsHOL (width := 2) 4 (.continue 777) = true := by cbv
-- rbf_2_0_continue_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_2_0_tick_guard
example : postAllocConventionsHOL (width := 2) 4 (.tick) = true := by cbv
-- rbf_2_0_tick_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_2_0_heap_guard
example : postAllocConventionsHOL (width := 2) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_2_0_heap_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_2_0_loc_guard
example : postAllocConventionsHOL (width := 2) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_2_0_loc_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_2_0_install_guard
example : postAllocConventionsHOL (width := 2) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_2_0_install_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_2_0_code_guard
example : postAllocConventionsHOL (width := 2) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_2_0_code_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_2_0_data_guard
example : postAllocConventionsHOL (width := 2) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_2_0_data_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_2_0_ffi_guard
example : postAllocConventionsHOL (width := 2) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_2_0_ffi_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_2_1_skip_guard
example : postAllocConventionsHOL (width := 2) 8 (.skip) = true := by cbv
-- rbf_2_1_skip_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_2_1_move_empty_guard
example : postAllocConventionsHOL (width := 2) 8 (.move 17 []) = true := by cbv
-- rbf_2_1_move_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_1_move_cycle_guard
example : postAllocConventionsHOL (width := 2) 8 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_2_1_move_cycle_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_1_move_spill_guard
example : postAllocConventionsHOL (width := 2) 8 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_2_1_move_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_1_move_self_guard
example : postAllocConventionsHOL (width := 2) 8 (.move 17 [(2,2)]) = true := by cbv
-- rbf_2_1_move_self_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_1_assign_guard
example : postAllocConventionsHOL (width := 2) 8 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_2_1_assign_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_2_1_get_guard
example : postAllocConventionsHOL (width := 2) 8 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_2_1_get_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_2_1_set_guard
example : postAllocConventionsHOL (width := 2) 8 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_2_1_set_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_1_set_bitmap_guard
example : postAllocConventionsHOL (width := 2) 8 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_2_1_set_bitmap_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_1_set_invalid_guard
example : postAllocConventionsHOL (width := 2) 8 (.set .handler (.const 7)) = true := by cbv
-- rbf_2_1_set_invalid_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_1_store_guard
example : postAllocConventionsHOL (width := 2) 8 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_2_1_store_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_2_1_alloc_guard
example : postAllocConventionsHOL (width := 2) 8 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_2_1_alloc_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_1_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 2) 8 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_2_1_alloc_nonempty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_1_alloc_malformed_guard
example : postAllocConventionsHOL (width := 2) 8 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_2_1_alloc_malformed_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_1_consts_guard
example : postAllocConventionsHOL (width := 2) 8 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_2_1_consts_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_2_1_consts_empty_guard
example : postAllocConventionsHOL (width := 2) 8 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_2_1_consts_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_2_1_raise_guard
example : postAllocConventionsHOL (width := 2) 8 (.raise 2) = true := by cbv
-- rbf_2_1_raise_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_2_1_return_guard
example : postAllocConventionsHOL (width := 2) 8 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_2_1_return_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_2_1_return_zero_guard
example : postAllocConventionsHOL (width := 2) 8 (.return 2 []) = true := by cbv
-- rbf_2_1_return_zero_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_2_1_break_guard
example : postAllocConventionsHOL (width := 2) 8 (.break 777) = true := by cbv
-- rbf_2_1_break_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_2_1_continue_guard
example : postAllocConventionsHOL (width := 2) 8 (.continue 777) = true := by cbv
-- rbf_2_1_continue_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_2_1_tick_guard
example : postAllocConventionsHOL (width := 2) 8 (.tick) = true := by cbv
-- rbf_2_1_tick_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_2_1_heap_guard
example : postAllocConventionsHOL (width := 2) 8 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_2_1_heap_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_2_1_loc_guard
example : postAllocConventionsHOL (width := 2) 8 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_2_1_loc_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_2_1_install_guard
example : postAllocConventionsHOL (width := 2) 8 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_2_1_install_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_2_1_code_guard
example : postAllocConventionsHOL (width := 2) 8 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_2_1_code_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_2_1_data_guard
example : postAllocConventionsHOL (width := 2) 8 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_2_1_data_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_2_1_ffi_guard
example : postAllocConventionsHOL (width := 2) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_2_1_ffi_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_2_2_skip_guard
example : postAllocConventionsHOL (width := 2) 4 (.skip) = true := by cbv
-- rbf_2_2_skip_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_2_2_move_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 []) = true := by cbv
-- rbf_2_2_move_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_2_move_cycle_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_2_2_move_cycle_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_2_move_spill_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_2_2_move_spill_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_2_move_self_guard
example : postAllocConventionsHOL (width := 2) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_2_2_move_self_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_2_2_assign_guard
example : postAllocConventionsHOL (width := 2) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_2_2_assign_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_2_2_get_guard
example : postAllocConventionsHOL (width := 2) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_2_2_get_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_2_2_set_guard
example : postAllocConventionsHOL (width := 2) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_2_2_set_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_2_set_bitmap_guard
example : postAllocConventionsHOL (width := 2) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_2_2_set_bitmap_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_2_set_invalid_guard
example : postAllocConventionsHOL (width := 2) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_2_2_set_invalid_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_2_2_store_guard
example : postAllocConventionsHOL (width := 2) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_2_2_store_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_2_2_alloc_guard
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_2_2_alloc_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_2_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_2_2_alloc_nonempty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_2_alloc_malformed_guard
example : postAllocConventionsHOL (width := 2) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_2_2_alloc_malformed_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_2_2_consts_guard
example : postAllocConventionsHOL (width := 2) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_2_2_consts_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_2_2_consts_empty_guard
example : postAllocConventionsHOL (width := 2) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_2_2_consts_empty_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_2_2_raise_guard
example : postAllocConventionsHOL (width := 2) 4 (.raise 2) = true := by cbv
-- rbf_2_2_raise_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_2_2_return_guard
example : postAllocConventionsHOL (width := 2) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_2_2_return_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_2_2_return_zero_guard
example : postAllocConventionsHOL (width := 2) 4 (.return 2 []) = true := by cbv
-- rbf_2_2_return_zero_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_2_2_break_guard
example : postAllocConventionsHOL (width := 2) 4 (.break 777) = true := by cbv
-- rbf_2_2_break_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_2_2_continue_guard
example : postAllocConventionsHOL (width := 2) 4 (.continue 777) = true := by cbv
-- rbf_2_2_continue_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_2_2_tick_guard
example : postAllocConventionsHOL (width := 2) 4 (.tick) = true := by cbv
-- rbf_2_2_tick_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_2_2_heap_guard
example : postAllocConventionsHOL (width := 2) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_2_2_heap_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_2_2_loc_guard
example : postAllocConventionsHOL (width := 2) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_2_2_loc_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_2_2_install_guard
example : postAllocConventionsHOL (width := 2) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_2_2_install_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_2_2_code_guard
example : postAllocConventionsHOL (width := 2) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_2_2_code_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_2_2_data_guard
example : postAllocConventionsHOL (width := 2) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_2_2_data_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_2_2_ffi_guard
example : postAllocConventionsHOL (width := 2) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_2_2_ffi_target
example (conf : AsmConfigExact 2) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_8_0_skip_guard
example : postAllocConventionsHOL (width := 8) 4 (.skip) = true := by cbv
-- rbf_8_0_skip_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_8_0_move_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 []) = true := by cbv
-- rbf_8_0_move_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_0_move_cycle_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_8_0_move_cycle_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_0_move_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_8_0_move_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_0_move_self_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_8_0_move_self_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_0_assign_guard
example : postAllocConventionsHOL (width := 8) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_8_0_assign_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_8_0_get_guard
example : postAllocConventionsHOL (width := 8) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_8_0_get_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_8_0_set_guard
example : postAllocConventionsHOL (width := 8) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_8_0_set_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_0_set_bitmap_guard
example : postAllocConventionsHOL (width := 8) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_8_0_set_bitmap_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_0_set_invalid_guard
example : postAllocConventionsHOL (width := 8) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_8_0_set_invalid_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_0_store_guard
example : postAllocConventionsHOL (width := 8) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_8_0_store_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_8_0_alloc_guard
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_8_0_alloc_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_0_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_8_0_alloc_nonempty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_0_alloc_malformed_guard
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_8_0_alloc_malformed_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_0_consts_guard
example : postAllocConventionsHOL (width := 8) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_8_0_consts_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_8_0_consts_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_8_0_consts_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_8_0_raise_guard
example : postAllocConventionsHOL (width := 8) 4 (.raise 2) = true := by cbv
-- rbf_8_0_raise_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_8_0_return_guard
example : postAllocConventionsHOL (width := 8) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_8_0_return_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_8_0_return_zero_guard
example : postAllocConventionsHOL (width := 8) 4 (.return 2 []) = true := by cbv
-- rbf_8_0_return_zero_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_8_0_break_guard
example : postAllocConventionsHOL (width := 8) 4 (.break 777) = true := by cbv
-- rbf_8_0_break_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_8_0_continue_guard
example : postAllocConventionsHOL (width := 8) 4 (.continue 777) = true := by cbv
-- rbf_8_0_continue_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_8_0_tick_guard
example : postAllocConventionsHOL (width := 8) 4 (.tick) = true := by cbv
-- rbf_8_0_tick_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_8_0_heap_guard
example : postAllocConventionsHOL (width := 8) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_8_0_heap_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_8_0_loc_guard
example : postAllocConventionsHOL (width := 8) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_8_0_loc_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_8_0_install_guard
example : postAllocConventionsHOL (width := 8) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_8_0_install_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_8_0_code_guard
example : postAllocConventionsHOL (width := 8) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_8_0_code_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_8_0_data_guard
example : postAllocConventionsHOL (width := 8) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_8_0_data_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_8_0_ffi_guard
example : postAllocConventionsHOL (width := 8) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_8_0_ffi_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_8_1_skip_guard
example : postAllocConventionsHOL (width := 8) 8 (.skip) = true := by cbv
-- rbf_8_1_skip_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_8_1_move_empty_guard
example : postAllocConventionsHOL (width := 8) 8 (.move 17 []) = true := by cbv
-- rbf_8_1_move_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_1_move_cycle_guard
example : postAllocConventionsHOL (width := 8) 8 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_8_1_move_cycle_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_1_move_spill_guard
example : postAllocConventionsHOL (width := 8) 8 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_8_1_move_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_1_move_self_guard
example : postAllocConventionsHOL (width := 8) 8 (.move 17 [(2,2)]) = true := by cbv
-- rbf_8_1_move_self_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_1_assign_guard
example : postAllocConventionsHOL (width := 8) 8 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_8_1_assign_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_8_1_get_guard
example : postAllocConventionsHOL (width := 8) 8 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_8_1_get_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_8_1_set_guard
example : postAllocConventionsHOL (width := 8) 8 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_8_1_set_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_1_set_bitmap_guard
example : postAllocConventionsHOL (width := 8) 8 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_8_1_set_bitmap_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_1_set_invalid_guard
example : postAllocConventionsHOL (width := 8) 8 (.set .handler (.const 7)) = true := by cbv
-- rbf_8_1_set_invalid_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_1_store_guard
example : postAllocConventionsHOL (width := 8) 8 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_8_1_store_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_8_1_alloc_guard
example : postAllocConventionsHOL (width := 8) 8 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_8_1_alloc_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_1_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 8) 8 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_8_1_alloc_nonempty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_1_alloc_malformed_guard
example : postAllocConventionsHOL (width := 8) 8 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_8_1_alloc_malformed_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_1_consts_guard
example : postAllocConventionsHOL (width := 8) 8 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_8_1_consts_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_8_1_consts_empty_guard
example : postAllocConventionsHOL (width := 8) 8 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_8_1_consts_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_8_1_raise_guard
example : postAllocConventionsHOL (width := 8) 8 (.raise 2) = true := by cbv
-- rbf_8_1_raise_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_8_1_return_guard
example : postAllocConventionsHOL (width := 8) 8 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_8_1_return_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_8_1_return_zero_guard
example : postAllocConventionsHOL (width := 8) 8 (.return 2 []) = true := by cbv
-- rbf_8_1_return_zero_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_8_1_break_guard
example : postAllocConventionsHOL (width := 8) 8 (.break 777) = true := by cbv
-- rbf_8_1_break_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_8_1_continue_guard
example : postAllocConventionsHOL (width := 8) 8 (.continue 777) = true := by cbv
-- rbf_8_1_continue_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_8_1_tick_guard
example : postAllocConventionsHOL (width := 8) 8 (.tick) = true := by cbv
-- rbf_8_1_tick_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_8_1_heap_guard
example : postAllocConventionsHOL (width := 8) 8 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_8_1_heap_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_8_1_loc_guard
example : postAllocConventionsHOL (width := 8) 8 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_8_1_loc_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_8_1_install_guard
example : postAllocConventionsHOL (width := 8) 8 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_8_1_install_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_8_1_code_guard
example : postAllocConventionsHOL (width := 8) 8 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_8_1_code_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_8_1_data_guard
example : postAllocConventionsHOL (width := 8) 8 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_8_1_data_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_8_1_ffi_guard
example : postAllocConventionsHOL (width := 8) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_8_1_ffi_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_8_2_skip_guard
example : postAllocConventionsHOL (width := 8) 4 (.skip) = true := by cbv
-- rbf_8_2_skip_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_8_2_move_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 []) = true := by cbv
-- rbf_8_2_move_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_2_move_cycle_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_8_2_move_cycle_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_2_move_spill_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_8_2_move_spill_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_2_move_self_guard
example : postAllocConventionsHOL (width := 8) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_8_2_move_self_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_8_2_assign_guard
example : postAllocConventionsHOL (width := 8) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_8_2_assign_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_8_2_get_guard
example : postAllocConventionsHOL (width := 8) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_8_2_get_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_8_2_set_guard
example : postAllocConventionsHOL (width := 8) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_8_2_set_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_2_set_bitmap_guard
example : postAllocConventionsHOL (width := 8) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_8_2_set_bitmap_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_2_set_invalid_guard
example : postAllocConventionsHOL (width := 8) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_8_2_set_invalid_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_8_2_store_guard
example : postAllocConventionsHOL (width := 8) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_8_2_store_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_8_2_alloc_guard
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_8_2_alloc_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_2_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_8_2_alloc_nonempty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_2_alloc_malformed_guard
example : postAllocConventionsHOL (width := 8) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_8_2_alloc_malformed_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_8_2_consts_guard
example : postAllocConventionsHOL (width := 8) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_8_2_consts_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_8_2_consts_empty_guard
example : postAllocConventionsHOL (width := 8) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_8_2_consts_empty_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_8_2_raise_guard
example : postAllocConventionsHOL (width := 8) 4 (.raise 2) = true := by cbv
-- rbf_8_2_raise_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_8_2_return_guard
example : postAllocConventionsHOL (width := 8) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_8_2_return_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_8_2_return_zero_guard
example : postAllocConventionsHOL (width := 8) 4 (.return 2 []) = true := by cbv
-- rbf_8_2_return_zero_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_8_2_break_guard
example : postAllocConventionsHOL (width := 8) 4 (.break 777) = true := by cbv
-- rbf_8_2_break_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_8_2_continue_guard
example : postAllocConventionsHOL (width := 8) 4 (.continue 777) = true := by cbv
-- rbf_8_2_continue_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_8_2_tick_guard
example : postAllocConventionsHOL (width := 8) 4 (.tick) = true := by cbv
-- rbf_8_2_tick_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_8_2_heap_guard
example : postAllocConventionsHOL (width := 8) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_8_2_heap_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_8_2_loc_guard
example : postAllocConventionsHOL (width := 8) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_8_2_loc_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_8_2_install_guard
example : postAllocConventionsHOL (width := 8) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_8_2_install_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_8_2_code_guard
example : postAllocConventionsHOL (width := 8) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_8_2_code_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_8_2_data_guard
example : postAllocConventionsHOL (width := 8) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_8_2_data_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_8_2_ffi_guard
example : postAllocConventionsHOL (width := 8) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_8_2_ffi_target
example (conf : AsmConfigExact 8) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_64_0_skip_guard
example : postAllocConventionsHOL (width := 64) 4 (.skip) = true := by cbv
-- rbf_64_0_skip_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_64_0_move_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 []) = true := by cbv
-- rbf_64_0_move_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_0_move_cycle_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_64_0_move_cycle_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_0_move_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_64_0_move_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_0_move_self_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_64_0_move_self_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_0_assign_guard
example : postAllocConventionsHOL (width := 64) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_64_0_assign_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_64_0_get_guard
example : postAllocConventionsHOL (width := 64) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_64_0_get_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_64_0_set_guard
example : postAllocConventionsHOL (width := 64) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_64_0_set_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_0_set_bitmap_guard
example : postAllocConventionsHOL (width := 64) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_64_0_set_bitmap_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_0_set_invalid_guard
example : postAllocConventionsHOL (width := 64) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_64_0_set_invalid_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_0_store_guard
example : postAllocConventionsHOL (width := 64) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_64_0_store_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_64_0_alloc_guard
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_64_0_alloc_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_0_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_64_0_alloc_nonempty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_0_alloc_malformed_guard
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_64_0_alloc_malformed_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_0_consts_guard
example : postAllocConventionsHOL (width := 64) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_64_0_consts_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_64_0_consts_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_64_0_consts_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_64_0_raise_guard
example : postAllocConventionsHOL (width := 64) 4 (.raise 2) = true := by cbv
-- rbf_64_0_raise_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_64_0_return_guard
example : postAllocConventionsHOL (width := 64) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_64_0_return_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_64_0_return_zero_guard
example : postAllocConventionsHOL (width := 64) 4 (.return 2 []) = true := by cbv
-- rbf_64_0_return_zero_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_64_0_break_guard
example : postAllocConventionsHOL (width := 64) 4 (.break 777) = true := by cbv
-- rbf_64_0_break_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_64_0_continue_guard
example : postAllocConventionsHOL (width := 64) 4 (.continue 777) = true := by cbv
-- rbf_64_0_continue_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_64_0_tick_guard
example : postAllocConventionsHOL (width := 64) 4 (.tick) = true := by cbv
-- rbf_64_0_tick_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_64_0_heap_guard
example : postAllocConventionsHOL (width := 64) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_64_0_heap_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_64_0_loc_guard
example : postAllocConventionsHOL (width := 64) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_64_0_loc_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_64_0_install_guard
example : postAllocConventionsHOL (width := 64) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_64_0_install_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_64_0_code_guard
example : postAllocConventionsHOL (width := 64) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_64_0_code_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_64_0_data_guard
example : postAllocConventionsHOL (width := 64) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_64_0_data_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_64_0_ffi_guard
example : postAllocConventionsHOL (width := 64) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_64_0_ffi_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_64_1_skip_guard
example : postAllocConventionsHOL (width := 64) 8 (.skip) = true := by cbv
-- rbf_64_1_skip_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_64_1_move_empty_guard
example : postAllocConventionsHOL (width := 64) 8 (.move 17 []) = true := by cbv
-- rbf_64_1_move_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_1_move_cycle_guard
example : postAllocConventionsHOL (width := 64) 8 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_64_1_move_cycle_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_1_move_spill_guard
example : postAllocConventionsHOL (width := 64) 8 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_64_1_move_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_1_move_self_guard
example : postAllocConventionsHOL (width := 64) 8 (.move 17 [(2,2)]) = true := by cbv
-- rbf_64_1_move_self_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_1_assign_guard
example : postAllocConventionsHOL (width := 64) 8 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_64_1_assign_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_64_1_get_guard
example : postAllocConventionsHOL (width := 64) 8 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_64_1_get_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_64_1_set_guard
example : postAllocConventionsHOL (width := 64) 8 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_64_1_set_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_1_set_bitmap_guard
example : postAllocConventionsHOL (width := 64) 8 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_64_1_set_bitmap_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_1_set_invalid_guard
example : postAllocConventionsHOL (width := 64) 8 (.set .handler (.const 7)) = true := by cbv
-- rbf_64_1_set_invalid_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_1_store_guard
example : postAllocConventionsHOL (width := 64) 8 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_64_1_store_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_64_1_alloc_guard
example : postAllocConventionsHOL (width := 64) 8 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_64_1_alloc_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_1_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 64) 8 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_64_1_alloc_nonempty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_1_alloc_malformed_guard
example : postAllocConventionsHOL (width := 64) 8 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_64_1_alloc_malformed_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_1_consts_guard
example : postAllocConventionsHOL (width := 64) 8 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_64_1_consts_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_64_1_consts_empty_guard
example : postAllocConventionsHOL (width := 64) 8 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_64_1_consts_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_64_1_raise_guard
example : postAllocConventionsHOL (width := 64) 8 (.raise 2) = true := by cbv
-- rbf_64_1_raise_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_64_1_return_guard
example : postAllocConventionsHOL (width := 64) 8 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_64_1_return_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_64_1_return_zero_guard
example : postAllocConventionsHOL (width := 64) 8 (.return 2 []) = true := by cbv
-- rbf_64_1_return_zero_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_64_1_break_guard
example : postAllocConventionsHOL (width := 64) 8 (.break 777) = true := by cbv
-- rbf_64_1_break_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_64_1_continue_guard
example : postAllocConventionsHOL (width := 64) 8 (.continue 777) = true := by cbv
-- rbf_64_1_continue_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_64_1_tick_guard
example : postAllocConventionsHOL (width := 64) 8 (.tick) = true := by cbv
-- rbf_64_1_tick_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_64_1_heap_guard
example : postAllocConventionsHOL (width := 64) 8 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_64_1_heap_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_64_1_loc_guard
example : postAllocConventionsHOL (width := 64) 8 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_64_1_loc_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_64_1_install_guard
example : postAllocConventionsHOL (width := 64) 8 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_64_1_install_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_64_1_code_guard
example : postAllocConventionsHOL (width := 64) 8 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_64_1_code_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_64_1_data_guard
example : postAllocConventionsHOL (width := 64) 8 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_64_1_data_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_64_1_ffi_guard
example : postAllocConventionsHOL (width := 64) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_64_1_ffi_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_64_2_skip_guard
example : postAllocConventionsHOL (width := 64) 4 (.skip) = true := by cbv
-- rbf_64_2_skip_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_64_2_move_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 []) = true := by cbv
-- rbf_64_2_move_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_2_move_cycle_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_64_2_move_cycle_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_2_move_spill_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_64_2_move_spill_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_2_move_self_guard
example : postAllocConventionsHOL (width := 64) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_64_2_move_self_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_64_2_assign_guard
example : postAllocConventionsHOL (width := 64) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_64_2_assign_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_64_2_get_guard
example : postAllocConventionsHOL (width := 64) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_64_2_get_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_64_2_set_guard
example : postAllocConventionsHOL (width := 64) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_64_2_set_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_2_set_bitmap_guard
example : postAllocConventionsHOL (width := 64) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_64_2_set_bitmap_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_2_set_invalid_guard
example : postAllocConventionsHOL (width := 64) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_64_2_set_invalid_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_64_2_store_guard
example : postAllocConventionsHOL (width := 64) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_64_2_store_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_64_2_alloc_guard
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_64_2_alloc_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_2_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_64_2_alloc_nonempty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_2_alloc_malformed_guard
example : postAllocConventionsHOL (width := 64) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_64_2_alloc_malformed_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_64_2_consts_guard
example : postAllocConventionsHOL (width := 64) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_64_2_consts_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_64_2_consts_empty_guard
example : postAllocConventionsHOL (width := 64) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_64_2_consts_empty_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_64_2_raise_guard
example : postAllocConventionsHOL (width := 64) 4 (.raise 2) = true := by cbv
-- rbf_64_2_raise_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_64_2_return_guard
example : postAllocConventionsHOL (width := 64) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_64_2_return_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_64_2_return_zero_guard
example : postAllocConventionsHOL (width := 64) 4 (.return 2 []) = true := by cbv
-- rbf_64_2_return_zero_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_64_2_break_guard
example : postAllocConventionsHOL (width := 64) 4 (.break 777) = true := by cbv
-- rbf_64_2_break_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_64_2_continue_guard
example : postAllocConventionsHOL (width := 64) 4 (.continue 777) = true := by cbv
-- rbf_64_2_continue_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_64_2_tick_guard
example : postAllocConventionsHOL (width := 64) 4 (.tick) = true := by cbv
-- rbf_64_2_tick_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_64_2_heap_guard
example : postAllocConventionsHOL (width := 64) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_64_2_heap_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_64_2_loc_guard
example : postAllocConventionsHOL (width := 64) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_64_2_loc_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_64_2_install_guard
example : postAllocConventionsHOL (width := 64) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_64_2_install_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_64_2_code_guard
example : postAllocConventionsHOL (width := 64) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_64_2_code_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_64_2_data_guard
example : postAllocConventionsHOL (width := 64) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_64_2_data_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_64_2_ffi_guard
example : postAllocConventionsHOL (width := 64) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_64_2_ffi_target
example (conf : AsmConfigExact 64) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_80_0_skip_guard
example : postAllocConventionsHOL (width := 80) 4 (.skip) = true := by cbv
-- rbf_80_0_skip_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_80_0_move_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 []) = true := by cbv
-- rbf_80_0_move_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_0_move_cycle_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_80_0_move_cycle_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_0_move_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_80_0_move_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_0_move_self_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_80_0_move_self_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_0_assign_guard
example : postAllocConventionsHOL (width := 80) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_80_0_assign_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_80_0_get_guard
example : postAllocConventionsHOL (width := 80) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_80_0_get_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_80_0_set_guard
example : postAllocConventionsHOL (width := 80) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_80_0_set_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_0_set_bitmap_guard
example : postAllocConventionsHOL (width := 80) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_80_0_set_bitmap_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_0_set_invalid_guard
example : postAllocConventionsHOL (width := 80) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_80_0_set_invalid_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_0_store_guard
example : postAllocConventionsHOL (width := 80) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_80_0_store_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_80_0_alloc_guard
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_80_0_alloc_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_0_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_80_0_alloc_nonempty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_0_alloc_malformed_guard
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_80_0_alloc_malformed_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_0_consts_guard
example : postAllocConventionsHOL (width := 80) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_80_0_consts_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_80_0_consts_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_80_0_consts_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_80_0_raise_guard
example : postAllocConventionsHOL (width := 80) 4 (.raise 2) = true := by cbv
-- rbf_80_0_raise_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_80_0_return_guard
example : postAllocConventionsHOL (width := 80) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_80_0_return_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_80_0_return_zero_guard
example : postAllocConventionsHOL (width := 80) 4 (.return 2 []) = true := by cbv
-- rbf_80_0_return_zero_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_80_0_break_guard
example : postAllocConventionsHOL (width := 80) 4 (.break 777) = true := by cbv
-- rbf_80_0_break_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_80_0_continue_guard
example : postAllocConventionsHOL (width := 80) 4 (.continue 777) = true := by cbv
-- rbf_80_0_continue_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_80_0_tick_guard
example : postAllocConventionsHOL (width := 80) 4 (.tick) = true := by cbv
-- rbf_80_0_tick_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_80_0_heap_guard
example : postAllocConventionsHOL (width := 80) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_80_0_heap_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_80_0_loc_guard
example : postAllocConventionsHOL (width := 80) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_80_0_loc_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_80_0_install_guard
example : postAllocConventionsHOL (width := 80) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_80_0_install_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_80_0_code_guard
example : postAllocConventionsHOL (width := 80) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_80_0_code_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_80_0_data_guard
example : postAllocConventionsHOL (width := 80) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_80_0_data_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_80_0_ffi_guard
example : postAllocConventionsHOL (width := 80) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_80_0_ffi_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,7,9)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_80_1_skip_guard
example : postAllocConventionsHOL (width := 80) 8 (.skip) = true := by cbv
-- rbf_80_1_skip_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_80_1_move_empty_guard
example : postAllocConventionsHOL (width := 80) 8 (.move 17 []) = true := by cbv
-- rbf_80_1_move_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_1_move_cycle_guard
example : postAllocConventionsHOL (width := 80) 8 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_80_1_move_cycle_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_1_move_spill_guard
example : postAllocConventionsHOL (width := 80) 8 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_80_1_move_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_1_move_self_guard
example : postAllocConventionsHOL (width := 80) 8 (.move 17 [(2,2)]) = true := by cbv
-- rbf_80_1_move_self_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_1_assign_guard
example : postAllocConventionsHOL (width := 80) 8 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_80_1_assign_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_80_1_get_guard
example : postAllocConventionsHOL (width := 80) 8 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_80_1_get_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_80_1_set_guard
example : postAllocConventionsHOL (width := 80) 8 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_80_1_set_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_1_set_bitmap_guard
example : postAllocConventionsHOL (width := 80) 8 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_80_1_set_bitmap_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_1_set_invalid_guard
example : postAllocConventionsHOL (width := 80) 8 (.set .handler (.const 7)) = true := by cbv
-- rbf_80_1_set_invalid_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_1_store_guard
example : postAllocConventionsHOL (width := 80) 8 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_80_1_store_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_80_1_alloc_guard
example : postAllocConventionsHOL (width := 80) 8 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_80_1_alloc_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_1_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 80) 8 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_80_1_alloc_nonempty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_1_alloc_malformed_guard
example : postAllocConventionsHOL (width := 80) 8 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_80_1_alloc_malformed_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_1_consts_guard
example : postAllocConventionsHOL (width := 80) 8 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_80_1_consts_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_80_1_consts_empty_guard
example : postAllocConventionsHOL (width := 80) 8 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_80_1_consts_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_80_1_raise_guard
example : postAllocConventionsHOL (width := 80) 8 (.raise 2) = true := by cbv
-- rbf_80_1_raise_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_80_1_return_guard
example : postAllocConventionsHOL (width := 80) 8 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_80_1_return_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_80_1_return_zero_guard
example : postAllocConventionsHOL (width := 80) 8 (.return 2 []) = true := by cbv
-- rbf_80_1_return_zero_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_80_1_break_guard
example : postAllocConventionsHOL (width := 80) 8 (.break 777) = true := by cbv
-- rbf_80_1_break_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_80_1_continue_guard
example : postAllocConventionsHOL (width := 80) 8 (.continue 777) = true := by cbv
-- rbf_80_1_continue_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_80_1_tick_guard
example : postAllocConventionsHOL (width := 80) 8 (.tick) = true := by cbv
-- rbf_80_1_tick_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_80_1_heap_guard
example : postAllocConventionsHOL (width := 80) 8 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_80_1_heap_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_80_1_loc_guard
example : postAllocConventionsHOL (width := 80) 8 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_80_1_loc_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_80_1_install_guard
example : postAllocConventionsHOL (width := 80) 8 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_80_1_install_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_80_1_code_guard
example : postAllocConventionsHOL (width := 80) 8 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_80_1_code_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_80_1_data_guard
example : postAllocConventionsHOL (width := 80) 8 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_80_1_data_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_80_1_ffi_guard
example : postAllocConventionsHOL (width := 80) 8 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_80_1_ffi_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (8,7,9)).1 10 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

-- rbf_80_2_skip_guard
example : postAllocConventionsHOL (width := 80) 4 (.skip) = true := by cbv
-- rbf_80_2_skip_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSkip <;> first | rfl | cbv

-- rbf_80_2_move_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 []) = true := by cbv
-- rbf_80_2_move_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_2_move_cycle_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 [(2,4),(4,2)]) = true := by cbv
-- rbf_80_2_move_cycle_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_2_move_spill_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) = true := by cbv
-- rbf_80_2_move_spill_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_2_move_self_guard
example : postAllocConventionsHOL (width := 80) 4 (.move 17 [(2,2)]) = true := by cbv
-- rbf_80_2_move_self_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.move 17 [(2,2)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundMove <;> first | rfl | cbv

-- rbf_80_2_assign_guard
example : postAllocConventionsHOL (width := 80) 4 (.assign 1180591620717411303424 (.const 7)) = true := by cbv
-- rbf_80_2_assign_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.assign 1180591620717411303424 (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAssign <;> first | rfl | cbv

-- rbf_80_2_get_guard
example : postAllocConventionsHOL (width := 80) 4 (.get 1180591620717411303424 .currHeap) = true := by cbv
-- rbf_80_2_get_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.get 1180591620717411303424 .currHeap) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundGet <;> first | rfl | cbv

-- rbf_80_2_set_guard
example : postAllocConventionsHOL (width := 80) 4 (.set .handler (.var 1180591620717411303424)) = true := by cbv
-- rbf_80_2_set_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .handler (.var 1180591620717411303424)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_2_set_bitmap_guard
example : postAllocConventionsHOL (width := 80) 4 (.set .bitmapBase (.var 2)) = true := by cbv
-- rbf_80_2_set_bitmap_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .bitmapBase (.var 2)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_2_set_invalid_guard
example : postAllocConventionsHOL (width := 80) 4 (.set .handler (.const 7)) = true := by cbv
-- rbf_80_2_set_invalid_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.set .handler (.const 7)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundSet <;> first | rfl | cbv

-- rbf_80_2_store_guard
example : postAllocConventionsHOL (width := 80) 4 (.store (.var 2) 1180591620717411303424) = true := by cbv
-- rbf_80_2_store_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.store (.var 2) 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStore <;> first | rfl | cbv

-- rbf_80_2_alloc_guard
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.ln,.ln)) = true := by cbv
-- rbf_80_2_alloc_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_2_alloc_nonempty_guard
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.ln,sptInsert 32 () .ln)) = true := by cbv
-- rbf_80_2_alloc_nonempty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.ln,sptInsert 32 () .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_2_alloc_malformed_guard
example : postAllocConventionsHOL (width := 80) 4 (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) = true := by cbv
-- rbf_80_2_alloc_malformed_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.alloc 2 (.bn .ln .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundAlloc <;> first | rfl | cbv

-- rbf_80_2_consts_guard
example : postAllocConventionsHOL (width := 80) 4 (.storeConsts 0 2 4 6 [(true,7),(false,8)]) = true := by cbv
-- rbf_80_2_consts_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.storeConsts 0 2 4 6 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_80_2_consts_empty_guard
example : postAllocConventionsHOL (width := 80) 4 (.storeConsts 0 2 4 6 []) = true := by cbv
-- rbf_80_2_consts_empty_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.storeConsts 0 2 4 6 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundStoreConsts <;> first | rfl | cbv

-- rbf_80_2_raise_guard
example : postAllocConventionsHOL (width := 80) 4 (.raise 2) = true := by cbv
-- rbf_80_2_raise_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.raise 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundRaise <;> first | rfl | cbv

-- rbf_80_2_return_guard
example : postAllocConventionsHOL (width := 80) 4 (.return 1180591620717411303424 [2,4,6]) = true := by cbv
-- rbf_80_2_return_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.return 1180591620717411303424 [2,4,6]) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_80_2_return_zero_guard
example : postAllocConventionsHOL (width := 80) 4 (.return 2 []) = true := by cbv
-- rbf_80_2_return_zero_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.return 2 []) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundReturn <;> first | rfl | cbv

-- rbf_80_2_break_guard
example : postAllocConventionsHOL (width := 80) 4 (.break 777) = true := by cbv
-- rbf_80_2_break_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundBreak <;> first | rfl | cbv

-- rbf_80_2_continue_guard
example : postAllocConventionsHOL (width := 80) 4 (.continue 777) = true := by cbv
-- rbf_80_2_continue_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundContinue <;> first | rfl | cbv

-- rbf_80_2_tick_guard
example : postAllocConventionsHOL (width := 80) 4 (.tick) = true := by cbv
-- rbf_80_2_tick_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundTick <;> first | rfl | cbv

-- rbf_80_2_heap_guard
example : postAllocConventionsHOL (width := 80) 4 (.opCurrHeap .add 1180591620717411303424 2) = true := by cbv
-- rbf_80_2_heap_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.opCurrHeap .add 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundOpCurrHeap <;> first | rfl | cbv

-- rbf_80_2_loc_guard
example : postAllocConventionsHOL (width := 80) 4 (.locValue 1180591620717411303424 17) = true := by cbv
-- rbf_80_2_loc_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.locValue 1180591620717411303424 17) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundLocValue <;> first | rfl | cbv

-- rbf_80_2_install_guard
example : postAllocConventionsHOL (width := 80) 4 (.install 2 4 1180591620717411303424 2 (.ln,.ln)) = true := by cbv
-- rbf_80_2_install_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.install 2 4 1180591620717411303424 2 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundInstall <;> first | rfl | cbv

-- rbf_80_2_code_guard
example : postAllocConventionsHOL (width := 80) 4 (.codeBufferWrite 1180591620717411303424 2) = true := by cbv
-- rbf_80_2_code_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.codeBufferWrite 1180591620717411303424 2) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundCodeBufferWrite <;> first | rfl | cbv

-- rbf_80_2_data_guard
example : postAllocConventionsHOL (width := 80) 4 (.dataBufferWrite 2 1180591620717411303424) = true := by cbv
-- rbf_80_2_data_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.dataBufferWrite 2 1180591620717411303424) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundDataBufferWrite <;> first | rfl | cbv

-- rbf_80_2_ffi_guard
example : postAllocConventionsHOL (width := 80) 4 (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) = true := by cbv
-- rbf_80_2_ffi_target
example (conf : AsmConfigExact 80) : regBound (compNative conf false (.ffi (Basis.Pure.MlString.ofString "abc") 2 4 6 8 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (4,0,1180591620717411303424)).1 6 := by
  apply wordToStackRegBoundFfi <;> first | rfl | cbv

end Flapjack.Test.WordToStackRegFlatParity
