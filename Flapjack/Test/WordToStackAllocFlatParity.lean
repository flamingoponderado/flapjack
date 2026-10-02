import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Flat

namespace Flapjack.Test.WordToStackAllocFlatParity

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm

open Flapjack.WordToStackProofs.AllocArgs

/- Original regression boundary: word_to_stack_alloc_flat_probe.out. Full generic source case applications and same-input actual compiler predicates; no full assembly or cross-language equivalence claim. -/

-- aaf_1_0_skip
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_move
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_0_assign
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_get
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_set
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_store
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_alloc
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_store_consts
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_raise
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_return
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_break
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_continue
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_tick
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_heap
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_loc
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_install
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_code_write
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_data_write
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_ffi
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_move_cycle
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_0_move_self
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_0_set_bitmap
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_set_rejected
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_return_zero
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_alloc_malformed
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_0_const_empty
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_skip
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_move
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_1_assign
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_get
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_set
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_store
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_alloc
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_store_consts
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_raise
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_return
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_break
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_continue
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_tick
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_heap
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_loc
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_install
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_code_write
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_data_write
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_ffi
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_move_cycle
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_1_move_self
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_1_set_bitmap
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_set_rejected
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_return_zero
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_alloc_malformed
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_1_const_empty
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_skip
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_move
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_2_assign
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_get
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_set
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_store
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_alloc
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_store_consts
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_raise
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_return
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_break
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_continue
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_tick
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_heap
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_loc
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_install
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_code_write
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_data_write
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_ffi
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_move_cycle
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_2_move_self
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_1_2_set_bitmap
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_set_rejected
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_return_zero
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_alloc_malformed
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_1_2_const_empty
example (conf : AsmConfigExact 1) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_skip
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_move
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_0_assign
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_get
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_set
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_store
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_alloc
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_store_consts
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_raise
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_return
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_break
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_continue
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_tick
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_heap
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_loc
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_install
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_code_write
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_data_write
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_ffi
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_move_cycle
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_0_move_self
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_0_set_bitmap
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_set_rejected
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_return_zero
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_alloc_malformed
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_0_const_empty
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_skip
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_move
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_1_assign
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_get
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_set
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_store
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_alloc
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_store_consts
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_raise
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_return
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_break
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_continue
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_tick
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_heap
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_loc
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_install
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_code_write
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_data_write
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_ffi
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_move_cycle
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_1_move_self
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_1_set_bitmap
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_set_rejected
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_return_zero
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_alloc_malformed
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_1_const_empty
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_skip
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_move
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_2_assign
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_get
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_set
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_store
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_alloc
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_store_consts
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_raise
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_return
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_break
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_continue
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_tick
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_heap
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_loc
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_install
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_code_write
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_data_write
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_ffi
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_move_cycle
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_2_move_self
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_2_2_set_bitmap
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_set_rejected
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_return_zero
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_alloc_malformed
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_2_2_const_empty
example (conf : AsmConfigExact 2) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_skip
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_move
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_0_assign
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_get
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_set
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_store
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_alloc
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_store_consts
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_raise
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_return
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_break
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_continue
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_tick
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_heap
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_loc
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_install
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_code_write
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_data_write
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_ffi
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_move_cycle
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_0_move_self
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_0_set_bitmap
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_set_rejected
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_return_zero
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_alloc_malformed
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_0_const_empty
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_skip
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_move
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_1_assign
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_get
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_set
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_store
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_alloc
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_store_consts
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_raise
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_return
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_break
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_continue
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_tick
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_heap
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_loc
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_install
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_code_write
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_data_write
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_ffi
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_move_cycle
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_1_move_self
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_1_set_bitmap
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_set_rejected
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_return_zero
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_alloc_malformed
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_1_const_empty
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_skip
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_move
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_2_assign
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_get
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_set
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_store
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_alloc
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_store_consts
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_raise
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_return
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_break
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_continue
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_tick
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_heap
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_loc
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_install
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_code_write
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_data_write
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_ffi
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_move_cycle
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_2_move_self
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_8_2_set_bitmap
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_set_rejected
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_return_zero
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_alloc_malformed
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_8_2_const_empty
example (conf : AsmConfigExact 8) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_skip
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_move
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_0_assign
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_get
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_set
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_store
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_alloc
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_store_consts
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_raise
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_return
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_break
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_continue
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_tick
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_heap
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_loc
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_install
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_code_write
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_data_write
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_ffi
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_move_cycle
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_0_move_self
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_0_set_bitmap
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_set_rejected
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_return_zero
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_alloc_malformed
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_0_const_empty
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_skip
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_move
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_1_assign
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_get
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_set
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_store
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_alloc
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_store_consts
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_raise
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_return
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_break
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_continue
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_tick
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_heap
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_loc
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_install
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_code_write
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_data_write
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_ffi
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_move_cycle
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_1_move_self
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_1_set_bitmap
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_set_rejected
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_return_zero
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_alloc_malformed
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_1_const_empty
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_skip
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_move
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_2_assign
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_get
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_set
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_store
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_alloc
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_store_consts
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_raise
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_return
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_break
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_continue
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_tick
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_heap
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_loc
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_install
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_code_write
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_data_write
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_ffi
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_move_cycle
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_2_move_self
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_64_2_set_bitmap
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_set_rejected
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_return_zero
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_alloc_malformed
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_64_2_const_empty
example (conf : AsmConfigExact 64) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_skip
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_move
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_0_assign
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_get
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_set
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_store
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_alloc
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_store_consts
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_raise
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_return
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_break
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_continue
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_tick
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_heap
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_loc
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_install
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_code_write
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_data_write
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_ffi
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_move_cycle
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_0_move_self
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_0_set_bitmap
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_set_rejected
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_return_zero
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_alloc_malformed
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_0_const_empty
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (0,0,0)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_skip
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_move
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_1_assign
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_get
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_set
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_store
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_alloc
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_store_consts
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_raise
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_return
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_break
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_continue
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_tick
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_heap
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_loc
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_install
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_code_write
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_data_write
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_ffi
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_move_cycle
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_1_move_self
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_1_set_bitmap
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_set_rejected
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_return_zero
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_alloc_malformed
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_1_const_empty
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (2,7,9)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_skip
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.skip) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_move
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 17 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_2_assign
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.assign 999 (.const 7)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_get
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.get 999 .currHeap) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_set
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .handler (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_store
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.store (.var 3) 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_alloc
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_store_consts
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_raise
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.raise 999) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_return
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.return 999 [2,4,6]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_break
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.break 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_continue
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.continue 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_tick
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.tick) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_heap
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.opCurrHeap .add 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_loc
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.locValue 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_install
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.install 0 1 2 3 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_code_write
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.codeBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_data_write
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.dataBufferWrite 999 777) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_ffi
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.ffi (Flapjack.Basis.Pure.MlString.ofString "abc") 999 777 555 333 (.ln,.ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_move_cycle
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 0 [(2,4),(4,2)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_2_move_self
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.move 0 [(2,2),(2,4),(2,6)]) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative, wMoveNative]
  exact moveAuxAllocArg _ _

-- aaf_80_2_set_bitmap
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .bitmapBase (.var 999)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_set_rejected
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.set .handler (.load (.var 999))) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_return_zero
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.return 999 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_alloc_malformed
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.alloc 999 (.bn .ln .ln,.bs .ln () .ln)) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

-- aaf_80_2_const_empty
example (conf : AsmConfigExact 80) : allocArg (compNative conf false (.storeConsts 0 1 2 3 []) (.append (.list [4]) (.list [7]),17) (1180591620717411303424,3,1180591620717411303425)).1 := by
  simp only [compNative]
  trivial

end Flapjack.Test.WordToStackAllocFlatParity
