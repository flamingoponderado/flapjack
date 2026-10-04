import Flapjack.Pancake.WordConvs.FullInstOkLess

namespace Flapjack.Test.WordConvsFullInstNativeParity
open Flapjack Flapjack.Compiler.Encoders.Asm
/- Expectations captured freshly from original full_inst_ok_less at exact
config/program carriers, six positive widths and both two-reg policy flags.
Other config fields remain arbitrary. The original broad oracle is unchanged. -/
private def config {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (two : Bool) : AsmConfigExact width :=
  { c with
    isa := .riscv
    regCount := 8
    avoidRegs := [3]
    fpRegCount := 4
    twoRegArith := two
    validImm := fun _ v => v == BitVec.ofNat width 1
    addrOffset := (0,100)
    hwOffset := (0,2)
    byteOffset := (0,3) }

-- fin_1_0_skip=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.skip : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_move=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_inst=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_assign=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_get=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_set=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_store=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_alloc=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_consts=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_raise=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.raise 99 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_return=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_break=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.break 777 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_continue=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.continue 777 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_tick=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.tick : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_heap=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_loc=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_install=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_code=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_data=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_ffi=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_share=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_must=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_loop=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_seq=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_if=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_tail=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_callreturn=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_callhandler=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_imm_good=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_imm_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_fpLess=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_load_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_store_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_store_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_load32_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_load32_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_store32_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_store32_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_load16_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_load16_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_store16_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_store16_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_0_load8_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_load8_4=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_store8_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_store8_4=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_skip=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.skip : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_move=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_inst=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_assign=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_get=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_set=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_store=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_alloc=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_consts=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_raise=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.raise 99 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_return=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_break=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.break 777 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_continue=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.continue 777 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_tick=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.tick : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_heap=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_loc=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_install=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_code=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_data=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_ffi=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_share=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_must=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_loop=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_seq=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_if=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_tail=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_callreturn=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_callhandler=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_imm_good=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_imm_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_fpLess=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_load_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_store_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_store_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_load32_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_load32_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_store32_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_store32_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_load16_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_load16_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_store16_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_store16_4=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_load8_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_load8_4=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_store8_1=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_store8_4=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_2_0_skip=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.skip : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_move=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_inst=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_assign=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_get=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_set=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_store=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_alloc=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_consts=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_raise=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.raise 99 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_return=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_break=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.break 777 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_continue=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.continue 777 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_tick=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.tick : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_heap=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_loc=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_install=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_code=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_data=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_ffi=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_share=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_must=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_loop=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_seq=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_if=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_tail=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_callreturn=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_callhandler=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_imm_good=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_imm_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_fpLess=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_load_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_store_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_store_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_load32_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_load32_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_store32_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_store32_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_0_load16_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_load16_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_store16_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_store16_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_load8_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_load8_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_store8_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_store8_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_skip=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.skip : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_move=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_inst=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_assign=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_get=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_set=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_store=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_alloc=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_consts=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_raise=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.raise 99 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_return=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_break=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.break 777 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_continue=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.continue 777 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_tick=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.tick : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_heap=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_loc=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_install=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_code=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_data=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_ffi=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_share=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_must=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_loop=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_seq=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_if=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_tail=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_callreturn=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_callhandler=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_imm_good=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_imm_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_fpLess=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_load_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_store_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_store_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_load32_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_load32_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_store32_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_store32_4=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_load16_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_load16_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_store16_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_store16_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_load8_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_load8_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_store8_1=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_store8_4=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_8_0_skip=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.skip : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_move=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_inst=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_assign=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_get=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_set=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_alloc=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_consts=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_raise=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.raise 99 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_return=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_break=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.break 777 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_continue=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.continue 777 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_tick=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.tick : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_heap=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_loc=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_install=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_code=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_data=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_ffi=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_share=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_must=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_loop=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_seq=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_if=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_tail=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_callreturn=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_callhandler=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_imm_good=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_imm_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_fpLess=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_load_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_load32_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_load32_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store32_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store32_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_load16_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_load16_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_store16_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store16_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_load8_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_load8_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_store8_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_0_store8_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_skip=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.skip : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_move=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_inst=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_assign=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_get=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_set=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_alloc=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_consts=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_raise=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.raise 99 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_return=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_break=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.break 777 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_continue=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.continue 777 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_tick=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.tick : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_heap=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_loc=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_install=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_code=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_data=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_ffi=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_share=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_must=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_loop=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_seq=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_if=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_tail=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_callreturn=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_callhandler=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_imm_good=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_imm_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_fpLess=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_load_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_load32_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_load32_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store32_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store32_4=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_load16_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_load16_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_store16_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store16_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_load8_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_load8_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_store8_1=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_store8_4=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_32_0_skip=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.skip : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_move=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_inst=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_assign=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_get=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_set=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_alloc=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_consts=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_raise=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.raise 99 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_return=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_break=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.break 777 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_continue=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.continue 777 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_tick=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.tick : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_heap=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_loc=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_install=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_code=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_data=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_ffi=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_share=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_must=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_loop=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_seq=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_if=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_tail=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_callreturn=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_callhandler=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_imm_good=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_imm_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_fpLess=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_load_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_load32_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_load32_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store32_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store32_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_load16_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_load16_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_store16_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store16_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_load8_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_load8_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_store8_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_0_store8_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_skip=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.skip : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_move=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_inst=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_assign=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_get=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_set=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_alloc=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_consts=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_raise=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.raise 99 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_return=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_break=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.break 777 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_continue=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.continue 777 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_tick=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.tick : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_heap=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_loc=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_install=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_code=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_data=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_ffi=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_share=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_must=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_loop=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_seq=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_if=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_tail=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_callreturn=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_callhandler=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_imm_good=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_imm_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_fpLess=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_load_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_load32_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_load32_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store32_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store32_4=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_load16_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_load16_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_store16_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store16_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_load8_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_load8_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_store8_1=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_store8_4=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_64_0_skip=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.skip : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_move=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_inst=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_assign=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_get=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_set=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_alloc=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_consts=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_raise=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.raise 99 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_return=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_break=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.break 777 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_continue=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.continue 777 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_tick=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.tick : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_heap=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_loc=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_install=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_code=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_data=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_ffi=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_share=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_must=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_loop=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_seq=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_if=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_tail=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_callreturn=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_callhandler=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_imm_good=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_imm_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_fpLess=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_load_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_load32_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_load32_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store32_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store32_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_load16_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_load16_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_store16_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store16_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_load8_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_load8_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_store8_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_0_store8_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_skip=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.skip : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_move=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_inst=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_assign=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_get=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_set=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_alloc=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_consts=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_raise=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.raise 99 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_return=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_break=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.break 777 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_continue=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.continue 777 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_tick=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.tick : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_heap=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_loc=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_install=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_code=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_data=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_ffi=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_share=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_must=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_loop=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_seq=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_if=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_tail=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_callreturn=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_callhandler=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_imm_good=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_imm_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_fpLess=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_load_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_load32_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_load32_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store32_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store32_4=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_load16_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_load16_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_store16_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store16_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_load8_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_load8_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_store8_1=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_store8_4=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_80_0_skip=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.skip : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_move=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_inst=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_assign=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_get=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_set=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_alloc=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_consts=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_raise=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.raise 99 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_return=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_break=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.break 777 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_continue=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.continue 777 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_tick=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.tick : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_heap=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_loc=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_install=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_code=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_data=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_ffi=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_share=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_must=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_loop=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_seq=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_if=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_tail=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_callreturn=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_callhandler=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_imm_good=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_imm_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_fpLess=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_load_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_load32_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_load32_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store32_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store32_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_load16_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_load16_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_store16_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store16_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_load8_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_load8_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_store8_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_0_store8_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_skip=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.skip : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_move=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.move 17 [(1180591620717411303424,4),(4,1180591620717411303424)] : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_inst=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_assign=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.assign 1180591620717411303424 (.const 7) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_get=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.get 1180591620717411303424 .currHeap : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_set=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.set .handler (.var 1180591620717411303424) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.store (.var 2) 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_alloc=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.alloc 99 (.ln,sptInsert 32 () .ln) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_consts=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.storeConsts 99 98 97 96 [(true,7),(false,8)] : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_raise=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.raise 99 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_return=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.return 1180591620717411303424 [2,4,6,8,10,12] : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_break=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.break 777 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_continue=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.continue 777 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_tick=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.tick : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_heap=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.opCurrHeap .add 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_loc=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.locValue 1180591620717411303424 17 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_install=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.install 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_code=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.codeBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_data=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.dataBufferWrite 1180591620717411303424 1180591620717411303424 : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_ffi=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.ffi (Basis.Pure.MlString.ofString "abc") 1180591620717411303424 1180591620717411303424 1180591620717411303424 1180591620717411303424 (.ln,.ln) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_share=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load 1180591620717411303424 (.op .add [.var 1180591620717411303424,.const 7]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_must=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.mustTerminate (.alloc 99 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_loop=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.loop .ln (.alloc 99 (.ln,.ln)) .ln : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_seq=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.seq (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_if=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.ite .equal 1180591620717411303424 (.imm 7) (.alloc 99 (.ln,.ln)) (.alloc 98 (.ln,.ln)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_tail=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.call none none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_callreturn=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [] none : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_callhandler=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.call (some ([2,4,6,8,10,12],(.ln,.ln),.alloc 99 (.ln,.ln),1,2)) none [2,1180591620717411303424] (some (99,.alloc 98 (.ln,.ln),3,4)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_imm_good=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_imm_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.inst (.arith (.binop .add 1 2 (.imm 2))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_fpLess=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_load_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_load32_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_load32_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store32_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store32_4=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store32 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_load16_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_load16_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_store16_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store16_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store16 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_load8_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_load8_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .load8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_store8_1=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 1]) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_store8_4=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.shareInst .store8 99 (.op .add [.var 98,.const 4]) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_1_0_seq_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_loop_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_if_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_must_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_ret_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_handler_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_0_none_handler_bad=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c false)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_1_1_seq_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_loop_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_if_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_must_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_ret_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_handler_bad=F
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 1)) = false := by cbv

-- fin_1_1_none_handler_bad=T
example (c : AsmConfigExact 1) : fullInstOkLessExact (config c true)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 1)) = true := by cbv

-- fin_2_0_seq_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_loop_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_if_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_must_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_ret_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_handler_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_0_none_handler_bad=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c false)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_2_1_seq_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_loop_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_if_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_must_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_ret_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_handler_bad=F
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 2)) = false := by cbv

-- fin_2_1_none_handler_bad=T
example (c : AsmConfigExact 2) : fullInstOkLessExact (config c true)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 2)) = true := by cbv

-- fin_8_0_seq_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_loop_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_if_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_must_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_ret_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_handler_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_0_none_handler_bad=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c false)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_8_1_seq_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_loop_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_if_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_must_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_ret_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_handler_bad=F
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 8)) = false := by cbv

-- fin_8_1_none_handler_bad=T
example (c : AsmConfigExact 8) : fullInstOkLessExact (config c true)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 8)) = true := by cbv

-- fin_32_0_seq_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_loop_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_if_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_must_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_ret_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_handler_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_0_none_handler_bad=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c false)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_32_1_seq_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_loop_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_if_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_must_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_ret_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_handler_bad=F
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 32)) = false := by cbv

-- fin_32_1_none_handler_bad=T
example (c : AsmConfigExact 32) : fullInstOkLessExact (config c true)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 32)) = true := by cbv

-- fin_64_0_seq_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_loop_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_if_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_must_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_ret_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_handler_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_0_none_handler_bad=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c false)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_64_1_seq_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_loop_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_if_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_must_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_ret_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_handler_bad=F
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 64)) = false := by cbv

-- fin_64_1_none_handler_bad=T
example (c : AsmConfigExact 64) : fullInstOkLessExact (config c true)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 64)) = true := by cbv

-- fin_80_0_seq_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_loop_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_if_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_must_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_ret_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_handler_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_0_none_handler_bad=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c false)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 80)) = true := by cbv

-- fin_80_1_seq_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.seq .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_loop_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.loop .ln (.inst (.arith (.binop .add 1 2 (.imm 2)))) .ln : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_if_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.ite .equal 999 (.reg 998) .skip (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_must_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.mustTerminate (.inst (.arith (.binop .add 1 2 (.imm 2)))) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_ret_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.inst (.arith (.binop .add 1 2 (.imm 2))),1,2)) none [] none : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_handler_bad=F
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.call (some ([],(.ln,.ln),.skip,1,2)) none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 80)) = false := by cbv

-- fin_80_1_none_handler_bad=T
example (c : AsmConfigExact 80) : fullInstOkLessExact (config c true)
    (.call none none [] (some (99,.inst (.arith (.binop .add 1 2 (.imm 2))),3,4)) : WordLangProgHOL (BitVec 80)) = true := by cbv

example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (first second : WordLangProgHOL (BitVec width)) :
    fullInstOkLessExact c (.seq first second) =
      (fullInstOkLessExact c first && fullInstOkLessExact c second) := by
  exact fullInstOkLessExactSeq c first second

end Flapjack.Test.WordConvsFullInstNativeParity
