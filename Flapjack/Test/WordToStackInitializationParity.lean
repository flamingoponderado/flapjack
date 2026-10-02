import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization

/-! Independent original initializer projections, including complete frame-size
Spt trees and compilation callback outputs. Regression evidence only. -/
namespace Flapjack.Test.WordToStackInitializationParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open WordToStack.Native WordToStack.Native.Initialization

-- mi_1_0_reset
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(0,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_0_sizes
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_0_inherit
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_1_0_store
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_1_0_oracle
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_1_reset
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(1,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_1_sizes
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_1_inherit
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ls (0,.tick)) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_1_1_store
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_1_1_oracle
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_2_reset
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(2,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_2_sizes
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_2_inherit
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs .ln (2,.skip) .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_1_2_store
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_1_2_oracle
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_3_reset
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(3,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_3_sizes
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_3_inherit
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bn .ln .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_1_3_store
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_1_3_oracle
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_4_reset
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(4,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_4_sizes
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.bs (.ls 18) 0 (.ls 0)) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_4_inherit
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_1_4_store
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_1_4_oracle
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_0_0_compile
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_0_99_compile
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_17_0_compile
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((0 :: []),(1,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_17_99_compile
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((0 :: []),(100,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_300_0_compile
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((0 :: []),(1,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_1_300_99_compile
example (c : AsmConfigExact 1) (t : StackSemStateFiniteExact 1 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((0 :: []),(100,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_0_reset
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(0,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_0_sizes
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_0_inherit
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_8_0_store
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_8_0_oracle
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_1_reset
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(1,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_1_sizes
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_1_inherit
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ls (0,.tick)) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_8_1_store
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_8_1_oracle
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_2_reset
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(2,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_2_sizes
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_2_inherit
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs .ln (2,.skip) .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_8_2_store
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_8_2_oracle
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_3_reset
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(3,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_3_sizes
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_3_inherit
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bn .ln .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_8_3_store
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_8_3_oracle
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_4_reset
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(4,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_4_sizes
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.bs (.ls 18) 0 (.ls 0)) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_4_inherit
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_8_4_store
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_8_4_oracle
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_0_0_compile
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_0_99_compile
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_17_0_compile
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((128 :: (128 :: (128 :: (128 :: (160 :: (128 :: (16 :: []))))))),(7,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_17_99_compile
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((128 :: (128 :: (128 :: (128 :: (160 :: (128 :: (16 :: []))))))),(106,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_300_0_compile
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((128 :: (128 :: (128 :: (128 :: (160 :: (128 :: (16 :: []))))))),(7,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_8_300_99_compile
example (c : AsmConfigExact 8) (t : StackSemStateFiniteExact 8 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((128 :: (128 :: (128 :: (128 :: (160 :: (128 :: (16 :: []))))))),(106,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_0_reset
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(0,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_0_sizes
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_0_inherit
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_64_0_store
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_64_0_oracle
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_1_reset
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(1,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_1_sizes
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_1_inherit
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ls (0,.tick)) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_64_1_store
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_64_1_oracle
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_2_reset
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(2,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_2_sizes
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_2_inherit
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs .ln (2,.skip) .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_64_2_store
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_64_2_oracle
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_3_reset
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(3,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_3_sizes
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_3_inherit
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bn .ln .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_64_3_store
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_64_3_oracle
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_4_reset
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(4,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_4_sizes
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.bs (.ls 18) 0 (.ls 0)) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_4_inherit
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_64_4_store
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_64_4_oracle
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_0_0_compile
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_0_99_compile
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_17_0_compile
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((70377334112256 :: []),(1,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_17_99_compile
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((70377334112256 :: []),(100,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_300_0_compile
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((70377334112256 :: []),(1,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_64_300_99_compile
example (c : AsmConfigExact 64) (t : StackSemStateFiniteExact 64 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((70377334112256 :: []),(100,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_0_reset
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(0,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_0_sizes
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_0_inherit
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_80_0_store
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_80_0_oracle
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 0 (.word 7), clock := 99, be := true }) (.ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_1_reset
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(1,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_1_sizes
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_1_inherit
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.ls (0,.tick)) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_80_1_store
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_80_1_oracle
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 1 (.word 7), clock := 99, be := true }) (.ls (0,.tick)) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_2_reset
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(2,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_2_sizes
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.ls 0) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_2_inherit
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs .ln (2,.skip) .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_80_2_store
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_80_2_oracle
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 2 (.word 7), clock := 99, be := true }) (.bs .ln (2,.skip) .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_3_reset
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(3,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_3_sizes
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = .ln := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_3_inherit
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bn .ln .ln) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_80_3_store
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_80_3_oracle
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 3 (.word 7), clock := 99, be := true }) (.bn .ln .ln) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_4_reset
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (sptToAList s.locals,s.localsSize,s.handler,s.termdep,s.stackLimit,s.stackMax,s.permute 7 9,s.permute 0 70)) = (((0,(.loc 1 0)) :: []),((some 0),(0,(0,(4,((some 1),(9,70))))))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_4_sizes
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.stackSize) = (.bs (.ls 18) 0 (.ls 0)) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_4_inherit
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.memory=t.memory ∧ s.mdomain=t.mdomain ∧ s.shMdomain=t.shMdomain ∧ s.gcFun=t.gcFun ∧ s.fpRegs=t.fpRegs ∧ s.code=(.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) ∧ s.dataBuffer=t.dataBuffer ∧ s.codeBuffer=t.codeBuffer ∧ s.ffi=t.ffi ∧ s.clock=99 ∧ s.be=true ∧ s.stack=[]) := by
  simp [makeInit]

-- mi_80_4_store
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); (s.store=t.store.eraseEq .handler) := by
  simp [makeInit]

-- mi_80_4_oracle
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (let s := makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with stack := List.replicate 4 (.word 7), clock := 99, be := true }) (.bs (.ls (10,.inst (.const 40 7))) (3,.tick) (.ls (0,.skip))) (fun n => ((n+100,17),[(7,3,.tick)])); s.compileOracle 3) = ((103,17),((7,(3,.tick)) :: [])) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_0_0_compile
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_0_99_compile
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,0) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = none := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_17_0_compile
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((70377334112256 :: []),(1,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_17_99_compile
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,17) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (17 :: [])),((70377334112256 :: []),(100,27)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_300_0_compile
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (0,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((70377334112256 :: []),(1,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

-- mi_80_300_99_compile
example (c : AsmConfigExact 80) (t : StackSemStateFiniteExact 80 Nat Unit) :
    (makeInit ({ c with regCount := 8, avoidRegs := [0,1], validImm := fun _ _ => false }) 4 ({ t with compile := fun cfg ps => if cfg=0 then none else some ([BitVec.ofNat 8 ps.length,BitVec.ofNat 8 cfg],cfg+10) }) .ln (fun n => ((n+100,17),[]))).compile (99,300) [(7,3,.alloc 99 (.ln,sptInsert 32 () .ln)),(8,0,.tick)] = (some ((2 :: (300 :: [])),((70377334112256 :: []),(100,310)))) := by
  dsimp only [makeInit]
  all_goals cbv

def runChecks : IO Bool := do
  IO.println "PASS original WordToStack initializer (124 kernel projection rows)"
  pure true
end Flapjack.Test.WordToStackInitializationParity
