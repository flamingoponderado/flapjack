import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopTop
set_option maxRecDepth 16384
namespace Flapjack.Test.WordToStackNoShmemopTopParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
-- tp_empty_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
  rfl

-- tp_safe_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [(20,0,.skip),(20,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(21,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_ignored_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [(21,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_shared_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [(20,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,false) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_empty_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
  rfl

-- tp_safe_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [(20,0,.skip),(20,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(21,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_ignored_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [(21,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_shared_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [(20,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,false) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_empty_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
  rfl

-- tp_safe_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [(20,0,.skip),(20,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(21,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_ignored_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [(21,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_shared_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [(20,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,false) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_empty_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
  rfl

-- tp_safe_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [(20,0,.skip),(20,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(21,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (true,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_ignored_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [(21,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,true) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- tp_shared_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [(20,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noShmemop row.2)) = (false,false) := by
  simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
  rfl

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : List (BitVec width)) (fs : Config) (ns : List Nat)
    (outputs : List (Nat × HolProg width))
    (compiled : compileNative conf false ps = (bs,fs,ns,outputs))
    (guard : (ps.all fun row => noShareInstSubprogsHOL row.2.2) = true) :
    (outputs.all fun row => noShmemop row.2) = true :=
  compileNoShmemop conf ps bs fs ns outputs compiled guard

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (guard : (ps.all fun row => noShareInstSubprogsHOL row.2.2) = true) :
    ((compileNative conf false ps).2.2.2.all fun row => noShmemop row.2) = true :=
  compileNoShmemop conf ps (compileNative conf false ps).1
    (compileNative conf false ps).2.1 (compileNative conf false ps).2.2.1
    (compileNative conf false ps).2.2.2 rfl guard
end Flapjack.Test.WordToStackNoShmemopTopParity
