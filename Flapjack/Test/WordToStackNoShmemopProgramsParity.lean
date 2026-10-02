import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrograms
set_option maxRecDepth 16384
namespace Flapjack.Test.WordToStackNoShmemopProgramsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
-- pl_empty_1
example (conf : AsmConfigExact 1) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 1)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 0 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  rfl

-- pl_safe_1
example (conf : AsmConfigExact 1) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 1)) := [(true,0,.skip),(true,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(false,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 0 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_ignored_1
example (conf : AsmConfigExact 1) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 1)) := [(false,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 0 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_shared_1
example (conf : AsmConfigExact 1) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 1)) := [(true,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 0 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,false) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_empty_32
example (conf : AsmConfigExact 32) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 32)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 2 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  rfl

-- pl_safe_32
example (conf : AsmConfigExact 32) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 32)) := [(true,0,.skip),(true,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(false,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 2 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_ignored_32
example (conf : AsmConfigExact 32) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 32)) := [(false,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 2 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_shared_32
example (conf : AsmConfigExact 32) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 32)) := [(true,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 2 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,false) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_empty_64
example (conf : AsmConfigExact 64) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 64)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 64 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  rfl

-- pl_safe_64
example (conf : AsmConfigExact 64) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 64)) := [(true,0,.skip),(true,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(false,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 64 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_ignored_64
example (conf : AsmConfigExact 64) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 64)) := [(false,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 64 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_shared_64
example (conf : AsmConfigExact 64) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 64)) := [(true,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf false 64 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,false) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_empty_80
example (conf : AsmConfigExact 80) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 80)) := [];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 999 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  rfl

-- pl_safe_80
example (conf : AsmConfigExact 80) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 80)) := [(true,0,.skip),(true,999,.seq (.alloc 999 (.bs .ln () .ln,.bn .ln .ln)) (.storeConsts 0 1 2 3 [(true,7),(false,8)])),(false,7,.return 0 [2,4])];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 999 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (true,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_ignored_80
example (conf : AsmConfigExact 80) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 80)) := [(false,17,.call none none [999] (some (999,.shareInst .load 0 (.var 3),7,9)))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 999 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,true) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

-- pl_shared_80
example (conf : AsmConfigExact 80) :
    let ps : List (Bool × Nat × WordLangProgHOL (BitVec 80)) := [(true,0,.shareInst .load 0 (.var 3))];
    ((ps.all fun row => noShareInstSubprogsHOL row.2.2),
      ((compileWordToStackNative conf true 999 ps
        (.append (.list [4]) (.list [7]),17)).1.all fun row => noShmemop row.2)) =
      (false,false) := by
  simp only [compileWordToStackNative, compileProgNative, compNative, maxVarHOL]
  rfl

example {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (k : Nat)
    (ps : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (outputs : List (β × HolProg width))
    (frames : List Nat) (residual : AppList (BitVec width) × Nat)
    (guard : (ps.all fun row => noShareInstSubprogsHOL row.2.2) = true)
    (compiled : compileWordToStackNative conf perf k ps bs = (outputs,frames,residual)) :
    (outputs.all fun row => noShmemop row.2) = true :=
  compileWordToStackNoShareInst conf perf k ps bs outputs frames residual guard compiled

example {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (k : Nat)
    (ps : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat)
    (guard : (ps.all fun row => noShareInstSubprogsHOL row.2.2) = true) :
    ((compileWordToStackNative conf perf k ps bs).1.all fun row => noShmemop row.2) = true :=
  compileWordToStackNoShareInst conf perf k ps bs
    (compileWordToStackNative conf perf k ps bs).1
    (compileWordToStackNative conf perf k ps bs).2.1
    (compileWordToStackNative conf perf k ps bs).2.2 guard rfl
end Flapjack.Test.WordToStackNoShmemopProgramsParity
