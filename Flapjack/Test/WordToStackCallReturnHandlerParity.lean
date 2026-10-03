import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnHandler

namespace Flapjack.Test.WordToStackCallReturnHandlerParity
open Flapjack Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

example {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (argCount k f f' : Nat) :
    stackHandlerArgsNative (width := width) false dest argCount (k, f, f') =
      stackArgsNative dest argCount (k, f + 3, f' + 3) :=
  CallReturnHandler.stackHandlerArgsF dest argCount k f f'

example {width : Nat} [NeZero width] {β γ : Type}
    (l1 l2 k : Nat) (f : β) (f' : γ) :
    pushHandlerNative (width := width) false l1 l2 (k, f, f') =
      .seq (.stackAlloc 3)
        (.seq (.inst (.const k (1 : BitVec width)))
          (.seq (.stackStore k 0)
            (.seq (.locValue k l1 l2)
              (.seq (.stackStore k 1)
                (.seq (.get k .handler)
                  (.seq (.stackStore k 2)
                    (.seq .skip (.seq (.stackGetSize k) (.set .handler k))))))))) :=
  CallReturnHandler.pushHandlerF l1 l2 k f f'

example {width : Nat} [NeZero width] {β γ : Type}
    (k : Nat) (f : β) (f' : γ) (program : HolProg width) :
    popHandlerNative false (k, f, f') program =
      .seq (.stackLoad k 2) (.seq (.set .handler k) (.seq (.stackFree 3) program)) :=
  CallReturnHandler.popHandlerF k f f' program

example {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b k f f' clock : Nat) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'),
      {source with clock := clock}) =
      ((StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).1,
        {(StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).2
          with clock := clock}) :=
  CallReturnHandler.evaluatePushHandlerClock source a b k f f' clock

example {width handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (a b c : Nat) (wstack : List (WordSemStackFrame width))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW width))
    (len : Nat) (bs : List (BitVec width)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (a,b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) : f' + 4 ≤ sstack.length :=
  CallReturnHandler.stackRelConsLenSome k whandler n l0 l a b c wstack shandler sstack len bs f' lens relation

example {width handlerWidth : Nat} [NeZero width] [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (whandler' b c : Nat) (wstack : List (WordSemStackFrame width))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW width))
    (len : Nat) (bs : List (BitVec width)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (whandler',b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) :
    stackRel k whandler' wstack (some (holEl 2 sstack)) (sstack.drop (f' + 4)) len bs lens :=
  CallReturnHandler.stackRelDropSome k whandler n l0 l whandler' b c wstack shandler sstack len bs f' lens relation

example {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register f f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none,post) ∧
      post = {target with
        stackSpace := post.stackSpace, regs := post.regs,
        stack := post.stack, store := post.store} ∧
      (∀ index, index < target.stack.length - target.stackSpace →
        holEl index (target.stack.drop target.stackSpace) =
          holEl (index + 3) (post.stack.drop post.stackSpace)) ∧
      (∀ index, index ≠ register → StackSemStateOps.getVar index post =
        StackSemStateOps.getVar index target) ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length ∧
      stateRel ac register 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
          with locals := .ln, localsSize := some 0}
        post (f' :: lens) 0 :=
  CallReturnHandler.evaluatePushHandler ac register f f' a b retValue retProgram source target envs lens room relation location

example {α β : Type}
    (dest : Sum α β) (argCount k f f' : Nat) :
    stackHandlerArgsNative (width := 1) false dest argCount (k, f, f') =
      stackArgsNative dest argCount (k, f + 3, f' + 3) :=
  CallReturnHandler.stackHandlerArgsF dest argCount k f f'

example {β γ : Type}
    (l1 l2 k : Nat) (f : β) (f' : γ) :
    pushHandlerNative (width := 1) false l1 l2 (k, f, f') =
      .seq (.stackAlloc 3)
        (.seq (.inst (.const k (1 : BitVec 1)))
          (.seq (.stackStore k 0)
            (.seq (.locValue k l1 l2)
              (.seq (.stackStore k 1)
                (.seq (.get k .handler)
                  (.seq (.stackStore k 2)
                    (.seq .skip (.seq (.stackGetSize k) (.set .handler k))))))))) :=
  CallReturnHandler.pushHandlerF l1 l2 k f f'

example {β γ : Type}
    (k : Nat) (f : β) (f' : γ) (program : HolProg 1) :
    popHandlerNative false (k, f, f') program =
      .seq (.stackLoad k 2) (.seq (.set .handler k) (.seq (.stackFree 3) program)) :=
  CallReturnHandler.popHandlerF k f f' program

example {C F : Type}
    (source : StackSemStateFiniteExact 1 C F) (a b k f f' clock : Nat) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'),
      {source with clock := clock}) =
      ((StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).1,
        {(StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).2
          with clock := clock}) :=
  CallReturnHandler.evaluatePushHandlerClock source a b k f f' clock

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 1))
    (a b c : Nat) (wstack : List (WordSemStackFrame 1))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 1))
    (len : Nat) (bs : List (BitVec 1)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (a,b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) : f' + 4 ≤ sstack.length :=
  CallReturnHandler.stackRelConsLenSome k whandler n l0 l a b c wstack shandler sstack len bs f' lens relation

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 1))
    (whandler' b c : Nat) (wstack : List (WordSemStackFrame 1))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 1))
    (len : Nat) (bs : List (BitVec 1)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (whandler',b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) :
    stackRel k whandler' wstack (some (holEl 2 sstack)) (sstack.drop (f' + 4)) len bs lens :=
  CallReturnHandler.stackRelDropSome k whandler n l0 l whandler' b c wstack shandler sstack len bs f' lens relation

example {C F : Type}
    (ac : AsmConfigExact 1) (register f f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec 1))
    (source : WordSemStateFiniteExact 1 (Nat × C) F)
    (target : StackSemStateFiniteExact 1 C F)
    (envs : Spt (WordLocW 1) × Spt (WordLocW 1)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ post : StackSemStateFiniteExact 1 C F,
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none,post) ∧
      post = {target with
        stackSpace := post.stackSpace, regs := post.regs,
        stack := post.stack, store := post.store} ∧
      (∀ index, index < target.stack.length - target.stackSpace →
        holEl index (target.stack.drop target.stackSpace) =
          holEl (index + 3) (post.stack.drop post.stackSpace)) ∧
      (∀ index, index ≠ register → StackSemStateOps.getVar index post =
        StackSemStateOps.getVar index target) ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length ∧
      stateRel ac register 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
          with locals := .ln, localsSize := some 0}
        post (f' :: lens) 0 :=
  CallReturnHandler.evaluatePushHandler ac register f f' a b retValue retProgram source target envs lens room relation location

example {α β : Type}
    (dest : Sum α β) (argCount k f f' : Nat) :
    stackHandlerArgsNative (width := 8) false dest argCount (k, f, f') =
      stackArgsNative dest argCount (k, f + 3, f' + 3) :=
  CallReturnHandler.stackHandlerArgsF dest argCount k f f'

example {β γ : Type}
    (l1 l2 k : Nat) (f : β) (f' : γ) :
    pushHandlerNative (width := 8) false l1 l2 (k, f, f') =
      .seq (.stackAlloc 3)
        (.seq (.inst (.const k (1 : BitVec 8)))
          (.seq (.stackStore k 0)
            (.seq (.locValue k l1 l2)
              (.seq (.stackStore k 1)
                (.seq (.get k .handler)
                  (.seq (.stackStore k 2)
                    (.seq .skip (.seq (.stackGetSize k) (.set .handler k))))))))) :=
  CallReturnHandler.pushHandlerF l1 l2 k f f'

example {β γ : Type}
    (k : Nat) (f : β) (f' : γ) (program : HolProg 8) :
    popHandlerNative false (k, f, f') program =
      .seq (.stackLoad k 2) (.seq (.set .handler k) (.seq (.stackFree 3) program)) :=
  CallReturnHandler.popHandlerF k f f' program

example {C F : Type}
    (source : StackSemStateFiniteExact 8 C F) (a b k f f' clock : Nat) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'),
      {source with clock := clock}) =
      ((StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).1,
        {(StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).2
          with clock := clock}) :=
  CallReturnHandler.evaluatePushHandlerClock source a b k f f' clock

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 8))
    (a b c : Nat) (wstack : List (WordSemStackFrame 8))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 8))
    (len : Nat) (bs : List (BitVec 8)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (a,b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) : f' + 4 ≤ sstack.length :=
  CallReturnHandler.stackRelConsLenSome k whandler n l0 l a b c wstack shandler sstack len bs f' lens relation

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 8))
    (whandler' b c : Nat) (wstack : List (WordSemStackFrame 8))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 8))
    (len : Nat) (bs : List (BitVec 8)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (whandler',b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) :
    stackRel k whandler' wstack (some (holEl 2 sstack)) (sstack.drop (f' + 4)) len bs lens :=
  CallReturnHandler.stackRelDropSome k whandler n l0 l whandler' b c wstack shandler sstack len bs f' lens relation

example {C F : Type}
    (ac : AsmConfigExact 8) (register f f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec 8))
    (source : WordSemStateFiniteExact 8 (Nat × C) F)
    (target : StackSemStateFiniteExact 8 C F)
    (envs : Spt (WordLocW 8) × Spt (WordLocW 8)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ post : StackSemStateFiniteExact 8 C F,
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none,post) ∧
      post = {target with
        stackSpace := post.stackSpace, regs := post.regs,
        stack := post.stack, store := post.store} ∧
      (∀ index, index < target.stack.length - target.stackSpace →
        holEl index (target.stack.drop target.stackSpace) =
          holEl (index + 3) (post.stack.drop post.stackSpace)) ∧
      (∀ index, index ≠ register → StackSemStateOps.getVar index post =
        StackSemStateOps.getVar index target) ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length ∧
      stateRel ac register 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
          with locals := .ln, localsSize := some 0}
        post (f' :: lens) 0 :=
  CallReturnHandler.evaluatePushHandler ac register f f' a b retValue retProgram source target envs lens room relation location

example {α β : Type}
    (dest : Sum α β) (argCount k f f' : Nat) :
    stackHandlerArgsNative (width := 64) false dest argCount (k, f, f') =
      stackArgsNative dest argCount (k, f + 3, f' + 3) :=
  CallReturnHandler.stackHandlerArgsF dest argCount k f f'

example {β γ : Type}
    (l1 l2 k : Nat) (f : β) (f' : γ) :
    pushHandlerNative (width := 64) false l1 l2 (k, f, f') =
      .seq (.stackAlloc 3)
        (.seq (.inst (.const k (1 : BitVec 64)))
          (.seq (.stackStore k 0)
            (.seq (.locValue k l1 l2)
              (.seq (.stackStore k 1)
                (.seq (.get k .handler)
                  (.seq (.stackStore k 2)
                    (.seq .skip (.seq (.stackGetSize k) (.set .handler k))))))))) :=
  CallReturnHandler.pushHandlerF l1 l2 k f f'

example {β γ : Type}
    (k : Nat) (f : β) (f' : γ) (program : HolProg 64) :
    popHandlerNative false (k, f, f') program =
      .seq (.stackLoad k 2) (.seq (.set .handler k) (.seq (.stackFree 3) program)) :=
  CallReturnHandler.popHandlerF k f f' program

example {C F : Type}
    (source : StackSemStateFiniteExact 64 C F) (a b k f f' clock : Nat) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'),
      {source with clock := clock}) =
      ((StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).1,
        {(StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).2
          with clock := clock}) :=
  CallReturnHandler.evaluatePushHandlerClock source a b k f f' clock

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 64))
    (a b c : Nat) (wstack : List (WordSemStackFrame 64))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 64))
    (len : Nat) (bs : List (BitVec 64)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (a,b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) : f' + 4 ≤ sstack.length :=
  CallReturnHandler.stackRelConsLenSome k whandler n l0 l a b c wstack shandler sstack len bs f' lens relation

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 64))
    (whandler' b c : Nat) (wstack : List (WordSemStackFrame 64))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 64))
    (len : Nat) (bs : List (BitVec 64)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (whandler',b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) :
    stackRel k whandler' wstack (some (holEl 2 sstack)) (sstack.drop (f' + 4)) len bs lens :=
  CallReturnHandler.stackRelDropSome k whandler n l0 l whandler' b c wstack shandler sstack len bs f' lens relation

example {C F : Type}
    (ac : AsmConfigExact 64) (register f f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × C) F)
    (target : StackSemStateFiniteExact 64 C F)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ post : StackSemStateFiniteExact 64 C F,
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none,post) ∧
      post = {target with
        stackSpace := post.stackSpace, regs := post.regs,
        stack := post.stack, store := post.store} ∧
      (∀ index, index < target.stack.length - target.stackSpace →
        holEl index (target.stack.drop target.stackSpace) =
          holEl (index + 3) (post.stack.drop post.stackSpace)) ∧
      (∀ index, index ≠ register → StackSemStateOps.getVar index post =
        StackSemStateOps.getVar index target) ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length ∧
      stateRel ac register 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
          with locals := .ln, localsSize := some 0}
        post (f' :: lens) 0 :=
  CallReturnHandler.evaluatePushHandler ac register f f' a b retValue retProgram source target envs lens room relation location

example {α β : Type}
    (dest : Sum α β) (argCount k f f' : Nat) :
    stackHandlerArgsNative (width := 80) false dest argCount (k, f, f') =
      stackArgsNative dest argCount (k, f + 3, f' + 3) :=
  CallReturnHandler.stackHandlerArgsF dest argCount k f f'

example {β γ : Type}
    (l1 l2 k : Nat) (f : β) (f' : γ) :
    pushHandlerNative (width := 80) false l1 l2 (k, f, f') =
      .seq (.stackAlloc 3)
        (.seq (.inst (.const k (1 : BitVec 80)))
          (.seq (.stackStore k 0)
            (.seq (.locValue k l1 l2)
              (.seq (.stackStore k 1)
                (.seq (.get k .handler)
                  (.seq (.stackStore k 2)
                    (.seq .skip (.seq (.stackGetSize k) (.set .handler k))))))))) :=
  CallReturnHandler.pushHandlerF l1 l2 k f f'

example {β γ : Type}
    (k : Nat) (f : β) (f' : γ) (program : HolProg 80) :
    popHandlerNative false (k, f, f') program =
      .seq (.stackLoad k 2) (.seq (.set .handler k) (.seq (.stackFree 3) program)) :=
  CallReturnHandler.popHandlerF k f f' program

example {C F : Type}
    (source : StackSemStateFiniteExact 80 C F) (a b k f f' clock : Nat) :
    StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'),
      {source with clock := clock}) =
      ((StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).1,
        {(StackSemEvaluate.evaluate (pushHandlerNative false a b (k, f, f'), source)).2
          with clock := clock}) :=
  CallReturnHandler.evaluatePushHandlerClock source a b k f f' clock

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 80))
    (a b c : Nat) (wstack : List (WordSemStackFrame 80))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 80))
    (len : Nat) (bs : List (BitVec 80)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (a,b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) : f' + 4 ≤ sstack.length :=
  CallReturnHandler.stackRelConsLenSome k whandler n l0 l a b c wstack shandler sstack len bs f' lens relation

example {handlerWidth : Nat} [NeZero handlerWidth]
    (k whandler : Nat) (n : Option Nat) (l0 l : List (Nat × WordLocW 80))
    (whandler' b c : Nat) (wstack : List (WordSemStackFrame 80))
    (shandler : Option (WordLocW handlerWidth)) (sstack : List (WordLocW 80))
    (len : Nat) (bs : List (BitVec 80)) (f' : Nat) (lens : List Nat)
    (relation : stackRel k whandler (.stackFrame n l0 l (some (whandler',b,c)) :: wstack)
      shandler sstack len bs (f' :: lens)) :
    stackRel k whandler' wstack (some (holEl 2 sstack)) (sstack.drop (f' + 4)) len bs lens :=
  CallReturnHandler.stackRelDropSome k whandler n l0 l whandler' b c wstack shandler sstack len bs f' lens relation

example {C F : Type}
    (ac : AsmConfigExact 80) (register f f' a b retValue : Nat)
    (retProgram : WordLangProgHOL (BitVec 80))
    (source : WordSemStateFiniteExact 80 (Nat × C) F)
    (target : StackSemStateFiniteExact 80 C F)
    (envs : Spt (WordLocW 80) × Spt (WordLocW 80)) (lens : List Nat)
    (room : 3 ≤ target.stackSpace)
    (relation : stateRel ac register 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      target (f' :: lens) 0)
    (location : StackSem.locCheckExact target.code (a,b)) :
    ∃ post : StackSemStateFiniteExact 80 C F,
      StackSemEvaluate.evaluate (pushHandlerNative false a b (register,f,f'), target) =
        (none,post) ∧
      post = {target with
        stackSpace := post.stackSpace, regs := post.regs,
        stack := post.stack, store := post.store} ∧
      (∀ index, index < target.stack.length - target.stackSpace →
        holEl index (target.stack.drop target.stackSpace) =
          holEl (index + 3) (post.stack.drop post.stackSpace)) ∧
      (∀ index, index ≠ register → StackSemStateOps.getVar index post =
        StackSemStateOps.getVar index target) ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length ∧
      stateRel ac register 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (retValue,retProgram,a,b)) source
          with locals := .ln, localsSize := some 0}
        post (f' :: lens) 0 :=
  CallReturnHandler.evaluatePushHandler ac register f f' a b retValue retProgram source target envs lens room relation location

end Flapjack.Test.WordToStackCallReturnHandlerParity
