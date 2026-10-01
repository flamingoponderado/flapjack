import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallTop
set_option maxRecDepth 16384
namespace Flapjack.Test.WordToStackNoInstallTopParity
open Flapjack Flapjack.WordProps Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
-- nt_empty_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
    rfl

-- nt_safe_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [(20,0,.skip),(21,999,.alloc 999 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_shadow_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [(20,0,.skip),(20,7,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ False) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_bad_1
example (conf : AsmConfigExact 1) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 1)) := [(20,0,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 0, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_empty_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
    rfl

-- nt_safe_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [(20,0,.skip),(21,999,.alloc 999 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_shadow_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [(20,0,.skip),(20,7,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ False) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_bad_32
example (conf : AsmConfigExact 32) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 32)) := [(20,0,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 9, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_empty_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
    rfl

-- nt_safe_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [(20,0,.skip),(21,999,.alloc 999 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_shadow_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [(20,0,.skip),(20,7,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ False) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_bad_64
example (conf : AsmConfigExact 64) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [(20,0,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 3, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_empty_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative]
    rfl

-- nt_safe_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [(20,0,.skip),(21,999,.alloc 999 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (true,true) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_shadow_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [(20,0,.skip),(20,7,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ False) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- nt_bad_80
example (conf : AsmConfigExact 80) :
    let ps : List (Nat × Nat × WordLangProgHOL (BitVec 80)) := [(20,0,.install 0 1 2 3 (.ln,.ln))];
    ((ps.map Prod.fst).Nodup ↔ True) ∧
    ((ps.all fun row => noInstallSubprogsHOL row.2.2),
      ((compileNative {conf with regCount := 1004, avoidRegs := [1,1]} false ps).2.2.2.all
        fun row => noInstall row.2)) = (false,false) := by
  constructor
  · decide +kernel
  · simp only [compileNative, compileWordToStackNative, raiseStubNative, storeConstsStubNative, compileProgNative, compNative, maxVarHOL]
    rfl

-- The original complete code-map guard holds for a shadowed bad entry,
-- while the duplicate identifiers invalidate the top theorem premise.
example {width : Nat} [NeZero width] :
    noInstallCode (sptFromAList ([(20,0,.skip),(20,7,.install 0 1 2 3 (.ln,.ln))] :
      List (Nat × Nat × WordLangProgHOL (BitVec width)))) := by
  intro key count program h
  rw [sptLookup_sptFromAList] at h
  by_cases hk : key = 20
  · simp [sptAListLookup,hk] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  · simp [sptAListLookup,hk] at h

example {width : Nat} [NeZero width] :
    noInstallCode (sptFromAList ([(20,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec width)))) := by
  intro key count program h
  rw [sptLookup_sptFromAList] at h
  by_cases hk : key = 20
  · simp [sptAListLookup,hk] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  · simp [sptAListLookup,hk] at h

example {width : Nat} [NeZero width] :
    noInstallCode (sptFromAList ([] : List (Nat × Nat × WordLangProgHOL (BitVec width)))) := by
  intro key count program h
  cases h

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : List (BitVec width)) (fs : Config) (ns : List Nat)
    (outputs : List (Nat × HolProg width))
    (distinct : (ps.map Prod.fst).Nodup)
    (codeGuard : noInstallCode (sptFromAList ps))
    (compiled : compileNative conf false ps = (bs,fs,ns,outputs)) :
    (outputs.all fun row => noInstall row.2) = true :=
  wordToStackCompileNoInstall conf ps bs fs ns outputs distinct codeGuard compiled

example {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (distinct : (ps.map Prod.fst).Nodup)
    (codeGuard : noInstallCode (sptFromAList ps)) :
    ((compileNative conf false ps).2.2.2.all fun row => noInstall row.2) = true :=
  wordToStackCompileNoInstall conf ps (compileNative conf false ps).1
    (compileNative conf false ps).2.1 (compileNative conf false ps).2.2.1
    (compileNative conf false ps).2.2.2 distinct codeGuard rfl
end Flapjack.Test.WordToStackNoInstallTopParity
