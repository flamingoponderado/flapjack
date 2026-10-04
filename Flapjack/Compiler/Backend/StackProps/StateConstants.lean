import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Full state-operation preservation and update-commutation statements from
stackPropsScript.sml20-168. Generic width, configuration and FFI parameters
are retained. These are support theorems, not an evaluator correctness result. -/
namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.StackSemStateOps

namespace StateConstants
/-- Canonical codec witness for the actual imported state owner; infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end StateConstants


/-- Full original source statement at line 20, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setStoreConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordStoreHOL) (y : WordLocW width) (z : StackSemStateFiniteExact width C F) :
    (setStore x y z).ffi = z.ffi ∧
   (setStore x y z).clock = z.clock ∧
   (setStore x y z).useAlloc = z.useAlloc ∧
   (setStore x y z).useStore = z.useStore ∧
   (setStore x y z).useStack = z.useStack ∧
   (setStore x y z).code = z.code ∧
   (setStore x y z).be = z.be ∧
   (setStore x y z).gcFun = z.gcFun ∧
   (setStore x y z).memory = z.memory ∧
   (setStore x y z).mdomain = z.mdomain ∧
   (setStore x y z).shMdomain = z.shMdomain ∧
   (setStore x y z).bitmaps = z.bitmaps ∧
   (setStore x y z).dataBuffer = z.dataBuffer ∧
   (setStore x y z).codeBuffer = z.codeBuffer ∧
   (setStore x y z).compile = z.compile ∧
   (setStore x y z).compileOracle = z.compileOracle ∧
   (setStore x y z).stackSpace = z.stackSpace ∧
   (setStore x y z).stack = z.stack := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Full original source statement at line 43, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setStoreWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordStoreHOL) (y : WordLocW width) (z : StackSemStateFiniteExact width C F) (a : Nat) :
    setStore x y { z with clock := a } = { setStore x y z with clock := a } := by
  rfl


/-- Full original source statement at line 49, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setVarConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLocW width) (z : StackSemStateFiniteExact width C F) :
    (setVar x y z).ffi = z.ffi ∧
   (setVar x y z).clock = z.clock ∧
   (setVar x y z).useAlloc = z.useAlloc ∧
   (setVar x y z).useStore = z.useStore ∧
   (setVar x y z).useStack = z.useStack ∧
   (setVar x y z).code = z.code ∧
   (setVar x y z).be = z.be ∧
   (setVar x y z).fpRegs = z.fpRegs ∧
   (setVar x y z).dataBuffer = z.dataBuffer ∧
   (setVar x y z).codeBuffer = z.codeBuffer ∧
   (setVar x y z).gcFun = z.gcFun ∧
   (setVar x y z).memory = z.memory ∧
   (setVar x y z).mdomain = z.mdomain ∧
   (setVar x y z).shMdomain = z.shMdomain ∧
   (setVar x y z).bitmaps = z.bitmaps ∧
   (setVar x y z).compile = z.compile ∧
   (setVar x y z).compileOracle = z.compileOracle ∧
   (setVar x y z).store = z.store ∧
   (setVar x y z).stack = z.stack ∧
   (setVar x y z).stackSpace = z.stackSpace := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Full original source statement at line 74, including all conjuncts.
The updated FFI host is independently polymorphic, as in HOL gamma-to-delta
state record update; all other updates keep the original input carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (x : Nat) (y : WordLocW width) (z : StackSemStateFiniteExact width C F)
    (clk : Nat) (m : BitVec width → WordLocW width) (newFfi : HolFfiState OtherF)
    (stk : List (WordLocW width)) (stk_space : Nat) :
    setVar x y { z with clock := clk } = { setVar x y z with clock := clk } ∧
   setVar x y { z with memory := m } = { setVar x y z with memory := m } ∧
   setVar x y ({ z with ffi := newFfi } : StackSemStateFiniteExact width C OtherF) = { setVar x y z with ffi := newFfi } ∧
   setVar x y { z with stack := stk } = { setVar x y z with stack := stk } ∧
   setVar x y { z with stackSpace := stk_space } = { setVar x y z with stackSpace := stk_space } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩


/-- Full original source statement at line 84, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setFpVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : BitVec 64) (z : StackSemStateFiniteExact width C F) (k : Nat) :
    setFpVar x y { z with clock := k } = { setFpVar x y z with clock := k } := by
  rfl


/-- Full original source statement at line 90, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setFpVarConstFields {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : BitVec 64) (z : StackSemStateFiniteExact width C F) :
    (setFpVar x y z).ffi = z.ffi ∧
   (setFpVar x y z).clock = z.clock ∧
   (setFpVar x y z).useAlloc = z.useAlloc ∧
   (setFpVar x y z).useStore = z.useStore ∧
   (setFpVar x y z).useStack = z.useStack ∧
   (setFpVar x y z).code = z.code ∧
   (setFpVar x y z).be = z.be ∧
   (setFpVar x y z).gcFun = z.gcFun ∧
   (setFpVar x y z).mdomain = z.mdomain ∧
   (setFpVar x y z).shMdomain = z.shMdomain ∧
   (setFpVar x y z).bitmaps = z.bitmaps ∧
   (setFpVar x y z).compile = z.compile ∧
   (setFpVar x y z).compileOracle = z.compileOracle ∧
   (setFpVar x y z).stack = z.stack ∧
   (setFpVar x y z).stackSpace = z.stackSpace := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Full original source statement at line 110, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getFpVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : StackSemStateFiniteExact width C F) (k : Nat) :
    getFpVar x { y with clock := k } = getFpVar x y := by
  rfl


/-- Full original source statement at line 116, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (t : StackSemStateFiniteExact width C F) (clk stk_space : Nat) :
    getVar r { t with clock := clk } =
  (getVar r t) ∧
  getVar r { t with stackSpace := stk_space } =
  (getVar r t) := by
  exact ⟨rfl, rfl⟩


/-- Full original source statement at line 125, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarsWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (xs : List Nat) (y : StackSemStateFiniteExact width C F) (k : Nat) :
    getVars xs { y with clock := k } = getVars xs y := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [getVars, getVar]
      rw [ih]



/-- Full original source statement at line 131, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getVarImmWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordRegImm (BitVec width)) (y : StackSemStateFiniteExact width C F) (k : Nat) :
    Flapjack.StackSemStateOps.getVarImm x { y with clock := k } = Flapjack.StackSemStateOps.getVarImm x y := by
  cases x <;> rfl


/-- Full original source statement at line 137, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem setFpVarConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : BitVec 64) (z : StackSemStateFiniteExact width C F) :
    (setFpVar x y z).stackSpace = z.stackSpace ∧
  (setFpVar x y z).stack = z.stack := by
  exact ⟨rfl, rfl⟩


/-- Full source statement at line 144: x and z have independently polymorphic
word, configuration and FFI carriers, as confirmed by the original full types.
The first two conjuncts concern x; all remaining thirteen concern z. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem emptyEnvConst {width otherWidth : Nat} [NeZero width] [NeZero otherWidth]
    {C F OtherC OtherF : Type}
    (x : StackSemStateFiniteExact width C F)
    (z : StackSemStateFiniteExact otherWidth OtherC OtherF) :
    (emptyEnv x).ffi = x.ffi ∧
   (emptyEnv x).clock = x.clock ∧
   (emptyEnv z).useAlloc = z.useAlloc ∧
   (emptyEnv z).useStore = z.useStore ∧
   (emptyEnv z).useStack = z.useStack ∧
   (emptyEnv z).code = z.code ∧
   (emptyEnv z).be = z.be ∧
   (emptyEnv z).gcFun = z.gcFun ∧
   (emptyEnv z).mdomain = z.mdomain ∧
   (emptyEnv z).shMdomain = z.shMdomain ∧
   (emptyEnv z).bitmaps = z.bitmaps ∧
   (emptyEnv z).dataBuffer = z.dataBuffer ∧
   (emptyEnv z).codeBuffer = z.codeBuffer ∧
   (emptyEnv z).compile = z.compile ∧
   (emptyEnv z).compileOracle = z.compileOracle := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Full original source statement at line 164, including all conjuncts.
No additional hypothesis or state-field specialization is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem emptyEnvWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : StackSemStateFiniteExact width C F) (y : Nat) :
    emptyEnv { x with clock := y } = { emptyEnv x with clock := y } := by
  rfl


end Flapjack.Compiler.Backend.StackProps
