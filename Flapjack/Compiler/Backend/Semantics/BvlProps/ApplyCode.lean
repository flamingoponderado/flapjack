import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyCode

/-! Code replacement for BVL primitive application. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace CodeCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end CodeCarrier

/-- Replace code and compiler fields in a successful optional primitive result. -/
def setCodeOption {C F : Type} (code : Spt (Nat × Bvl.Exp)) (compiler : Compiler C) (oracle : CompileOracle C) (result : Option (BvlSem.Value × State C F)) :
    Option (BvlSem.Value × State C F) :=
  result.map fun (value, state) => (value, { state with code := code, compile := compiler, compileOracle := oracle })

/-- Global primitives commute with replacing code and compiler fields. -/
theorem applyGlobal_setCode {C F : Type} (op : ClosLang.GlobOp) (args : List BvlSem.Value)
    (state : State C F) (code : Spt (Nat × Bvl.Exp)) (compiler : Compiler C) (oracle : CompileOracle C) :
    applyGlobal op args { state with code := code, compile := compiler, compileOracle := oracle } =
      setCodeOption code compiler oracle (applyGlobal op args state) := by
  unfold applyGlobal setCodeOption
  repeat' split
  all_goals simp_all [Function.comp_def]

/-- Block primitives commute with replacing code and compiler fields. -/
theorem applyBlock_setCode {C F : Type} (op : ClosLang.BlockOp) (args : List BvlSem.Value)
    (state : State C F) (code : Spt (Nat × Bvl.Exp)) (compiler : Compiler C) (oracle : CompileOracle C) :
    applyBlock op args { state with code := code, compile := compiler, compileOracle := oracle } =
      setCodeOption code compiler oracle (applyBlock op args state) := by
  unfold applyBlock setCodeOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]

/-- Numeric primitives commute with replacing code and compiler fields. -/
theorem applyNumeric_setCode {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : State C F) (code : Spt (Nat × Bvl.Exp)) (compiler : Compiler C) (oracle : CompileOracle C) :
    applyNumeric op args { state with code := code, compile := compiler, compileOracle := oracle } =
      setCodeOption code compiler oracle (applyNumeric op args state) := by
  cases op <;> simp [applyNumeric, setCodeOption, Option.map_map, Function.comp_def]


/-- Memory primitives commute with replacing code and compiler fields. -/
theorem applyMemory_setCode {C F : Type} (op : ClosLang.MemOp) (args : List BvlSem.Value)
    (state : State C F) (code : Spt (Nat × Bvl.Exp)) (compiler : Compiler C) (oracle : CompileOracle C) :
    applyMemory op args { state with code := code, compile := compiler, compileOracle := oracle } =
      setCodeOption code compiler oracle (applyMemory op args state) := by
  unfold applyMemory setCodeOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try omega
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind, Function.comp_def]))



/-- A successful non-install operation remains successful when the code
domain is extended and the compiler fields are replaced. -/
theorem doApp_withCode {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state next : State C F) (value : BvlSem.Value) (code : Spt (Nat × Bvl.Exp))
    (compiler : Compiler C) (oracle : CompileOracle C)
    (run : doApp op args state = .val (value, next)) (notInstall : op ≠ .install)
    (domain : ∀ key, sptDomain state.code key → sptDomain code key) :
    doApp op args { state with code := code, compile := compiler, compileOracle := oracle } =
      .val (value, { next with code := code, compile := compiler, compileOracle := oracle }) := by
  cases op with
  | globOp operation =>
    cases found : applyGlobal operation args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyGlobal_setCode, found, setCodeOption]
  | blockOp operation =>
    cases found : applyBlock operation args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyBlock_setCode, found, setCodeOption]
  | memOp operation =>
    cases found : applyMemory operation args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyMemory_setCode, found, setCodeOption]
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyNumeric_setCode, found, setCodeOption]
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [doApp, found] using run
      subst pair
      simp [doApp, applyNumeric_setCode, found, setCodeOption]
  | label index =>
    cases args with
    | cons a rest => simp [doApp] at run
    | nil =>
      cases found : sptLookup index state.code with
      | none => simp [doApp, found] at run
      | some entry =>
        have present : sptDomain code index := domain index (by simp [sptDomain, found])
        cases newFound : sptLookup index code with
        | none => simp [sptDomain, newFound] at present
        | some replacement =>
          simp [doApp, found] at run
          rcases run with ⟨rfl, rfl⟩
          simp [doApp, newFound]
  | install => exact (notInstall rfl).elim
  | ffi | thunkOp =>
    simp only [doApp] at run ⊢
    repeat' split at run
    all_goals simp_all
    all_goals aesop

/-- A non-install error is preserved when the new code domain is contained
in the old one, or the error is not a type error. -/
theorem doApp_withCodeErr {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : State C F) (error : ErrorResult BvlSem.Value) (code : Spt (Nat × Bvl.Exp))
    (compiler : Compiler C) (oracle : CompileOracle C)
    (run : doApp op args state = .err error) (notInstall : op ≠ .install)
    (guard : (∀ key, sptDomain code key → sptDomain state.code key) ∨ error ≠ .abort .typeError) :
    doApp op args { state with code := code, compile := compiler, compileOracle := oracle } = .err error := by
  cases op with
  | globOp operation =>
    cases found : applyGlobal operation args state <;>
      simp_all [doApp, applyGlobal_setCode, setCodeOption]
  | blockOp operation =>
    cases found : applyBlock operation args state <;>
      simp_all [doApp, applyBlock_setCode, setCodeOption]
  | memOp operation =>
    cases found : applyMemory operation args state <;>
      simp_all [doApp, applyMemory_setCode, setCodeOption]
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args state <;>
      simp_all [doApp, applyNumeric_setCode, setCodeOption]
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args state <;>
      simp_all [doApp, applyNumeric_setCode, setCodeOption]
  | label index =>
    cases args with
    | cons a rest => simp_all [doApp]
    | nil =>
      cases found : sptLookup index state.code with
      | some entry => simp [doApp, found] at run
      | none =>
        simp [doApp, found] at run
        subst error
        have subset := guard.resolve_right (by simp)
        cases newFound : sptLookup index code with
        | none => simp [doApp, newFound]
        | some entry =>
          have present := subset index (by simp [sptDomain, newFound])
          simp [sptDomain, found] at present
  | install => exact (notInstall rfl).elim
  | ffi | thunkOp =>
    simp only [doApp] at run ⊢
    repeat' split at run
    all_goals simp_all

/-- Successful non-install application is preserved when the code domain grows. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_with_code"
  (fmap_as_finite_support := [refs])]
theorem doAppWithCode {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (value : BvlSem.Value)
    (next : Flapjack.Compiler.Backend.BvlSem.State C F) (code : Spt (Nat × Bvl.Exp))
    (compiler : Compiler C) (oracle : CompileOracle C)
    (h : doApp op args state = .val (value, next) ∧ op ≠ .install)
    (domain : ∀ key, sptDomain state.code key → sptDomain code key) :
    doApp op args { state with code := code, compile := compiler, compileOracle := oracle } =
      .val (value, { next with code := code, compile := compiler, compileOracle := oracle }) :=
  doApp_withCode op args state next value code compiler oracle h.1 h.2 domain

/-- Non-install errors persist under the original code-domain condition. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_with_code_err_not_Install"
  (fmap_as_finite_support := [refs])]
theorem doAppWithCodeErr {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (error : ErrorResult BvlSem.Value)
    (code : Spt (Nat × Bvl.Exp)) (compiler : Compiler C) (oracle : CompileOracle C)
    (h : doApp op args state = .err error ∧ op ≠ .install)
    (guard : (∀ key, sptDomain code key → sptDomain state.code key) ∨ error ≠ .abort .typeError) :
    doApp op args { state with code := code, compile := compiler, compileOracle := oracle } = .err error :=
  doApp_withCodeErr op args state error code compiler oracle h.1 h.2 guard

end Flapjack.Compiler.Backend.BvlProps
