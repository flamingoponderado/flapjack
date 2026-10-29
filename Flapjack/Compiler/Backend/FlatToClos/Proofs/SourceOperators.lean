import Flapjack.Compiler.Backend.FlatToClos.Proofs.Ffi
import Flapjack.Compiler.Backend.FlatToClos.Proofs.PrimitiveTests
import Flapjack.Compiler.Backend.FlatToClos.Proofs.PrimitiveArith
import Flapjack.Compiler.Backend.FlatToClos.Proofs.PrimitiveConversions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.WordShifts
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Array
import Flapjack.Compiler.Backend.FlatToClos.Proofs.MemoryExpressions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EqualityExpressions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.ThunkOperations

/-! Dispatcher for ordinary source operators in the proof-side simulation.
The special application, assignment, dynamic installation, and thunk forcing cases
require additional induction hypotheses. This is not a reviewed HOL port. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- These source operators have no ordinary Flat semantics: after argument
evaluation they abort with a type error. -/
theorem rejectedSourceOp_apply {C F : Type} (state : FlatSem.State C F)
    (op : AstHOL.Op) (args : List FlatSem.Value)
    (rejected : op = .opderef ∨ op = .aallocEmpty ∨ op = .envId) :
    (FlatSem.applyResult state (.src op) args).2 = .err (.abort .typeError) := by
  rcases rejected with rfl | rfl | rfl <;>
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
      FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy]

/-- The source operators without ordinary Flat semantics preserve argument
errors; successful arguments contradict the non-type-error premise. -/
theorem evaluate_rejectedSourceOp {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : AstHOL.Op) (args : List FlatLang.Exp)
    (rejected : op = .opderef ∨ op = .aallocEmpty ∨ op = .envId)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src op) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps_reverse] at argsSim
  simp only [compile, compileExps] at ⊢
  have compiled : compileExp names (.app trace (.src op) args) =
      .let .none (compileExps names args).reverse (.var .none 0) := by
    rcases rejected with rfl | rfl | rfl <;> simp [compileExp, compileOp]
  rw [compiled, FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have failure : (FlatSem.applyResult next (.src op) sourceArgs.reverse).2 =
            .err (.abort .typeError) := rejectedSourceOp_apply next op _ rejected
        have fixed := flatFix
        rw [flatRun] at fixed
        apply False.elim
        apply notTypeError
        rw [FlatSem.evaluate, flatRun, fixed]
        rcases rejected with rfl | rfl | rfl <;> simpa using failure

/-- Operators whose simulations require only argument evaluation, except
for conversion's explicit nested-expression induction hypotheses. -/
inductive DirectSourceOp : AstHOL.Op → Prop where
  | arith (action : Arith) (typ : PrimType) : DirectSourceOp (.arith action typ)
  | fromTo (a b : PrimType) : DirectSourceOp (.fromTo a b)
  | shift (width : WordSize) (shift : Flapjack.Shift) (amount : Nat) : DirectSourceOp (.shift width shift amount)
  | test (test : Test) (typ : PrimType) : DirectSourceOp (.test test typ)
  | ffi (name : MlString) : DirectSourceOp (.ffi name)
  | allocThunk (mode : ThunkMode) : DirectSourceOp (.thunkOp (.allocThunk mode))
  | updateThunk (mode : ThunkMode) : DirectSourceOp (.thunkOp (.updateThunk mode))
  | opderef : DirectSourceOp .opderef
  | aallocEmpty : DirectSourceOp .aallocEmpty
  | envId : DirectSourceOp .envId
  | equality : DirectSourceOp .equality
  | opref : DirectSourceOp .opref
  | aw8alloc : DirectSourceOp .aw8alloc
  | aw8sub : DirectSourceOp .aw8sub
  | aw8length : DirectSourceOp .aw8length
  | aw8update : DirectSourceOp .aw8update
  | copyStrStr : DirectSourceOp .copyStrStr
  | copyStrAw8 : DirectSourceOp .copyStrAw8
  | copyAw8Str : DirectSourceOp .copyAw8Str
  | copyAw8Aw8 : DirectSourceOp .copyAw8Aw8
  | xorAw8StrUnsafe : DirectSourceOp .xorAw8StrUnsafe
  | implode : DirectSourceOp .implode
  | explode : DirectSourceOp .explode
  | strsub : DirectSourceOp .strsub
  | strlen : DirectSourceOp .strlen
  | strcat : DirectSourceOp .strcat
  | vfromList : DirectSourceOp .vfromList
  | vsub : DirectSourceOp .vsub
  | vlength : DirectSourceOp .vlength
  | aalloc : DirectSourceOp .aalloc
  | aallocFixed : DirectSourceOp .aallocFixed
  | asub : DirectSourceOp .asub
  | alength : DirectSourceOp .alength
  | aupdate : DirectSourceOp .aupdate
  | vsubUnsafe : DirectSourceOp .vsubUnsafe
  | asubUnsafe : DirectSourceOp .asubUnsafe
  | aupdateUnsafe : DirectSourceOp .aupdateUnsafe
  | aw8subUnsafe : DirectSourceOp .aw8subUnsafe
  | aw8updateUnsafe : DirectSourceOp .aw8updateUnsafe
  | listAppend : DirectSourceOp .listAppend
  | configGC : DirectSourceOp .configGC

/-- Every source operator is either covered by the direct dispatcher or is
one of the four cases requiring separate control-flow simulation. -/
theorem directSourceOp_or_special (op : AstHOL.Op) :
    DirectSourceOp op ∨ op = .opapp ∨ op = .opassign ∨ op = .eval ∨
      op = .thunkOp .forceThunk := by
  cases op with
  | arith action typ => exact Or.inl (by constructor)
  | fromTo a b => exact Or.inl (by constructor)
  | shift width shift amount => exact Or.inl (by constructor)
  | equality => exact Or.inl (.equality)
  | test test typ => exact Or.inl (by constructor)
  | opapp => exact Or.inr (by simp)
  | opassign => exact Or.inr (by simp)
  | opref => exact Or.inl (.opref)
  | opderef => exact Or.inl (.opderef)
  | aw8alloc => exact Or.inl (.aw8alloc)
  | aw8sub => exact Or.inl (.aw8sub)
  | aw8length => exact Or.inl (.aw8length)
  | aw8update => exact Or.inl (.aw8update)
  | copyStrStr => exact Or.inl (.copyStrStr)
  | copyStrAw8 => exact Or.inl (.copyStrAw8)
  | copyAw8Str => exact Or.inl (.copyAw8Str)
  | copyAw8Aw8 => exact Or.inl (.copyAw8Aw8)
  | xorAw8StrUnsafe => exact Or.inl (.xorAw8StrUnsafe)
  | implode => exact Or.inl (.implode)
  | explode => exact Or.inl (.explode)
  | strsub => exact Or.inl (.strsub)
  | strlen => exact Or.inl (.strlen)
  | strcat => exact Or.inl (.strcat)
  | vfromList => exact Or.inl (.vfromList)
  | vsub => exact Or.inl (.vsub)
  | vlength => exact Or.inl (.vlength)
  | aalloc => exact Or.inl (.aalloc)
  | aallocEmpty => exact Or.inl (.aallocEmpty)
  | aallocFixed => exact Or.inl (.aallocFixed)
  | asub => exact Or.inl (.asub)
  | alength => exact Or.inl (.alength)
  | aupdate => exact Or.inl (.aupdate)
  | vsubUnsafe => exact Or.inl (.vsubUnsafe)
  | asubUnsafe => exact Or.inl (.asubUnsafe)
  | aupdateUnsafe => exact Or.inl (.aupdateUnsafe)
  | aw8subUnsafe => exact Or.inl (.aw8subUnsafe)
  | aw8updateUnsafe => exact Or.inl (.aw8updateUnsafe)
  | thunkOp op =>
    cases op with
    | forceThunk => exact Or.inr (by simp)
    | allocThunk mode => exact Or.inl (.allocThunk mode)
    | updateThunk mode => exact Or.inl (.updateThunk mode)
  | listAppend => exact Or.inl (.listAppend)
  | configGC => exact Or.inl (.configGC)
  | ffi _ => exact Or.inl (by constructor)
  | eval => exact Or.inr (by simp)
  | envId => exact Or.inl (.envId)

/-- Ordinary source operator compilation preserves the proof-side evaluator
relation, assuming the argument and nested conversion expressions simulate. -/
theorem evaluate_directSourceOp {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : AstHOL.Op) (args : List FlatLang.Exp)
    (direct : DirectSourceOp op)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (charInnerSim : ∀ innerTrace inner,
      args = [.app innerTrace (.src (.fromTo .charT .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (wordInnerSim : ∀ innerTrace inner,
      args = [.app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src op) args] := by
  cases direct with
  | arith action typ => exact evaluate_primitiveArith env names values source target trace action typ args argsSim notTypeError
  | fromTo a b => exact evaluate_primitiveConversion env names values source target trace a b args argsSim charInnerSim wordInnerSim notTypeError
  | shift width shift amount => exact evaluate_wordShift env names values source target trace width shift amount args argsSim notTypeError
  | test test typ => exact evaluate_primitiveTest env names values source target trace test typ args argsSim notTypeError
  | ffi name => exact evaluate_ffi env names values source target trace name args argsSim notTypeError
  | allocThunk mode => exact evaluate_allocThunk env names values source target trace mode args argsSim notTypeError
  | updateThunk mode => exact evaluate_updateThunk env names values source target trace mode args argsSim notTypeError
  | opderef => exact evaluate_rejectedSourceOp env names values source target trace .opderef args (Or.inl rfl) argsSim notTypeError
  | aallocEmpty => exact evaluate_rejectedSourceOp env names values source target trace .aallocEmpty args (Or.inr (Or.inl rfl)) argsSim notTypeError
  | envId => exact evaluate_rejectedSourceOp env names values source target trace .envId args (Or.inr (Or.inr rfl)) argsSim notTypeError
  | equality => exact evaluate_polymorphicEquality env names values source target trace args argsSim notTypeError
  | opref => exact evaluate_ref env names values source target trace args argsSim notTypeError
  | aw8alloc => exact evaluate_allocByteArray env names values source target trace args argsSim notTypeError
  | aw8sub => exact evaluate_checkedByteRead env names values source target trace args argsSim notTypeError
  | aw8length => exact evaluate_byteArrayLength env names values source target trace args argsSim notTypeError
  | aw8update => exact evaluate_checkedByteUpdate env names values source target trace args argsSim notTypeError
  | copyStrStr => exact evaluate_copyString env names values source target trace args argsSim notTypeError
  | copyStrAw8 => exact evaluate_copyStringToByteArray env names values source target trace args argsSim notTypeError
  | copyAw8Str => exact evaluate_copyByteArray env names values source target trace args argsSim notTypeError
  | copyAw8Aw8 => exact evaluate_copyByteArrayToByteArray env names values source target trace args argsSim notTypeError
  | xorAw8StrUnsafe => exact evaluate_xorByteArray env names values source target trace args argsSim notTypeError
  | implode => exact evaluate_stringImplode env names values source target trace args argsSim notTypeError
  | explode => exact evaluate_stringExplode env names values source target trace args argsSim notTypeError
  | strsub => exact evaluate_checkedStringRead env names values source target trace args argsSim notTypeError
  | strlen => exact evaluate_stringLength env names values source target trace args argsSim notTypeError
  | strcat => exact evaluate_stringConcat env names values source target trace args argsSim notTypeError
  | vfromList => exact evaluate_vectorFromList env names values source target trace args argsSim notTypeError
  | vsub => exact evaluate_checkedVectorRead env names values source target trace args argsSim notTypeError
  | vlength => exact evaluate_vectorLength env names values source target trace args argsSim notTypeError
  | aalloc => exact evaluate_allocArray env names values source target trace args argsSim notTypeError
  | aallocFixed => exact evaluate_allocFixed env names values source target trace args argsSim notTypeError
  | asub => exact evaluate_checkedArrayRead env names values source target trace args argsSim notTypeError
  | alength => exact evaluate_arrayLength env names values source target trace args argsSim notTypeError
  | aupdate => exact evaluate_checkedArrayUpdate env names values source target trace args argsSim notTypeError
  | vsubUnsafe => exact evaluate_uncheckedVectorRead env names values source target trace args argsSim notTypeError
  | asubUnsafe => exact evaluate_uncheckedArrayRead env names values source target trace args argsSim notTypeError
  | aupdateUnsafe => exact evaluate_uncheckedArrayUpdate env names values source target trace args argsSim notTypeError
  | aw8subUnsafe => exact evaluate_uncheckedByteRead env names values source target trace args argsSim notTypeError
  | aw8updateUnsafe => exact evaluate_uncheckedByteUpdate env names values source target trace args argsSim notTypeError
  | listAppend => exact evaluate_listAppend env names values source target trace args argsSim notTypeError
  | configGC => exact evaluate_configGC env names values source target trace args argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos
