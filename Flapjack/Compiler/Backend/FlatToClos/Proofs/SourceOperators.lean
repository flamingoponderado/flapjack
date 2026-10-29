import Flapjack.Compiler.Backend.FlatToClos.Proofs.Ffi
import Flapjack.Compiler.Backend.FlatToClos.Proofs.PrimitiveTests
import Flapjack.Compiler.Backend.FlatToClos.Proofs.PrimitiveArith
import Flapjack.Compiler.Backend.FlatToClos.Proofs.PrimitiveConversions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.WordShifts
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Array
import Flapjack.Compiler.Backend.FlatToClos.Proofs.MemoryExpressions
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EqualityExpressions

/-! Dispatcher for ordinary source operators in the proof-side simulation.
The special application, assignment, dynamic installation, and thunk cases
require additional induction hypotheses. This is not a reviewed HOL port. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Operators whose simulations require only argument evaluation, except
for conversion's explicit nested-expression induction hypotheses. -/
inductive DirectSourceOp : AstHOL.Op → Prop where
  | arith (action : Arith) (typ : PrimType) : DirectSourceOp (.arith action typ)
  | fromTo (a b : PrimType) : DirectSourceOp (.fromTo a b)
  | shift (width : WordSize) (shift : Flapjack.Shift) (amount : Nat) : DirectSourceOp (.shift width shift amount)
  | test (test : Test) (typ : PrimType) : DirectSourceOp (.test test typ)
  | ffi (name : MlString) : DirectSourceOp (.ffi name)
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
