import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys

namespace Flapjack.Test.WordToStackCompileKeysParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.WordToStackProofs

/-- Apply the full reviewed output-equation theorem to the actual compiler
result. This local test helper has no separate HOL original. -/
private theorem actualKeys {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (k : Nat)
    (ps : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bm : AppList (BitVec width) × Nat) :
    (compileWordToStackNative conf perf k ps bm).1.map Prod.fst = ps.map Prod.fst :=
  mapFstCompileWordToStack conf perf k ps bm _ _ rfl

example (c : AsmConfigExact 64) :
    (compileWordToStackNative c false 4 ([] : List (Bool × Nat × WordLangProgHOL (BitVec 64)))
      (.list [4],1)).1.map Prod.fst = [] := actualKeys c false 4 [] (.list [4],1)
example {β : Type} (c : AsmConfigExact 64) (i : β) :
    (compileWordToStackNative c false 4 [(i,7,.skip)] (.list [4],1)).1.map Prod.fst = [i] :=
  actualKeys c false 4 _ _
example {β : Type} (c : AsmConfigExact 64) (i j : β) :
    (compileWordToStackNative c false 4 [(i,7,.skip),(j,0,.tick)] (.list [4],1)).1.map Prod.fst = [i,j] :=
  actualKeys c false 4 _ _
example (c : AsmConfigExact 64) :
    (compileWordToStackNative c true 4 [(true,7,.skip),(true,0,.tick)] (.list [4],1)).1.map Prod.fst = [true,true] :=
  actualKeys c true 4 _ _
example (c : AsmConfigExact 64) :
    (compileWordToStackNative c false 4 [(9,0,.skip),(2,5,.tick),(9,7,.skip)] (.list [4],1)).1.map Prod.fst = [9,2,9] :=
  actualKeys c false 4 _ _
example (c : AsmConfigExact 64) :
    (compileWordToStackNative c false 4 [(1,5,.alloc 0 (.ln,.ln)),(0,7,.alloc 0 (.ln,.ln))]
      (.list [4],1)).1.map Prod.fst = [1,0] := actualKeys c false 4 _ _
example (c : AsmConfigExact 1) :
    (compileWordToStackNative c true 0 [(true,7,.skip),(false,0,.tick),(false,200,.skip)]
      (.list [4],1)).1.map Prod.fst = [true,false,false] := actualKeys c true 0 _ _

end Flapjack.Test.WordToStackCompileKeysParity
