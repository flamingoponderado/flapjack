import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileLookup

/-! Kernel replay of original lookup probes. Finite observations do not prove
cross-language equivalence. Duplicate identifiers intentionally remain present. -/
namespace Flapjack.Test.WordToStackCompileLookupParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def snapshot (c : AsmConfigExact 64) (later : Bool) : Prop :=
  let bs : AppList (BitVec 64) × Nat := (.append (.list [8]) (.list [2]),5)
  let code : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
    if later then [(8,5,.alloc 0 (.ln,.ln)),(9,5,.alloc 0 (.ln,.ln)),(9,0,.skip)]
    else [(7,5,.alloc 0 (.ln,.ln)),(7,0,.skip)]
  let (_,_,next) := compileProgNative c false (.alloc 0 (.ln,.ln)) 5 4 bs
  let start := if later then next else bs
  let (ps,fs,_) := compileWordToStackNative c false 4 code bs
  let (body,_,finish) := compileProgNative c false (.alloc 0 (.ln,.ln)) 5 4 start
  let key := if later then 9 else 7
  panPropsALookupEq key code = some (5,.alloc 0 (.ln,.ln)) ∧
    panPropsALookupEq key ps = some body ∧
    ((appListAppend finish.1).length,finish.2,finish.2-(appListAppend finish.1).length,fs) =
      (if later then (4,7,3,[2,2,0]) else (3,6,3,[2,0]))

-- lookup_duplicate_first and lookup_later_threaded: actual selected body and bitmap result.
example (c : AsmConfigExact 64) : snapshot c false ∧ snapshot c true := by
  simp +decide [snapshot,compileWordToStackNative,panPropsALookupEq,
    compileProgNative,maxVarHOL,compNative,wLiveNative,
    Flapjack.Compiler.Backend.WordToStack.insertBitmap,
    Flapjack.Compiler.Backend.WordToStack.writeBitmapExact,
    Flapjack.Compiler.Backend.WordToStack.wordListW,
    Flapjack.Compiler.Backend.WordToStack.bitsToWordW,appListAppend,appendAux] <;> decide +kernel

-- lookup_missing
example (c : AsmConfigExact 64) :
    panPropsALookupEq 8 (compileWordToStackNative c false 4
      ([(7,0,.skip)] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (.list [],0)).1 = none := by
  simp +decide [compileWordToStackNative,panPropsALookupEq,compileProgNative,maxVarHOL,compNative]

-- lookup_bool_first
example (c : AsmConfigExact 8) :
    panPropsALookupEq true (compileWordToStackNative c true 4
      [(true,0,.skip),(true,5,.alloc 0 (.ln,.ln))] (.list [8],3)).1 =
      some (compileProgNative c true .skip 0 4 (.list [8],3)).1 := by
  simp only [compileWordToStackNative,panPropsALookupEq,decide_true,ite_true]

end Flapjack.Test.WordToStackCompileLookupParity
