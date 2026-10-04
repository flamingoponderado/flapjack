import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.MakeCtxtExact
import Flapjack.Misc.Sptree

/-!
# Exact `loop_to_word` `comp_func` / `compile_prog` / `compile` ports

These are the clause-for-clause HOL ports of `comp_func_def`,
`compile_prog_def`, and `compile_def` from
`cakeml/pancake/loop_to_wordScript.sml:164-177`, over the exact
`HolLoopProg`/`Spt` carriers and the exact `compHOL`. They reuse the reviewed
`accVarsHOL`, `toNumSetHOL`, `fromNumSetHOL`, `sptDifference`, `makeCtxtHOL`,
and `compHOL`. Fixed-width production entrypoints call these definitions when
the executable source codec and FFI byte-range guard succeed; executable-only
syntax retains the compatibility implementation.
-/

namespace Flapjack

open Flapjack.LoopToWord

/-- Exact HOL `comp_func_def` (`cakeml/pancake/loop_to_wordScript.sml:164-169`):
`let vs = fromNumSet (difference (acc_vars body LN) (toNumSet params))`;
`let ctxt = make_ctxt 2 (params ++ vs) LN in FST (comp ctxt body (name,2))`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def loopToWordCompFuncHOL {width : Nat} [NeZero width] (name : Nat)
    (params : List Nat) (body : HolLoopProg width) : WordLangProgHOL (BitVec width) :=
  let vs := fromNumSetHOL
    (sptDifference (accVarsHOL body (.ln : Spt Unit)) (toNumSetHOL params))
  let ctxt := makeCtxtHOL 2 (params ++ vs) (.ln : Spt Nat)
  (Flapjack.LoopToWord.compHOL ctxt body (name, 2)).1

/-- Exact HOL `compile_prog_def` (`cakeml/pancake/loop_to_wordScript.sml:171-174`):
`MAP (λ(name, params, body). (name, LENGTH params+1, comp_func name params body)) p`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def loopToWordCompileProgHOL {width : Nat} [NeZero width]
    (code : List (Nat × List Nat × HolLoopProg width)) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  code.map (fun entry =>
    (entry.1, entry.2.1.length + 1,
      loopToWordCompFuncHOL entry.1 entry.2.1 entry.2.2))

/-- Exact HOL `compile_def` (`cakeml/pancake/loop_to_wordScript.sml:176-177`):
`compile p = compile_prog p`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def loopToWordCompileHOL {width : Nat} [NeZero width]
    (code : List (Nat × List Nat × HolLoopProg width)) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  loopToWordCompileProgHOL code

end Flapjack
