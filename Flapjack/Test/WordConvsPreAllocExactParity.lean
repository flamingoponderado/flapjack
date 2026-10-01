import Flapjack.Pancake.WordConvs

/-! Kernel replay of the four original pre-allocation rows from
word_convs_alloc_conventions_probe.out, using exact Spt cutsets. -/
namespace Flapjack.Test.WordConvsPreAllocExactParity
open Flapjack.Basis.Pure.MlString in
private def ffiH (a b c d : Nat) (cut : Nat) : WordLangProgHOL (BitVec 8) :=
  .ffi (ofString "f") a b c d (sptInsert cut () .ln, .ln)
-- `pre_ok_ffi=T`
example : preAllocConventionsHOL (ffiH 2 4 6 8 3) = true := by cbv
-- `pre_bad_scalar=F`
example : preAllocConventionsHOL (ffiH 3 4 6 8 3) = false := by cbv
-- `pre_bad_cutset=F`
example : preAllocConventionsHOL (ffiH 2 4 6 8 4) = false := by cbv
-- `pre_bad_argconv=F`
example : preAllocConventionsHOL (ffiH 2 4 6 9 3) = false := by cbv

def runChecks : IO Bool := do
  IO.println "PASS exact pre-allocation convention matches four original HOL rows"
  pure true
end Flapjack.Test.WordConvsPreAllocExactParity
