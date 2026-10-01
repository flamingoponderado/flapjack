import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCallCore

/-! Identical-input original helper predicate regressions, not cross-language
agreement or instrumentation evaluation correctness. -/
namespace Flapjack.Test.WordToStackNoShmemopCallCoreParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- cc_ret_zero
example : noShmemop (copyRetAuxNative 0 0 0 : HolProg 64) = true := rfl

-- cc_ret_one
example : noShmemop (copyRetAuxNative 2 3 1 : HolProg 64) = true := rfl

-- cc_ret_many
example : noShmemop (copyRetAuxNative 7 999 4 : HolProg 32) = true := rfl

-- cc_ret_width1
example : noShmemop (copyRetAuxNative 999 0 5 : HolProg 1) = true := rfl

-- cc_prefix_1
example : noShmemop (perfCallPrefixNative 999 7 0 : HolProg 1) = true := rfl

-- cc_suffix_1
example : noShmemop (perfCallSuffixNative : HolProg 1) = true := rfl

-- cc_prefix_32
example : noShmemop (perfCallPrefixNative 999 7 0 : HolProg 32) = true := rfl

-- cc_suffix_32
example : noShmemop (perfCallSuffixNative : HolProg 32) = true := rfl

-- cc_prefix_64
example : noShmemop (perfCallPrefixNative 999 7 0 : HolProg 64) = true := rfl

-- cc_suffix_64
example : noShmemop (perfCallSuffixNative : HolProg 64) = true := rfl

-- cc_prefix_80
example : noShmemop (perfCallPrefixNative 999 7 0 : HolProg 80) = true := rfl

-- cc_suffix_80
example : noShmemop (perfCallSuffixNative : HolProg 80) = true := rfl

-- Full public theorem applications have no additional safety/bounds premise.
example {width : Nat} [NeZero width] (k f n : Nat) :
    noShmemop (copyRetAuxNative k f n : HolProg width) = true :=
  copyRetAuxNoShmemop k f n

example {width : Nat} [NeZero width] (l1 l2 k : Nat) :
    noShmemop (perfCallPrefixNative l1 l2 k : HolProg width) = true :=
  perfCallPrefixNoShmemop l1 l2 k

example {width : Nat} [NeZero width] :
    noShmemop (perfCallSuffixNative : HolProg width) = true :=
  perfCallSuffixNoShmemop

end Flapjack.Test.WordToStackNoShmemopCallCoreParity
