import Flapjack.Compiler.Backend.StackRemove

namespace Flapjack.Test.StackRemoveWordSelector
open Flapjack Flapjack.Compiler.Backend.StackRemove

example {width : Nat} [NeZero width] (value : BitVec width) :
    theSomeWord (some (.word value)) = value := rfl
example {width : Nat} [NeZero width] :
    theSomeWord (width := width) none = holArb (BitVec width) := rfl
example {width : Nat} [NeZero width] (label offset : Nat) :
    theSomeWord (width := width) (some (.loc label offset)) = holArb (BitVec width) := rfl
example {width : Nat} [NeZero width] (label offset : Nat) :
    theSomeWord (width := width) (some (.loc label offset)) = theSomeWord (width := width) none := rfl
example {width : Nat} [NeZero width] (a b c d : Nat) :
    theSomeWord (width := width) (some (.loc a b)) =
      theSomeWord (width := width) (some (.loc c d)) := rfl
example : theSomeWord (some (.word (255 : BitVec 8))) = 255 := rfl
example : theSomeWord (some (.word (1 : BitVec 1))) = 1 := rfl
example : theSomeWord (some (.word (0 : BitVec 64))) = 0 := rfl
example : theSomeWord (some (.word (2^79 : BitVec 80))) = 2^79 := rfl

end Flapjack.Test.StackRemoveWordSelector
