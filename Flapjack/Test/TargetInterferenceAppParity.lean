import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceApp
namespace Flapjack.Test.TargetInterferenceAppParity
open Flapjack.Compiler.Backend.Semantics.TargetProps
example {w : Nat} [NeZero w] {S : Type} (i : Nat) (bs : List (BitVec 8)) (pre post : S) :
    isFfiApp (.ffiApp i bs pre post : InterferenceApp w S) = true := rfl
example {w : Nat} [NeZero w] {S : Type} (a b : BitVec w) (pre post : S) :
    isFfiApp (.ccApp a b pre post) = false := rfl
example {w : Nat} [NeZero w] {S : Type} (i : Nat) (bs : List (BitVec 8)) (pre post : S) :
    appPost (.ffiApp i bs pre post : InterferenceApp w S) = post := rfl
example {w : Nat} [NeZero w] {S : Type} (a b : BitVec w) (pre post : S) :
    appPost (.ccApp a b pre post) = post := rfl
end Flapjack.Test.TargetInterferenceAppParity
