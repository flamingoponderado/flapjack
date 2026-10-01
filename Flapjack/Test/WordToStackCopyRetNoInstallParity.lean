import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstall

namespace Flapjack.Test.WordToStackCopyRetNoInstallParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- Each full source iff is obtained from the new theorem; negative output is preserved.
example : noInstall (copyRetNative false false (9,0,true) [1,2]
    (.install 0 1 2 3 4 : HolProg 64)) = true ↔
    noInstall (.install 0 1 2 3 4 : HolProg 64) = true := copyRetNoInstall _ _ _ _ _
example : noInstall (copyRetNative false false (9,0,true) [1,2]
    (.install 0 1 2 3 4 : HolProg 64)) = false := by
  have h := copyRetNoInstall false false (9,0,true) [1,2] (.install 0 1 2 3 4 : HolProg 64)
  cases result : noInstall (copyRetNative false false (9,0,true) [1,2] (.install 0 1 2 3 4 : HolProg 64))
  · rfl
  · have impossible := h.mp result
    contradiction
example : noInstall (copyRetNative false false (1,0,false) [1,2] (.skip : HolProg 64)) = true :=
  (copyRetNoInstall _ _ _ _ _).mpr rfl
example : noInstall (copyRetNative false true (1,7,[true,false]) [1,2]
    (.install 0 1 2 3 4 : HolProg 64)) = true ↔
    noInstall (.install 0 1 2 3 4 : HolProg 64) = true := copyRetNoInstall _ _ _ _ _
example : noInstall (copyRetNative true true (0,7,[true,false]) [true,false] (.skip : HolProg 1)) = true :=
  (copyRetNoInstall _ _ _ _ _).mpr rfl
example : noInstall (copyRetNative true false (0,7,true) [true,false]
    (.install 0 1 2 3 4 : HolProg 1)) = true ↔
    noInstall (.install 0 1 2 3 4 : HolProg 1) = true := copyRetNoInstall _ _ _ _ _
example : noInstall (copyRetNative true false (0,7,(none : Option Bool))
    [[],[1,2]] (.call none (.inl 8) (some (.install 0 1 2 3 4,7,5)) : HolProg 1)) = true ↔
    noInstall (.call none (.inl 8) (some (.install 0 1 2 3 4,7,5)) : HolProg 1) = true :=
  copyRetNoInstall _ _ _ _ _
example : noInstall (copyRetNative false true (0,0,([] : List Nat)) ([] : List Nat)
    (.loop (.install 0 1 2 3 4) : HolProg 16)) = true ↔
    noInstall (.loop (.install 0 1 2 3 4) : HolProg 16) = true := copyRetNoInstall _ _ _ _ _
example : noInstall (copyRetNative false true (3,99,()) [1,2]
    (.seq (.inst .skip) .skip : HolProg 16)) = true :=
  (copyRetNoInstall _ _ _ _ _).mpr rfl

-- Full arbitrary non-Nat tail/list carrier application, with no supplied target safety.
example {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (k f : Nat) (tail : γ) (vs : List β) (kont : HolProg width) :
    noInstall (copyRetNative perf b (k,f,tail) vs kont) = true ↔ noInstall kont = true :=
  copyRetNoInstall perf b (k,f,tail) vs kont

end Flapjack.Test.WordToStackCopyRetNoInstallParity
