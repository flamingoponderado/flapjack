import Flapjack.TypeSystemHOL.Declarations

/-! Representative cases captured from the pinned HOL type-system definitions.
The capture is regression evidence, not a cross-language equivalence proof. -/
namespace Flapjack.Test.CakeTypeEnvironmentParity
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString
open Flapjack.NamespaceHOL Flapjack.AstHOL

#guard match deBruijnInc 1 3 (.app [.varDb 0, .varDb 1, .varDb 4] 7) with
  | .app [.varDb 0, .varDb 4, .varDb 7] 7 => true
  | _ => false

#guard match deBruijnSubst 1 [.app [] 5, .varDb 7]
    (.app [.varDb 0, .varDb 1, .varDb 2, .varDb 4] 9) with
  | .app [.varDb 0, .app [] 5, .varDb 7, .varDb 2] 9 => true
  | _ => false

#guard match tveLookup (ofString "x") 0
    (.bindTvar 2 (.bindName (ofString "x") 1 (.app [.varDb 0, .varDb 1] 4) .empty)) with
  | some (1, .app [.varDb 0, .varDb 3] 4) => true
  | _ => false

private def abbreviationEnv : TenvAbbrev := alistToNs
  [(ofString "pair", ([ofString "a", ofString "b"], .app [.var (ofString "a"), .var (ofString "b")] 9)),
   (ofString "dup", ([ofString "a", ofString "a"], .var (ofString "a")))]

#guard match typeNameSubst abbreviationEnv
    (.atapp [.atvar (ofString "x"), .atvar (ofString "y")] (.short (ofString "pair"))) with
  | .app [.var x, .var y] 9 => x == ofString "x" && y == ofString "y"
  | _ => false

#guard match typeNameSubst abbreviationEnv
    (.atapp [.atvar (ofString "x")] (.short (ofString "missing"))) with
  | .app [.var x] 9 => x == ofString "x"
  | _ => false

#guard match typeNameSubst abbreviationEnv
    (.atapp [.atvar (ofString "x"), .atvar (ofString "y")] (.short (ofString "dup"))) with
  | .var x => x == ofString "x"
  | _ => false

private def emptyTypeEnv : TypeEnv := ⟨nsEmpty, nsEmpty, nsEmpty⟩

example : TypeP 0 emptyTypeEnv (.pvar (ofString "x")) (.app [] 5) [(ofString "x", .app [] 5)] :=
  .var 0 emptyTypeEnv (ofString "x") (.app [] 5) (by simp [checkFreevars, checkFreevarsList])

example : TypePs 0 emptyTypeEnv [.pvar (ofString "x"), .pvar (ofString "y")]
    [.app [] 5, .app [] 1] [(ofString "y", .app [] 1), (ofString "x", .app [] 5)] := by
  exact .cons 0 emptyTypeEnv _ _ _ _ _ _
    (.var 0 emptyTypeEnv (ofString "x") (.app [] 5) (by simp [checkFreevars, checkFreevarsList]))
    (.cons 0 emptyTypeEnv _ _ _ _ _ _
      (.var 0 emptyTypeEnv (ofString "y") (.app [] 1) (by simp [checkFreevars, checkFreevarsList])) (.nil 0 emptyTypeEnv))

example : typeOp (.arith .add .intT) [.app [] 5, .app [] 5] (.app [] 5) := by
  simp [typeOp, typeOf, supportedArith]

example : ¬ typeOp (.arith .add .intT) [.app [] 5] (.app [] 5) := by
  simp [typeOp, typeOf, supportedArith]

example : typeOp .aallocEmpty [.app [] 9] (.app [.app [] 5] 0) := by
  exact ⟨rfl, ⟨.app [] 5, rfl⟩⟩

example : ¬ typeOp .aw8subUnsafe [.app [] 13, .app [] 5] (.app [] 12) := by
  simp [typeOp]

example : TypeE emptyTypeEnv .empty (.lit (.intLit 3)) (.app [] 5) :=
  .intLit emptyTypeEnv .empty 3

#guard isValue (.con none [.lit (.intLit 1), .lit (.intLit 2)])
#guard !isValue (.app .opapp [.lit (.intLit 1), .lit (.intLit 2)])

example : checkCtorTenv nsEmpty [([], ofString "t", [(ofString "A", []), (ofString "B", [])])] := by
  simp [checkCtorTenv, Flapjack.SemanticPrimitivesHOL.checkDupCtors, ofString]

example : ¬ checkCtorTenv nsEmpty [([], ofString "t", [(ofString "A", []), (ofString "A", [])])] := by
  simp [checkCtorTenv, Flapjack.SemanticPrimitivesHOL.checkDupCtors]

example : TypeD false emptyTypeEnv
    (.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 3)))
    (fun _ => False) ⟨alistToNs [(ofString "x", (0, .app [] 5))], nsEmpty, nsEmpty⟩ := by
  apply TypeD.value false 0 emptyTypeEnv (.pvar (ofString "x")) (.lit (.intLit 3))
    (.app [] 5) [(ofString "x", .app [] 5)] Flapjack.Misc.Location.unknownLoc
  · simp [isValue]
  · simp [patBindings]
  · exact .var 0 emptyTypeEnv (ofString "x") (.app [] 5) (by simp [checkFreevars, checkFreevarsList])
  · simpa [bindTvar] using TypeE.intLit emptyTypeEnv .empty 3
  · simp

end Flapjack.Test.CakeTypeEnvironmentParity
