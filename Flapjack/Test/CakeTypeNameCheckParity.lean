module

public import Flapjack.Compiler.Inference.Infer.TypeNameCheck
public import Flapjack.Compiler.Inference.Infer.TypeDefinitions
public meta import Flapjack.Compiler.Inference.Infer.TypeNameCheck
public meta import Flapjack.Compiler.Inference.Infer.TypeDefinitions

@[expose] public section

/-! Replay of original HOL results in env_rel_init_probe.out. -/
namespace Flapjack.Test.CakeTypeNameCheckParity
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Basis.Pure.MlString Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.Infer.TypeNameCheck
  Flapjack.Compiler.Inference.Infer.TypeDefinitions

private def location : LocErrInfo := ⟨none, nsEmpty⟩
private def a : MlString := ofString "a"

#guard match typeNameCheckSubst location id nsEmpty [] (.atvar a) (7 : Nat) with
  | (.failure (none, name), 7) => name == a
  | _ => false

#guard match typeNameCheckSubst location id nsEmpty [a] (.attup [.atvar a, .atvar a]) (7 : Nat) with
  | (.success (.app [.var first, .var second] 9), 7) => first == a && second == a
  | _ => false

#guard match typeNameCheckSubst location id nsEmpty []
    (.atapp [] (.short (ofString "missing"))) (7 : Nat) with
  | (.failure (none, message), 7) => message == ofString "Undefined type constructor: missing"
  | _ => false

#guard match typeNameCheckSubst location id
    (nsBind (ofString "pair") ([ofString "x", ofString "x"], .var (ofString "x")) nsEmpty)
    [a, ofString "b"] (.atapp [.atvar a, .atvar (ofString "b")] (.short (ofString "pair")))
    (7 : Nat) with
  | (.success (.var name), 7) => name == a
  | _ => false

#guard match checkTypeDefinition location nsEmpty
    [([a, a], ofString "t", [(ofString "C", []), (ofString "C", [])])] (7 : Nat) with
  | (.failure (none, message), 7) =>
      message == ofString "Duplicate constructor C in the definition of type t"
  | _ => false

#guard match checkTypeDefinition location nsEmpty
    [([], ofString "t", []), ([], ofString "t", [])] (7 : Nat) with
  | (.failure (none, message), 7) =>
      message == ofString "Duplicate type constructor t in a mutually recursive type definition"
  | _ => false

#guard match checkTypeDefinition location nsEmpty
    [([], ofString "t", [(ofString "C", [.atvar a])])] (7 : Nat) with
  | (.failure (none, message), 7) =>
      message == ofString "Unbound type variable a in type definition with constructor C"
  | _ => false

#guard match typeNameCheckSubst location id
    (nsBind (ofString "pair") ([ofString "x", ofString "y"], .var (ofString "x")) nsEmpty)
    [] (.atapp [] (.short (ofString "pair"))) (7 : Nat) with
  | (.failure (none, message), 7) =>
      message == ofString "Type constructor pair given 0 arguments, but expected 2"
  | _ => false

end Flapjack.Test.CakeTypeNameCheckParity
