import Flapjack.PrimTypesHOL
import Flapjack.TypeSystemHOL.Declarations

/-! Initial declarative type environment from the CakeML primitive-types
script. The type-environment carrier remains pending full source review. -/
namespace Flapjack.PrimTypesHOL
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.TypeSystemHOL

@[hol "cakeml/semantics/primTypesScript.sml" "prim_tenv_def"]
def primTenv : TypeEnv :=
  let a := ofString "'a"
  let var := SemanticT.var a
  { v := nsEmpty
    c := alistToNs ([(ofString "Bind", ([], [], 3)), (ofString "Chr", ([], [], 3)),
      (ofString "Div", ([], [], 3)), (ofString "Subscript", ([], [], 3)),
      (ofString "False", ([], [], 1)), (ofString "True", ([], [], 1)),
      (ofString "[]", ([a], [], 6)), (ofString "::", ([a], [var, .app [var] 6], 6))].reverse)
    t := alistToNs ([(ofString "array", ([a], .app [var] 0)),
      (ofString "bool", ([], .app [] 1)), (ofString "char", ([], .app [] 2)),
      (ofString "double", ([], .app [] 14)), (ofString "exn", ([], .app [] 3)),
      (ofString "int", ([], .app [] 5)), (ofString "list", ([a], .app [var] 6)),
      (ofString "ref", ([a], .app [var] 7)), (ofString "string", ([], .app [] 8)),
      (ofString "unit", ([], .app [] 9)), (ofString "vector", ([a], .app [var] 10)),
      (ofString "word64", ([], .app [] 11)), (ofString "word8", ([], .app [] 12)),
      (ofString "word8array", ([], .app [] 13))].reverse) }

@[hol "cakeml/semantics/primTypesScript.sml" "prim_type_ids_def"]
def primTypeIds : Nat → Prop := fun id => id ∈ 6 :: 1 :: primTypeNums

end Flapjack.PrimTypesHOL
