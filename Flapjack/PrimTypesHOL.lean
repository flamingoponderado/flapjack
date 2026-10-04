import Flapjack.AstHOL.Syntax

/-!
# `primTypesScript`: the primitive-types program

Counterpart of `cakeml/semantics/primTypesScript.sml`'s `prim_types_program_def`
(lines 12-22), the declarations in scope before any CakeML program: the
exceptions `Bind`, `Chr`, `Div`, `Subscript` and the datatypes `bool` and
`'a list`. HOL's mlstring literal `«s»` is `MlString.ofString "s"` (ASCII, so the
byte list is exactly HOL's `implode`d character list), `unknown_loc` is
`Misc.Location.unknownLoc` and `Short` is `NamespaceHOL.Ident.short`.
-/

namespace Flapjack.PrimTypesHOL

open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Misc.Location
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `prim_types_program_def` (`primTypesScript.sml:12-22`). -/
@[hol "cakeml/semantics/primTypesScript.sml" "prim_types_program_def"]
def primTypesProgram : List Dec :=
  [.dexn unknownLoc (ofString "Bind") [],
   .dexn unknownLoc (ofString "Chr") [],
   .dexn unknownLoc (ofString "Div") [],
   .dexn unknownLoc (ofString "Subscript") [],
   .dtype unknownLoc [([], ofString "bool",
     [(ofString "False", []), (ofString "True", [])])],
   .dtype unknownLoc
     [([ofString "'a"], ofString "list",
       [(ofString "[]", []),
        (ofString "::", [.atvar (ofString "'a"),
          .atapp [.atvar (ofString "'a")] (.short (ofString "list"))])])]]

end Flapjack.PrimTypesHOL
