import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Extract the incremental compilation entry location from the first expression. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The source's choice-based definition is evaluated by its `extract_name_pmatch`
theorem: only a nonnegative integer constant at the head supplies a location.
The singleton constant is retained so that the program remains nonempty. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "extract_name_def"]
def extractName (xs : List ClosLang.Exp) : Nat × List ClosLang.Exp :=
  match xs with
  | (.op _ (.intOp (.const (.ofNat n))) []) :: rest =>
      (n, if rest.isEmpty then xs else rest)
  | _ => (0, xs)

end Flapjack.Compiler.Backend.ClosToBvl
