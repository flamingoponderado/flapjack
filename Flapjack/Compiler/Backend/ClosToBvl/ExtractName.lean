module

public import Flapjack.Compiler.Backend.ClosLang.Syntax

@[expose] public section

/-! Extract the incremental compilation entry location from the first expression. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Executable entry extraction: only a nonnegative integer constant at the
head supplies a location. `extractNameSource_eq_extractName` establishes
agreement with the source's choice-based definition. -/
def extractName (xs : List ClosLang.Exp) : Nat × List ClosLang.Exp :=
  match xs with
  | (.op _ (.intOp (.const (.ofNat n))) []) :: rest =>
      (n, if rest.isEmpty then xs else rest)
  | _ => (0, xs)

end Flapjack.Compiler.Backend.ClosToBvl
