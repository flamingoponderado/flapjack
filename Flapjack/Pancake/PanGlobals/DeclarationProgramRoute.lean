module

public import Flapjack.Pancake.PanGlobals.CallHandlerExact

@[expose] public section

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Complete HOL-observable context correspondence. HOL names are `MlS`, so
the production map is observed at decoded HOL keys. Equality on arbitrary
Unicode String keys would be false: `ofString` truncates character codes to
bytes. This Flapjack cross-carrier relation has no separate HOL original. -/
def GlobalDeclarationContextRel {width : Nat} [NeZero width]
    (production : CakeContext width) (exactContext : PanGlobalsContextExact width) : Prop :=
  production.globalsSize = exactContext.globalsSize ∧
  production.maxGlobalsSize = exactContext.maxGlobalsSize ∧
  ∀ key : MlS,
    production.globals (Flapjack.Basis.Pure.MlString.toStringOfBytes key) =
      (exactContext.globals.lookup key).map (fun value => (shapeOfHOL value.1, value.2))

end Flapjack
