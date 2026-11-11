module

public import Flapjack.Pancake.Proofs.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.Proofs.PanGlobals
@[expose] public section

namespace Flapjack.Test.PanGlobalsFpermClusterParity

open Flapjack
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)
open Flapjack.Pancake.PanLang

/-! Regression for the tagged polymorphic `fpermName` and the exact
    `fperm_decs` cluster
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1622-1711`), exercised
    on the same `foo`/`bar` fixture as `PanGlobalsFpermDecsParity`. -/
def sourceFunction : FunDeclHOL 64 :=
  { name := ofString "foo"
    inline := false
    exported := true
    params := []
    body := .call none (ofString "foo") []
    returnShape := .one }

def targetFunction : FunDeclHOL 64 :=
  { name := ofString "bar"
    inline := true
    exported := false
    params := []
    body := .decCall (ofString "x") .one (ofString "foo") [] .skip
    returnShape := .one }

def declarations : List (DeclHOL 64) :=
  [.decl .one (ofString "g") (.const 7), .function sourceFunction,
    .function targetFunction]


-- The exact HOL port is polymorphic; exercise the generic theorems at `Nat` as
-- well, so the `MlS` specialization is not mistaken for the HOL original.
theorem fpermNameCancelNatFixture :
    fpermName (α := Nat) 1 2 (fpermName (α := Nat) 1 2 1) = 1 :=
  fpermName_cancel 1 2 1

theorem fpermNameCongNatFixture :
    fpermName (α := Nat) 1 2 3 = fpermName (α := Nat) 1 2 4 ↔
      (3 : Nat) = 4 :=
  fpermName_cong 1 2 3 4

def fpermClusterGuard : Bool :=
  toStringOfBytes (fpermName (ofString "foo") (ofString "bar")
      (fpermName (ofString "foo") (ofString "bar") (ofString "foo"))) == "foo" &&
  toStringOfBytes (fpermName (ofString "foo") (ofString "bar") (ofString "foo")) !=
    toStringOfBytes (fpermName (ofString "foo") (ofString "bar") (ofString "bar")) &&
  ((functionsHOL (fpermDecsHOL (width := 64) (ofString "foo") (ofString "bar")
      declarations)).map (fun entry => toStringOfBytes entry.1)) == ["bar", "foo"] &&
  ((functionsHOL declarations).map (fun entry => toStringOfBytes entry.1)).Nodup &&
  ((functionsHOL (fpermDecsHOL (width := 64) (ofString "foo") (ofString "bar")
      declarations)).map (fun entry => toStringOfBytes entry.1)).Nodup

#guard fpermClusterGuard

def runChecks : IO Bool := do
  if fpermClusterGuard then
    IO.println "PASS pan_globals fperm_name/fperm_decs cluster"
    pure true
  else
    IO.println "FAIL pan_globals fperm_name/fperm_decs cluster"
    pure false

end Flapjack.Test.PanGlobalsFpermClusterParity
