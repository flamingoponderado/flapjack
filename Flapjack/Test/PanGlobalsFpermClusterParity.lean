import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsFpermClusterParity

open Flapjack

/-! Regression for the source-shaped (Flapjack-specific, untagged) `fperm_name`
    counterparts and the `fperm_decs` cluster
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1622-1711`), exercised
    on the same `foo`/`bar` fixture as `PanGlobalsFpermDecsParity`. -/
def sourceFunction : FunDecl Nat :=
  { name := "foo"
    inline := false
    exported := true
    params := []
    body := .call none "foo" []
    returnShape := .one }

def targetFunction : FunDecl Nat :=
  { name := "bar"
    inline := true
    exported := false
    params := []
    body := .decCall "x" .one "foo" [] .skip
    returnShape := .one }

def declarations : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .function sourceFunction,
    .function targetFunction]


-- The exact HOL port is polymorphic; exercise the generic theorems at `Nat` as
-- well, so the `String` specialization is not mistaken for the HOL original.
theorem fpermNameCancelNatFixture :
    fpermName (α := Nat) 1 2 (fpermName (α := Nat) 1 2 1) = 1 :=
  fpermName_cancel 1 2 1

theorem fpermNameCongNatFixture :
    fpermName (α := Nat) 1 2 3 = fpermName (α := Nat) 1 2 4 ↔
      (3 : Nat) = 4 :=
  fpermName_cong 1 2 3 4

def fpermClusterGuard : Bool :=
  (globalRenameFunctionName "foo" "bar"
      (globalRenameFunctionName "foo" "bar" "foo") == "foo") &&
  (globalRenameFunctionName "foo" "bar" "foo" !=
      globalRenameFunctionName "foo" "bar" "bar") &&
  ((functions (globalRenameDecls "foo" "bar" declarations)).map
      (fun entry => entry.1) == ["bar", "foo"]) &&
  ((functions declarations).map (fun entry => entry.1)).Nodup &&
  ((functions (globalRenameDecls "foo" "bar" declarations)).map
      (fun entry => entry.1)).Nodup

#guard fpermClusterGuard

def runChecks : IO Bool := do
  if fpermClusterGuard then
    IO.println "PASS pan_globals fperm_name/fperm_decs cluster"
    pure true
  else
    IO.println "FAIL pan_globals fperm_name/fperm_decs cluster"
    pure false

end Flapjack.Test.PanGlobalsFpermClusterParity