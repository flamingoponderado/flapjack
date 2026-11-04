import Flapjack.Compiler.Backend.ConfigDecidableEq
import Flapjack.Compiler.Backend.Arm8Config.BackendConfig
import Flapjack.RiscV.NativeSource

/-! Regression for issue #1226: `Backend.Config`, its nested pass configurations
and the complete compiler artifact type have computable `DecidableEq`
instances, so a concrete compilation result can be compared whole, metadata
included. -/
namespace Flapjack.Test.BackendConfigDecidableEq

open Flapjack.Compiler.Backend

/-- The artifact type returned by `compileProgAsmFast`. -/
example : DecidableEq (Option (List (BitVec 8) × List (BitVec 64) × Backend.Config)) :=
  inferInstance

private def config : Backend.Config := Arm8Config.arm8BackendConfigExecutable

/-- A closure expression exercising every nested carrier of `ClosLang.Exp`. -/
private def closExp : ClosLang.Exp :=
  .letrec [Flapjack.Basis.Pure.MlString.ofString "f"] (some 1) (some [2])
    [(1, .op .none (.blockOp (.constant (.constCons 0 [.constInt 3]))) [.var .none 0])]
    (.app .none none (.var .none 1) [])

/-- A known-closure configuration whose approximation map nests `ValApprox`. -/
private def knownWithApprox : ClosKnown.Config :=
  ⟨0, 0, 0, .ls (.tuple 0 [.clos 1 2 closExp 3, .other])⟩

/-- Equal and unequal configurations, the unequal ones differing only in a
deeply nested field (closure inline map, BVL/BVI inline expressions, the source
namespace, the word-to-word colouring oracle and the exported names). -/
private def configChecks : List (String × Bool) :=
  [ ("config equals itself", decide (config = config)),
    ("closure expression equals itself", decide (closExp = closExp)),
    ("same-constructor closure expressions with different nested payload differ",
      !decide (closExp = .letrec [Flapjack.Basis.Pure.MlString.ofString "f"] (some 1) (some [2])
        [(1, .op .none (.blockOp (.constant (.constCons 0 [.constInt 4]))) [.var .none 0])]
        (.app .none none (.var .none 1) []))),
    ("same-constructor BVI calls with different optional handler differ",
      !decide ((Bvi.Exp.call 0 none [] (some (.var 0))) = .call 0 none [] (some (.var 1)))),
    ("same-constructor BVL lets with different list length differ",
      !decide ((Bvl.Exp.«let» [.var 0] (.var 1)) = .«let» [.var 0, .var 0] (.var 1))),
    ("same-constructor approximations with different nested tuple differ",
      !decide ((ClosKnown.ValApprox.tuple 0 [.other]) = .tuple 0 [.impossible])),
    ("same-constructor namespaces with different nested module differ",
      !decide ((NamespaceHOL.Namespace.bind ([] : List (Nat × Nat))
          [(0, .bind [(1, 2)] [])]) = .bind [] [(0, .bind [(1, 3)] [])])),
    ("closure call state differs",
      !decide (config = { config with
        closConf := { config.closConf with callState := (.ln, [(0, (1, closExp))]) } })),
    ("known-closure approximation differs",
      !decide (config = { config with
        closConf := { config.closConf with
          knownConf := some knownWithApprox } })),
    ("BVL inline map differs",
      !decide (config = { config with
        bvlConf := { config.bvlConf with
          inlines := .ls (1, .call 0 none [.op (.label 2) [.var 0]]) } })),
    ("BVI inline map differs",
      !decide (config = { config with
        bvlConf := { config.bvlConf with
          bviInlines := .ls (1, .call 0 none [] (some (.«return» [.var 0]))) } })),
    ("source namespace differs",
      !decide (config = { config with
        sourceConf := { config.sourceConf with
          modEnv := { config.sourceConf.modEnv with
            v := .bind [] [(Flapjack.Basis.Pure.MlString.ofString "M", .bind [] [])] } } })),
    ("colouring oracle differs",
      !decide (config = { config with
        wordToWordConf := { config.wordToWordConf with colOracle := [none] } })),
    ("exported names differ",
      !decide (config = { config with
        exported := [Flapjack.Basis.Pure.MlString.ofString "main"] })) ]

/-- A complete RISC-V compilation result compared whole, including its
`Backend.Config` metadata. -/
private def artifactCheck : Bool :=
  match Parser.parseTopDecs (fun value => BitVec.ofInt 64 value)
      "fun main () { return 7; }" with
  | .error _ => false
  | .ok declarations =>
      let artifact := RiscV.NativeSource.compileDeclarations declarations
      artifact.isSome && decide (artifact = artifact)

def runChecks : IO Bool := do
  let mut ok := true
  for (label, passed) in configChecks ++ [("compiled artifact equals itself", artifactCheck)] do
    if passed then
      IO.println s!"PASS backend config DecidableEq: {label}"
    else
      IO.println s!"FAIL backend config DecidableEq: {label}"
      ok := false
  pure ok

end Flapjack.Test.BackendConfigDecidableEq
