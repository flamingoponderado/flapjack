import Flapjack.Compiler.Inference.InferT.Display

/-! Byte-oriented output for CakeML's `--types` mode. The combined traversal
is Flapjack infrastructure: HOL separately nubs namespaces, flattens them,
and formats the resulting list. Full correspondence remains pending review. -/
namespace Flapjack.Compiler.Inference.Infer.TypesOutput
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferTDisplay

private abbrev ValEnv := Namespace MlString MlString (Nat × InferT)

private def values : List (MlString × (Nat × InferT)) → List MlString → List (MlString × (Nat × InferT))
  | [], _ => []
  | (name, value) :: rest, seen =>
    if name ∈ seen then values rest seen else (name, value) :: values rest (name :: seen)

mutual
private def flatten : ValEnv → List (MlString × (Nat × InferT))
  | .bind entries modules => values entries [] ++ flattenModules modules []
termination_by env => sizeOf env

private def flattenModules : List (MlString × ValEnv) → List MlString → List (MlString × (Nat × InferT))
  | [], _ => []
  | (name, env) :: rest, seen =>
    if name ∈ seen then flattenModules rest seen
    else (flatten env).map (fun (child, value) =>
      (MlString.concat [name, ofString ".", child], value)) ++ flattenModules rest (name :: seen)
termination_by modules _ => sizeOf modules
end

/-- Render the final inference environment as raw HOL bytes, including the
source driver's leading and trailing newlines. -/
def render (env : Env) : List HolChar :=
  let lines := (flatten env.infV).map fun (name, (_, t)) =>
    MlString.concat [name, ofString ": ", inferTypeToString env.infT t, ofString "\n"]
  (MlString.concat ([ofString "\n"] ++ lines.reverse ++ [ofString "\n"])).explode

end Flapjack.Compiler.Inference.Infer.TypesOutput
