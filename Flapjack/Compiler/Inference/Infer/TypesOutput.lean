module

public import Flapjack.Compiler.Inference.InferT.Display

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Byte-oriented output for CakeML's `--types` mode. The combined namespace
traversal is Flapjack infrastructure: HOL separately nubs namespaces,
flattens them, and formats the resulting list. Full correspondence remains
pending review. -/
namespace Flapjack.Compiler.Inference.Infer.TypesOutput
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferTDisplay

private abbrev ValEnv := Namespace MlString MlString (Nat × InferT)

/-- Executable deduplication using the key type's decidable equality. -/
def alistNub {α β : Type} [DecidableEq α] : List (α × β) → List (α × β)
  | [] => []
  | (key, value) :: rest =>
    (key, value) :: alistNub (rest.filter (fun entry => key != entry.1))
termination_by entries => entries.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le (fun entry => key != entry.1.1) rest.attach)

/-- Source-polymorphic association-list deduplication. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "alist_nub_def"]
noncomputable def alistNubHOL {α β : Type} (entries : List (α × β)) : List (α × β) :=
  @alistNub α β (Classical.typeDecidableEq α) entries

/-- The executable dictionary and HOL's unrestricted equality give the same result. -/
theorem alistNubHOL_eq {α β : Type} [inst : DecidableEq α] (entries : List (α × β)) :
    alistNubHOL entries = alistNub entries := by
  unfold alistNubHOL
  have same : Classical.typeDecidableEq α = inst := Subsingleton.elim _ _
  rw [same]

mutual
private def flatten : ValEnv → List (MlString × (Nat × InferT))
  | .bind entries modules => alistNub entries ++ flattenModules modules []
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
