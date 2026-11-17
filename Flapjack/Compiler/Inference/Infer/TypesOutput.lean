module

public import Flapjack.Compiler.Inference.InferT.Display

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Namespace traversal and byte-oriented output for CakeML's `--types` mode. -/
namespace Flapjack.Compiler.Inference.Infer.TypesOutput
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferTDisplay

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
/-- Deduplicate each namespace's value and module bindings. -/
def nsNub {M N V : Type} [DecidableEq M] [DecidableEq N] :
    Namespace M N V → Namespace M N V
  | .bind entries modules => .bind (alistNub entries) (alistNub (innerNsNubs modules))
termination_by env => sizeOf env

/-- Deduplicate nested namespaces before filtering duplicate module names. -/
def innerNsNubs {M N V : Type} [DecidableEq M] [DecidableEq N] :
    List (M × Namespace M N V) → List (M × Namespace M N V)
  | [] => []
  | (name, env) :: rest => (name, nsNub env) :: innerNsNubs rest
termination_by modules => sizeOf modules
end

/-- Source-polymorphic namespace deduplication. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "ns_nub_def"]
noncomputable def nsNubHOL {M N V : Type} (env : Namespace M N V) : Namespace M N V :=
  @nsNub M N V (Classical.typeDecidableEq M) (Classical.typeDecidableEq N) env

/-- Source-polymorphic traversal of nested namespaces. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "ns_nub_def"]
noncomputable def innerNsNubsHOL {M N V : Type} (modules : List (M × Namespace M N V)) :
    List (M × Namespace M N V) :=
  @innerNsNubs M N V (Classical.typeDecidableEq M) (Classical.typeDecidableEq N) modules

/-- The HOL-shaped operation agrees with the executable equality dictionaries. -/
theorem nsNubHOL_eq {M N V : Type} [hm : DecidableEq M] [hn : DecidableEq N]
    (env : Namespace M N V) : nsNubHOL env = nsNub env := by
  unfold nsNubHOL
  have em : Classical.typeDecidableEq M = hm := Subsingleton.elim _ _
  have en : Classical.typeDecidableEq N = hn := Subsingleton.elim _ _
  rw [em, en]

/-- The nested traversal likewise agrees with the executable dictionaries. -/
theorem innerNsNubsHOL_eq {M N V : Type} [hm : DecidableEq M] [hn : DecidableEq N]
    (modules : List (M × Namespace M N V)) : innerNsNubsHOL modules = innerNsNubs modules := by
  unfold innerNsNubsHOL
  have em : Classical.typeDecidableEq M = hm := Subsingleton.elim _ _
  have en : Classical.typeDecidableEq N = hn := Subsingleton.elim _ _
  rw [em, en]

mutual
/-- Flatten namespace bindings in the source type printer's order. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "ns_to_alist_def"]
def nsToAlist {V : Type} : Namespace MlString MlString V → List (MlString × V)
  | .bind entries modules => entries ++ nsToAlistModules modules
termination_by env => sizeOf env

private def nsToAlistModules {V : Type} :
    List (MlString × Namespace MlString MlString V) → List (MlString × V)
  | [] => []
  | (name, env) :: rest =>
    (nsToAlist env).map (fun (child, value) =>
      (MlString.concat [name, ofString ".", child], value)) ++ nsToAlistModules rest
termination_by modules => sizeOf modules
end

/-- Format the value namespace in the order used by the source compiler. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "inf_env_to_types_string_def"]
def infEnvToTypesString (env : Env) : List MlString :=
  let lines := (nsToAlist (nsNub env.infV)).map fun (name, (_, t)) =>
    MlString.concat [name, ofString ": ", inferTypeToString env.infT t, ofString "\n"]
  lines.reverse

/-- Render the final inference environment as raw HOL bytes, including the
source driver's leading and trailing newlines. -/
def render (env : Env) : List HolChar :=
  (MlString.concat ([ofString "\n"] ++ infEnvToTypesString env ++ [ofString "\n"])).explode

end Flapjack.Compiler.Inference.Infer.TypesOutput
