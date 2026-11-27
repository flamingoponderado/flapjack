module

public import Flapjack.Compiler.Inference.Unify.Substitution
public import Flapjack.Compiler.Inference.Unify.ComputationalWf

@[expose] public section

/-! Transfer relations and the walker decrease relation of the source
unification machine, stated over the reviewed first-order term encoding.
These are the machine's prerequisite definitions; the machine functions that
are defined through HOL's unspecified well-founded recursion or `TAILREC`
remain unported. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Original `RKC_def`: the reverse encoding relation from first-order terms to
inference types. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "RKC_def"]
def rkc (rkt : Term Atom) (ct : InferT) : Prop := encodeInferT ct = rkt

/-- Original `substR_def`: an encoded substitution relates to an inference
substitution when it is the term encoding of that sparse tree. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "substR_def"
  (fmap_as_finite_support_relation := [fm])]
def substR (fm : HolFiniteMapExact Nat (Term Atom)) (sp : Spt InferT) : Prop :=
  wfs fm ∧ sptWf sp = true ∧ fm = (sp2fm sp).map2 (fun p => encodeInferT p.2)

/-- Original `sp2fm_map`: converting a mapped sparse tree is composing the
map with the conversion. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "sp2fm_map"]
theorem sp2fm_map {α β : Type} (f : β → α) (sp : Spt β) :
    sp2fm (sptMap f sp) = (sp2fm sp).map2 (fun p => f p.2) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  rw [holFmapAsFiniteSupportResultWitness_sp2fm, HolFiniteMapExact.lookup_map2]
  rw [holFmapAsFiniteSupportResultWitness_sp2fm, sptLookup_sptMap]

/-- Original `option_CASE_MAP`: mapping under an option commutes with its case
split. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "option_CASE_MAP"]
theorem optionCaseMap {α β γ : Type} (f : γ → β) (v : Option γ) (n : α) (sf : β → α) :
    (match Option.map f v with
      | none => n
      | some x => sf x) =
      match v with
      | none => n
      | some x => sf (f x) := by
  cases v with
  | none => rfl
  | some x => rfl

/-- Original `list_CASE_MAP`: mapping under a list commutes with its case
split. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "list_CASE_MAP"]
theorem listCaseMap {α β γ : Type} (f : γ → β) (l : List γ) (n : α)
    (cf : β → List β → α) :
    (match List.map f l with
      | [] => n
      | h :: t => cf h t) =
      match l with
      | [] => n
      | h :: t => cf (f h) (List.map f t) := by
  cases l with
  | nil => rfl
  | cons h t => rfl

end Flapjack.Compiler.Inference.Unify
