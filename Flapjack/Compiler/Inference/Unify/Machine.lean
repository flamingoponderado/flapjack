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

/-- Original `option_map_itcase`: mapping under an option distributes over the
inference-type case split. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "option_map_itcase"]
theorem optionMapInferCase {α β : Type} (f : β → α) (arg : InferT)
    (x : Nat → Option β) (y : List InferT → Nat → Option β) (z : Nat → Option β) :
    Option.map f (match arg with
      | .varDb n => x n
      | .app l n => y l n
      | .uvar u => z u) =
      match arg with
      | .varDb n => Option.map f (x n)
      | .app l n => Option.map f (y l n)
      | .uvar u => Option.map f (z u) := by
  cases arg with
  | varDb n => rfl
  | app l n => rfl
  | uvar u => rfl

/-- Original `option_map_COND`: mapping under an option distributes over a
Boolean conditional. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "option_map_COND"]
theorem optionMapCond {α β : Type} (f : β → α) (g : Bool) (t e : Option β) :
    Option.map f (if g then t else e) = if g then Option.map f t else Option.map f e := by
  cases g with
  | true => rfl
  | false => rfl

/-- Original `sptree_map_COND`: the sparse-tree map distributes over a Boolean
conditional. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "sptree_map_COND"]
theorem sptMapCond {α β : Type} (f : β → α) (g : Bool) (t e : Spt β) :
    sptMap f (if g then t else e) = if g then sptMap f t else sptMap f e := by
  cases g with
  | true => rfl
  | false => rfl

/-- Original `SOME_COND`: the `some` constructor distributes over a Boolean
conditional. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "SOME_COND"]
theorem someCond {α : Type} (g : Bool) (t e : α) :
    some (if g then t else e) = if g then some t else some e := by
  cases g with
  | true => rfl
  | false => rfl

/-- Original `OPTION_MAP_BIND`: mapping commutes with the option bind. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "OPTION_MAP_BIND"]
theorem optionMapBind {α β γ : Type} (f : β → α) (m : Option γ) (mf : γ → Option β) :
    Option.map f (m.bind mf) = m.bind (fun x => Option.map f (mf x)) := by
  cases m with
  | none => rfl
  | some x => rfl

/-- Original `OPTION_BIND_MAP`: binding a mapped option applies the function
before the continuation. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "OPTION_BIND_MAP"]
theorem optionBindMap {α β γ : Type} (f : γ → β) (m : Option γ) (mf : β → Option α) :
    (Option.map f m).bind mf = m.bind (fun x => mf (f x)) := by
  cases m with
  | none => rfl
  | some x => rfl

/-- Original `term_CASE_encode`: the term case split of an encoded inference
type is the inference-type case split over the encoded components. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "term_CASE_encode"]
theorem termCaseEncode {α : Type} (v : InferT) (vf : Nat → α)
    (pf : Term Atom → Term Atom → α) (cf : Atom → α) :
    (match encodeInferT v with
      | .var n => vf n
      | .pair a b => pf a b
      | .const c => cf c) =
      match v with
      | .varDb n => cf (.dbTag n)
      | .app l n => pf (.const .tappTag) (.pair (.const (.tcTag n)) (encodeInferTs l))
      | .uvar u => vf u := by
  cases v with
  | varDb n => simp [encodeInferT]
  | app l n => simp [encodeInferT]
  | uvar u => simp [encodeInferT]

end Flapjack.Compiler.Inference.Unify
