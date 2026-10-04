import Flapjack.HolRef

/-! Primary counterpart of the source namespace script. The association-list
alias and recursively nested namespace carrier preserve list order and repeated
keys. The identifier datatype and every namespace operation of the script follow
(lines 14-117); HOL `ALOOKUP` is `List.lookup` with decidable key equality and a
HOL set is its membership predicate. -/
namespace Flapjack.NamespaceHOL

/-- Literal source association-list abbreviation. -/
@[hol "cakeml/semantics/namespaceScript.sml" "alist"]
abbrev Alist (Key Value : Type) := List (Key × Value)

/-- Complete original namespace carrier, with independent module-name,
identifier-name and value types. Both payloads remain association lists. -/
@[hol "cakeml/semantics/namespaceScript.sml" "namespace"]
inductive Namespace (ModuleName Name Value : Type) where
  | bind : List (Name × Value) → List (ModuleName × Namespace ModuleName Name Value) →
      Namespace ModuleName Name Value

/-- Complete original identifier carrier `id = Short 'n | Long 'm id`, with
independent module-name and name types. -/
@[hol "cakeml/semantics/namespaceScript.sml" "id"]
inductive Ident (ModuleName Name : Type) where
  | short : Name → Ident ModuleName Name
  | long : ModuleName → Ident ModuleName Name → Ident ModuleName Name
  deriving DecidableEq, Repr

/-- Exact HOL `mk_id_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "mk_id_def"]
def mkId {ModuleName Name : Type} : List ModuleName → Name → Ident ModuleName Name
  | [], n => .short n
  | mn :: mns, n => .long mn (mkId mns n)

/-- Exact HOL `id_to_n_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "id_to_n_def"]
def idToN {ModuleName Name : Type} : Ident ModuleName Name → Name
  | .short n => n
  | .long _ id => idToN id

/-- Exact HOL `id_to_mods_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "id_to_mods_def"]
def idToMods {ModuleName Name : Type} : Ident ModuleName Name → List ModuleName
  | .short _ => []
  | .long mn id => mn :: idToMods id

/-- Exact HOL `nsLookup_def`; `ALOOKUP` is `List.lookup` with decidable key
equality (HOL equality). Recursion is on the identifier, as in HOL. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsLookup_def"]
def nsLookup {ModuleName Name Value : Type} [DecidableEq ModuleName] [DecidableEq Name] :
    Namespace ModuleName Name Value → Ident ModuleName Name → Option Value
  | .bind v _, .short n => v.lookup n
  | .bind _ m, .long mn id =>
      match m.lookup mn with
      | none => none
      | some env => nsLookup env id

/-- Exact HOL `nsLookupMod_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsLookupMod_def"]
def nsLookupMod {ModuleName Name Value : Type} [DecidableEq ModuleName] :
    Namespace ModuleName Name Value → List ModuleName → Option (Namespace ModuleName Name Value)
  | e, [] => some e
  | .bind _ m, mn :: path =>
      match m.lookup mn with
      | none => none
      | some env => nsLookupMod env path

/-- Exact HOL `nsEmpty_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsEmpty_def"]
def nsEmpty {ModuleName Name Value : Type} : Namespace ModuleName Name Value :=
  .bind [] []

/-- Exact HOL `nsAppend_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsAppend_def"]
def nsAppend {ModuleName Name Value : Type} :
    Namespace ModuleName Name Value → Namespace ModuleName Name Value →
      Namespace ModuleName Name Value
  | .bind v1 m1, .bind v2 m2 => .bind (v1 ++ v2) (m1 ++ m2)

/-- Exact HOL `nsLift_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsLift_def"]
def nsLift {ModuleName Name Value : Type} (mn : ModuleName)
    (env : Namespace ModuleName Name Value) : Namespace ModuleName Name Value :=
  .bind [] [(mn, env)]

/-- Exact HOL `alist_to_ns_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "alist_to_ns_def"]
def alistToNs {ModuleName Name Value : Type} (a : Alist Name Value) :
    Namespace ModuleName Name Value :=
  .bind a []

/-- Exact HOL `nsBind_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsBind_def"]
def nsBind {ModuleName Name Value : Type} (k : Name) (x : Value) :
    Namespace ModuleName Name Value → Namespace ModuleName Name Value
  | .bind v m => .bind ((k, x) :: v) m

/-- Exact HOL `nsBindList_def`: `FOLDR (λ(x,v) e. nsBind x v e) e l`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsBindList_def"]
def nsBindList {ModuleName Name Value : Type} (l : List (Name × Value))
    (e : Namespace ModuleName Name Value) : Namespace ModuleName Name Value :=
  l.foldr (fun p e => nsBind p.1 p.2 e) e

/-- Exact HOL `nsOptBind_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsOptBind_def"]
def nsOptBind {ModuleName Name Value : Type} (n : Option Name) (x : Value)
    (env : Namespace ModuleName Name Value) : Namespace ModuleName Name Value :=
  match n with
  | none => env
  | some n => nsBind n x env

/-- Exact HOL `nsSing_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsSing_def"]
def nsSing {ModuleName Name Value : Type} (n : Name) (x : Value) :
    Namespace ModuleName Name Value :=
  .bind [(n, x)] []

/-- Exact HOL `nsSub_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsSub_def"]
def nsSub {ModuleName Name Value1 Value2 : Type} [DecidableEq ModuleName] [DecidableEq Name]
    (r : Ident ModuleName Name → Value1 → Value2 → Prop)
    (env1 : Namespace ModuleName Name Value1) (env2 : Namespace ModuleName Name Value2) : Prop :=
  (∀ id v1, nsLookup env1 id = some v1 → ∃ v2, nsLookup env2 id = some v2 ∧ r id v1 v2) ∧
    ∀ path, nsLookupMod env2 path = none → nsLookupMod env1 path = none

/-- Exact HOL `nsAll_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsAll_def"]
def nsAll {ModuleName Name Value : Type} [DecidableEq ModuleName] [DecidableEq Name]
    (f : Ident ModuleName Name → Value → Prop) (env : Namespace ModuleName Name Value) : Prop :=
  ∀ id v, nsLookup env id = some v → f id v

/-- Exact HOL `nsAll2_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsAll2_def"]
def nsAll2 {ModuleName Name Value1 Value2 : Type} [DecidableEq ModuleName] [DecidableEq Name]
    (r : Ident ModuleName Name → Value1 → Value2 → Prop)
    (env1 : Namespace ModuleName Name Value1) (env2 : Namespace ModuleName Name Value2) : Prop :=
  nsSub r env1 env2 ∧ nsSub (fun x y z => r x z y) env2 env1

/-- Exact HOL `nsDom_def`; the HOL set is its membership predicate. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsDom_def"]
def nsDom {ModuleName Name Value : Type} [DecidableEq ModuleName] [DecidableEq Name]
    (env : Namespace ModuleName Name Value) : Ident ModuleName Name → Prop :=
  fun n => ∃ v, nsLookup env n = some v

/-- Exact HOL `nsDomMod_def`; the HOL set is its membership predicate. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsDomMod_def"]
def nsDomMod {ModuleName Name Value : Type} [DecidableEq ModuleName]
    (env : Namespace ModuleName Name Value) : List ModuleName → Prop :=
  fun n => ∃ v, nsLookupMod env n = some v

/-- Exact HOL `nsMap_def`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsMap_def"]
def nsMap {ModuleName Name Value Value' : Type} (f : Value → Value') :
    Namespace ModuleName Name Value → Namespace ModuleName Name Value'
  | .bind v m => .bind (v.map fun p => (p.1, f p.2)) (m.map fun p => (p.1, nsMap f p.2))
decreasing_by
  rename_i h
  have := List.sizeOf_lt_of_mem h
  obtain ⟨mn, e⟩ := p
  simp only [Prod.mk.sizeOf_spec, Namespace.bind.sizeOf_spec] at this ⊢
  omega

end Flapjack.NamespaceHOL
