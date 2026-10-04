import Flapjack.HolRef

/-! Primary counterpart of the source namespace script. The association-list
alias and recursively nested namespace carrier preserve list order and repeated
keys. Lookup operations and source-environment construction remain separate. -/
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

/-- HOL `id` (`namespaceScript.sml:14-16`): a short name, or a module-qualified long name.
    HOL's type is `('m,'n) id` (type variables in alphabetical order), so the independent
    `ModuleName Name` parameters come in that order, as for `Namespace`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "id"]
inductive Id (ModuleName Name : Type) where
  | short : Name → Id ModuleName Name
  | long : ModuleName → Id ModuleName Name → Id ModuleName Name
  deriving DecidableEq, Repr

/-- HOL `mk_id_def` (`namespaceScript.sml:18-21`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "mk_id_def"]
def mkId {ModuleName Name : Type} : List ModuleName → Name → Id ModuleName Name
  | [], n => .short n
  | mn :: mns, n => .long mn (mkId mns n)

/-- HOL `nsLookup_def` (`namespaceScript.sml:38-45`); `ALOOKUP` is `List.lookup` with
    decidable key equality. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsLookup_def"]
def nsLookup {ModuleName Name Value : Type} [DecidableEq ModuleName] [DecidableEq Name] :
    Namespace ModuleName Name Value → Id ModuleName Name → Option Value
  | .bind v _, .short n => v.lookup n
  | .bind _ m, .long mn id =>
      match m.lookup mn with
      | none => none
      | some env => nsLookup env id

/-- HOL `nsEmpty_def` (`namespaceScript.sml:53-55`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsEmpty_def"]
def nsEmpty {ModuleName Name Value : Type} : Namespace ModuleName Name Value := .bind [] []

/-- HOL `nsAppend_def` (`namespaceScript.sml:57-59`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsAppend_def"]
def nsAppend {ModuleName Name Value : Type} :
    Namespace ModuleName Name Value → Namespace ModuleName Name Value →
      Namespace ModuleName Name Value
  | .bind v1 m1, .bind v2 m2 => .bind (v1 ++ v2) (m1 ++ m2)

/-- HOL `nsLift_def` (`namespaceScript.sml:61-63`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsLift_def"]
def nsLift {ModuleName Name Value : Type} (mn : ModuleName) (env : Namespace ModuleName Name Value) :
    Namespace ModuleName Name Value :=
  .bind [] [(mn, env)]

/-- HOL `alist_to_ns_def` (`namespaceScript.sml:65-67`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "alist_to_ns_def"]
def alistToNs {ModuleName Name Value : Type} (a : Alist Name Value) :
    Namespace ModuleName Name Value :=
  .bind a []

/-- HOL `nsBind_def` (`namespaceScript.sml:69-71`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsBind_def"]
def nsBind {ModuleName Name Value : Type} (k : Name) (x : Value) :
    Namespace ModuleName Name Value → Namespace ModuleName Name Value
  | .bind v m => .bind ((k, x) :: v) m

/-- HOL `nsBindList_def` (`namespaceScript.sml:73-75`): `FOLDR (λ(x,v) e. nsBind x v e) e l`. -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsBindList_def"]
def nsBindList {ModuleName Name Value : Type} (l : List (Name × Value))
    (e : Namespace ModuleName Name Value) : Namespace ModuleName Name Value :=
  l.foldr (fun xv e => nsBind xv.1 xv.2 e) e

/-- HOL `nsSing_def` (`namespaceScript.sml:81-83`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsSing_def"]
def nsSing {ModuleName Name Value : Type} (n : Name) (x : Value) :
    Namespace ModuleName Name Value :=
  .bind [(n, x)] []

/-- HOL `nsMap_def` (`namespaceScript.sml:113-116`). -/
@[hol "cakeml/semantics/namespaceScript.sml" "nsMap_def"]
def nsMap {ModuleName Name Value Value' : Type} (f : Value → Value') :
    Namespace ModuleName Name Value → Namespace ModuleName Name Value'
  | .bind v m => .bind (v.map (fun nx => (nx.1, f nx.2)))
      (m.attach.map (fun ⟨me, _⟩ => (me.1, nsMap f me.2)))
termination_by ns => sizeOf ns
decreasing_by
  simp_wf
  rename_i h
  have := List.sizeOf_lt_of_mem h
  cases me
  simp at this ⊢
  omega

/-- The literal HOL `nsMap_def` clause, `MAP (λ(mn,e). (mn,nsMap f e)) m` without the `attach`
    used for termination (Flapjack infrastructure). -/
theorem nsMap_bind {ModuleName Name Value Value' : Type} (f : Value → Value')
    (v : List (Name × Value)) (m : List (ModuleName × Namespace ModuleName Name Value)) :
    nsMap f (.bind v m) =
      .bind (v.map (fun nx => (nx.1, f nx.2))) (m.map (fun me => (me.1, nsMap f me.2))) := by
  rw [nsMap]
  congr 1
  simp [List.map_attach_eq_pmap]

end Flapjack.NamespaceHOL
