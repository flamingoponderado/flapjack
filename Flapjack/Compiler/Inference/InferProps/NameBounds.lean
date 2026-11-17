module

public import Flapjack.Compiler.Inference.InferProps.SubstBounds

@[expose] public section

/-! Identifier bounds for source type-name substitution. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL
  Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

/-- Flapjack lookup infrastructure for the source ZIP substitution argument. -/
private theorem lookupZipBound (names : List MlString) (types : List SemanticT) (tids : Nat → Prop)
    (all : ∀ id, setTidsList types id → tids id) :
    ∀ key value, (typeSubstMap (names.zip types)).lookup key = some value → setTidsSubset tids value := by
  intro key value found
  rw [lookupTypeSubstMap] at found
  induction names generalizing types with
  | nil => simp at found
  | cons name names ih =>
    cases types with
    | nil => simp at found
    | cons ty types =>
      simp only [List.zip_cons_cons, List.lookup] at found
      split at found
      · cases found
        intro id member
        exact all id (by simp [setTidsList, member])
      · apply ih types ?_ found
        intro id member
        exact all id (by simp [setTidsList, member])

mutual
/-- Resolving any source type preserves an environment identifier bound. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "set_tids_subset_type_name_subst"]
theorem setTidsSubsetTypeNameSubst (env : TenvAbbrev) (t : AstT) (tids : Nat → Prop) :
    primTids true tids ∧ nsAll (fun _ entry => setTidsSubset tids entry.2) env →
      setTidsSubset tids (typeNameSubst env t) := by
  rintro ⟨prim, all⟩ id member
  have tup : tids TtupNum := (prim TtupNum (by simp [primTypeNums])).2 rfl
  have fn : tids TfnNum := (prim TfnNum (by simp [primTypeNums])).2 rfl
  cases t with
  | atvar name => simp [typeNameSubst, setTids] at member
  | attup ts =>
    simp only [typeNameSubst, Ttup, setTids] at member
    rcases member with same | nested
    · simpa [same] using tup
    · exact nameListBound env ts tids prim all id nested
  | atfun left right =>
    simp only [typeNameSubst, Tfn, setTids, setTidsList] at member
    rcases member with same | l | r | impossible
    · simpa [same] using fn
    · exact setTidsSubsetTypeNameSubst env left tids ⟨prim, all⟩ id l
    · exact setTidsSubsetTypeNameSubst env right tids ⟨prim, all⟩ id r
    · contradiction
  | atapp ts name =>
    have args := nameListBound env ts tids prim all
    cases found : nsLookup env name with
    | none =>
      simp only [typeNameSubst, found, Ttup, setTids] at member
      rcases member with same | nested
      · simpa [same] using tup
      · exact args id nested
    | some entry =>
      rcases entry with ⟨names, body⟩
      have bodyBound : setTidsSubset tids body := all name (names, body) found
      have mapBound := lookupZipBound names (typeNameSubstList env ts) tids args
      have := setTidsSubsetTypeSubst (typeSubstMap (names.zip (typeNameSubstList env ts))) body tids
        ⟨mapBound, bodyBound⟩
      exact this id (by simpa [typeNameSubst, found] using member)
termination_by sizeOf t

/-- List traversal for the source type-name substitution bound induction. -/
private theorem nameListBound (env : TenvAbbrev) (ts : List AstT) (tids : Nat → Prop)
    (prim : primTids true tids) (all : nsAll (fun _ entry => setTidsSubset tids entry.2) env) :
    ∀ id, setTidsList (typeNameSubstList env ts) id → tids id := by
  cases ts with
  | nil => simp [typeNameSubstList, setTidsList]
  | cons t ts =>
    intro id member
    simp only [typeNameSubstList, setTidsList] at member
    rcases member with head | tail
    · exact setTidsSubsetTypeNameSubst env t tids ⟨prim, all⟩ id head
    · exact nameListBound env ts tids prim all id tail
termination_by sizeOf ts
end

end Flapjack.Compiler.Inference.InferProps
