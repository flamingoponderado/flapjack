module

public import Flapjack.TypeSoundInvariants
public import Flapjack.TypeSysProps.Freevars

@[expose] public section

/-! Well-formed declarative type abbreviations. -/
namespace Flapjack.TypeSysProps
open Flapjack Flapjack.AstHOL Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.TypeSoundInvariants

noncomputable local instance abbrevClassicalDecidableEq (α : Type) : DecidableEq α :=
  Classical.typeDecidableEq α

/-- Looking up a well-formed abbreviation yields a type whose free variables
are among its declared parameters. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_abbrev_ok_lookup"]
theorem tenvAbbrevOkLookup {M N : Type}
    (env : Namespace M N (List MlString × SemanticT)) (name : Ident M N)
    (tvs : List MlString) (t : SemanticT) :
    tenvAbbrevOk env ∧ nsLookup env name = some (tvs, t) →
      checkFreevars 0 tvs t = true := by
  rintro ⟨wellFormed, found⟩
  exact wellFormed name (tvs, t) found

/-- The recursive list check agrees with HOL's `EVERY`. This Flapjack
infrastructure is shared by the type-name and pattern proofs. -/
theorem checkFreevarsListEqAll (dbmax : Nat) (tvs : List MlString) (ts : List SemanticT) :
    checkFreevarsList dbmax tvs ts = ts.all (checkFreevars dbmax tvs) := by
  induction ts with
  | nil => simp [checkFreevarsList]
  | cons t rest ih => simp [checkFreevarsList, ih]

/-- Source type-name resolution preserves list length; HOL simplifies this
recursive traversal inline. -/
private theorem typeNamesLength (env : TenvAbbrev) (ts : List AstT) :
    (typeNameSubstList env ts).length = ts.length := by
  induction ts with
  | nil => simp [typeNameSubstList]
  | cons t rest ih => simp [typeNameSubstList, ih]

mutual
/-- Resolving a well-formed source type preserves its free-variable bounds. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_type_name_subst"]
theorem checkFreevarsTypeNameSubst (tvs : List MlString) (t : AstT) (dbmax : Nat) (env : TenvAbbrev) :
    tenvAbbrevOk env ∧ checkTypeNames env t = true ∧ checkFreevarsAst tvs t = true →
    checkFreevars dbmax tvs (typeNameSubst env t) = true := by
  rintro ⟨wellFormed, names, free⟩
  cases t with
  | atvar name => simpa [typeNameSubst, checkFreevars, checkFreevarsAst] using free
  | attup ts =>
    simp only [checkTypeNames] at names
    simp only [checkFreevarsAst] at free
    simp only [typeNameSubst, Ttup, checkFreevars]
    exact typeNamesFreevars tvs ts dbmax env ⟨wellFormed, names, free⟩
  | atfun left right =>
    simp only [checkTypeNames, Bool.and_eq_true] at names
    simp only [checkFreevarsAst, Bool.and_eq_true] at free
    simp only [typeNameSubst, Tfn, checkFreevars, checkFreevarsList, Bool.and_eq_true]
    exact ⟨checkFreevarsTypeNameSubst tvs left dbmax env ⟨wellFormed, names.1, free.1⟩,
      checkFreevarsTypeNameSubst tvs right dbmax env ⟨wellFormed, names.2, free.2⟩, trivial⟩
  | atapp args name =>
    simp only [checkTypeNames, Bool.and_eq_true] at names
    simp only [checkFreevarsAst] at free
    have argsFree := typeNamesFreevars tvs args dbmax env ⟨wellFormed, names.2, free⟩
    simp only [typeNameSubst]
    cases found : nsLookup env name with
    | none => simp [found] at names
    | some entry =>
      rcases entry with ⟨params, body⟩
      have lengths : params.length = (typeNameSubstList env args).length := by
        rw [typeNamesLength]
        simpa [found] using names.1
      have bodyFree : checkFreevars 0 params body = true := by
        have decEq : Classical.typeDecidableEq MlString = inferInstanceAs (DecidableEq MlString) :=
          Subsingleton.elim _ _
        rw [← decEq] at found
        exact tenvAbbrevOkLookup env name params body ⟨wellFormed, found⟩
      have lifted := checkFreevarsAdd 0 params body bodyFree dbmax (Nat.zero_le _)
      have all : (typeNameSubstList env args).all (checkFreevars dbmax tvs) = true := by
        rw [← checkFreevarsListEqAll]
        exact argsFree
      change checkFreevars dbmax tvs
        (typeSubst (typeSubstMap (params.zip (typeNameSubstList env args))) body) = true
      rw [← alistToFmapEqTypeSubstMap]
      exact checkFreevarsSubstSingle dbmax params body tvs _ ⟨lengths, lifted, all⟩
termination_by sizeOf t

/-- List traversal for the source type-name induction, not a separate HOL
theorem. -/
private theorem typeNamesFreevars (tvs : List MlString) (ts : List AstT) (dbmax : Nat) (env : TenvAbbrev) :
    tenvAbbrevOk env ∧ checkTypeNamesList env ts = true ∧ checkFreevarsAstList tvs ts = true →
    checkFreevarsList dbmax tvs (typeNameSubstList env ts) = true := by
  rintro ⟨wellFormed, names, free⟩
  cases ts with
  | nil => simp [typeNameSubstList, checkFreevarsList]
  | cons t rest =>
    simp only [checkTypeNamesList, Bool.and_eq_true] at names
    simp only [checkFreevarsAstList, Bool.and_eq_true] at free
    simp only [typeNameSubstList, checkFreevarsList, Bool.and_eq_true]
    exact ⟨checkFreevarsTypeNameSubst tvs t dbmax env ⟨wellFormed, names.1, free.1⟩,
      typeNamesFreevars tvs rest dbmax env ⟨wellFormed, names.2, free.2⟩⟩
termination_by sizeOf ts
end

end Flapjack.TypeSysProps
