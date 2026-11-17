module

public import Flapjack.Compiler.Inference.Infer.TypeDefinitions
public import Flapjack.Compiler.Inference.Infer.TypeNameCheckBind

@[expose] public section

/-! Expanded source equations for type-definition checking. -/
namespace Flapjack.Compiler.Inference.Infer.TypeDefinitions
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.Misc.Location
  Flapjack.Basis.Pure.MlString Flapjack.Translator.Monadic.MonadBase
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.Infer.Duplicates
  Flapjack.Compiler.Inference.Infer.TypeNameCheck

@[hol "cakeml/compiler/inference/inferScript.sml" "check_ctor_types_expand"]
theorem checkCtorTypesExpand {σ : Type} :
    (∀ tvs env l (s : σ), checkCtorTypes l env tvs [] s = (.success (), s)) ∧
    (∀ tvs ts env l ctors name (s : σ),
      checkCtorTypes l env tvs ((name, ts) :: ctors) s =
      match typeNameCheckSubList l env tvs ts s with
      | (.success _, s') => checkCtorTypes l env tvs ctors s'
      | (.failure (loc, .inl msg), s') => (.failure (loc, msg), s')
      | (.failure (loc, .inr tv), s') => (.failure (loc,
          MlString.concat [ofString "Unbound type variable ", tv,
            ofString " in type definition with constructor ", name]), s')) := by
  constructor
  · intros; rfl
  · intro tvs ts env l ctors name s
    let formatter := fun tv => MlString.concat [ofString "Unbound type variable ", tv,
      ofString " in type definition with constructor ", name]
    have h := (ignoreBindTypeNameCheckSubst l formatter env tvs (.atvar name) ts
      (fun s : σ => (.success (), s)) (checkCtorTypes l env tvs ctors)).2
    cases result : typeNameCheckSubList l env tvs ts s with
    | mk answer next =>
      cases answer with
      | success values => simpa [checkCtorTypes, formatter, result] using congrFun h s
      | failure error =>
        rcases error with ⟨loc, sum⟩
        cases sum <;> simpa [checkCtorTypes, formatter, result] using congrFun h s

@[hol "cakeml/compiler/inference/inferScript.sml" "check_ctors_expand"]
theorem checkCtorsExpand {σ : Type} :
    (∀ env l (s : σ), checkCtors l env [] s = (.success (), s)) ∧
    (∀ tvs name env defs l ctors (s : σ),
      checkCtors l env ((tvs, name, ctors) :: defs) s =
      match findDupHOL (ctors.map Prod.fst) with
      | some n => (.failure (l.loc, MlString.concat [ofString "Duplicate constructor ", n,
          ofString " in the definition of type ", name]), s)
      | none => match findDupHOL tvs with
        | some n => (.failure (l.loc, MlString.concat [ofString "Duplicate type variable binding ", n,
            ofString " in the definition of type ", name]), s)
        | none => match checkCtorTypes l env tvs ctors s with
          | (.success _, s') => checkCtors l env defs s'
          | (.failure e, s') => (.failure e, s')) := by
  constructor
  · intros; rfl
  · intro tvs name env defs l ctors s
    simp only [checkCtors, ← checkDups_eq, checkDupsEqFindDup]
    cases findDupHOL (ctors.map Prod.fst) with
    | none =>
      simp only [ignoreBind]
      cases findDupHOL tvs with
      | none =>
        cases h : checkCtorTypes l env tvs ctors s with
        | mk result next => cases result <;> rfl
      | some n => rfl
    | some n => rfl

@[hol "cakeml/compiler/inference/inferScript.sml" "check_type_definition_expand"]
theorem checkTypeDefinitionExpand {σ : Type} :
    ∀ l env defs (s : σ), checkTypeDefinition l env defs s =
      match findDupHOL (defs.map (fun (_, name, _) => name)) with
      | none => checkCtors l env defs s
      | some n => (.failure (l.loc, MlString.concat [ofString "Duplicate type constructor ", n,
          ofString " in a mutually recursive type definition"]), s) := by
  intro l env defs s
  simp only [checkTypeDefinition, ← checkDups_eq, checkDupsEqFindDup]
  cases findDupHOL (defs.map (fun (_, name, _) => name)) <;> rfl

end Flapjack.Compiler.Inference.Infer.TypeDefinitions
