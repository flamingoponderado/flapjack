module

public import Flapjack.Compiler.Inference.TypeDCanon
public import Flapjack.TypeSysProps.Expression
public import Flapjack.TypeSysProps.Constructor
public import Flapjack.NamespaceProps.EmptyLookup
public import Flapjack.NamespaceProps.LiftLookup

@[expose] public section

/-! Canonical declaration typing preserves well-formed environments. -/

namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants Flapjack.NamespaceHOL
  Flapjack.Basis.Pure.MlString Flapjack.AstHOL Flapjack.TypeSysProps

/-- Binding types checked at a common level form a well-formed value environment. -/
private theorem bindingEnvOk (tvs : Nat) (bindings : List (MlString × SemanticT))
    (checks : (bindings.map Prod.snd).all (checkFreevars tvs []) = true) :
    tenvOk ⟨alistToNs (tenvAddTvs tvs bindings), nsEmpty, nsEmpty⟩ := by
  simp only [tenvOk, tenvValOk, tenvCtorOk, tenvAbbrevOk]
  refine ⟨?_, ?_, ?_⟩
  · apply nsAllAlistToNs
    intro entry member
    simp only [tenvAddTvs, List.mem_map] at member
    obtain ⟨⟨name, ty⟩, mem, rfl⟩ := member
    simpa using (List.all_eq_true.mp checks ty (List.mem_map.mpr ⟨(name, ty), mem, rfl⟩))
  · simp [nsAll, nsLookup_nsEmpty]
  · simp [nsAll, nsLookup_nsEmpty]

set_option maxHeartbeats 1200000 in
/-- Canonical declaration and declaration-list typing preserve environment well-formedness. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_d_canon_tenv_ok"]
theorem typeDCanonTenvOk :
    (∀ n env d count out, TypeDCanon n env d count out → tenvOk env → tenvOk out) ∧
    (∀ n env ds count out, TypeDsCanon n env ds count out → tenvOk env → tenvOk out) := by
  classical
  constructor <;> intro n env d count out typed
  all_goals
    first
    | refine TypeDCanon.rec (motive_1 := fun n env d count out _ => tenvOk env → tenvOk out)
        (motive_2 := fun n env ds count out _ => tenvOk env → tenvOk out) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    | refine TypeDsCanon.rec (motive_1 := fun n env d count out _ => tenvOk env → tenvOk out)
        (motive_2 := fun n env ds count out _ => tenvOk env → tenvOk out) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    case refine_1 =>
      intro n tvs env p e t bindings loc value distinct pattern expression principal ok
      exact bindingEnvOk tvs bindings (typePFreevars.1 tvs env p t bindings pattern).2
    case refine_2 =>
      intro n env p e t bindings loc restricted distinct pattern expression ok
      exact bindingEnvOk 0 bindings (typePFreevars.1 0 env p t bindings pattern).2
    case refine_3 =>
      intro n env funs bindings tvs loc typed principal ok
      apply bindingEnvOk tvs bindings
      have localOk : tenvValExpOk (bindVarList 0 bindings (bindTvar tvs .empty)) := by
        apply tenvValExpOkBvlFuns funs bindings env bindings () (bindTvar tvs .empty)
        exact ⟨typed, by by_cases zero : tvs = 0 <;> simp [bindTvar, tenvValExpOk, zero]⟩
      have result := typeEFreevars.2.2 env (bindVarList 0 bindings (bindTvar tvs .empty)) funs bindings typed ⟨localOk, ok.1⟩
      by_cases zero : tvs = 0 <;> simpa [numTvsBindVarList, bindTvar, numTvs, zero] using result
    case refine_4 =>
      intro n ids env defs newTypes loc bound allocated valid types ok
      have newOk : tenvAbbrevOk newTypes := by
        rw [types]
        unfold tenvAbbrevOk
        apply nsAllAlistToNs
        intro entry member
        simp only [List.mem_map] at member
        obtain ⟨⟨⟨params, name, ctors⟩, id⟩, member, rfl⟩ := member
        simp [checkFreevars, checkFreevarsListEqAll]
      have lengthEq : defs.length = ids.length := by simp [allocated]
      have ctorOk := checkCtorTenvOk (M := MlString) (nsAppend newTypes env.t) defs ids
        ⟨lengthEq, valid, nsAll_nsAppend _ _ _ ⟨newOk, ok.2.2⟩⟩
      exact ⟨by simp [tenvValOk, nsAll, nsLookup_nsEmpty], ctorOk, newOk⟩
    case refine_5 =>
      intro n env tvs name t loc free names distinct ok
      simp only [tenvOk, tenvValOk, tenvCtorOk, tenvAbbrevOk]
      refine ⟨by simp [nsAll, nsLookup_nsEmpty], by simp [nsAll, nsLookup_nsEmpty], ?_⟩
      change @nsAll MlString MlString _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _) _
        (alistToNs [(name, (tvs, typeNameSubst env.t t))] : TenvAbbrev)
      apply nsAllAlistToNs
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      exact checkFreevarsTypeNameSubst tvs t 0 env.t ⟨ok.2.2, names, free⟩
    case refine_6 =>
      intro n env name ts loc free names ok
      simp only [tenvOk, tenvValOk, tenvCtorOk, tenvAbbrevOk]
      refine ⟨by simp [nsAll, nsLookup_nsEmpty], ?_, by simp [nsAll, nsLookup_nsEmpty]⟩
      change @nsAll MlString MlString _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _) _
        (alistToNs [(name, ([], ts.map (typeNameSubst env.t), TexnNum))] : TenvCtor)
      apply nsAllAlistToNs
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      intro ty tymem
      obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp tymem
      exact checkFreevarsTypeNameSubst [] source 0 env.t
        ⟨ok.2.2, List.all_eq_true.mp names source sourceMem, List.all_eq_true.mp free source sourceMem⟩
    case refine_7 =>
      intro n env name ds count newEnv typed ih ok
      have result := ih ok
      simpa only [tenvOk, tenvValOk, tenvCtorOk, tenvAbbrevOk, tenvLift, nsAll_nsLift] using result
    case refine_8 =>
      intro n env privateDs publicDs env1 env2 count1 count2 first second ih1 ih2 ok
      exact ih2 (extendDecTenvOk env1 env ⟨ih1 ok, ok⟩)
    case refine_9 =>
      intro n env ok
      simp [tenvOk, tenvValOk, tenvCtorOk, tenvAbbrevOk, nsAll, nsLookup_nsEmpty]
    case refine_10 =>
      intro n env d ds env1 env2 count1 count2 head tail ih1 ih2 ok
      have ok1 := ih1 ok
      exact extendDecTenvOk env2 env1 ⟨ih2 (extendDecTenvOk env1 env ⟨ok1, ok⟩), ok1⟩
end Flapjack.Compiler.Inference.TypeDCanon
