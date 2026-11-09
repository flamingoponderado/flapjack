module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnvConditions
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations

@[expose] public section

/-! Equality simulation over the source-to-flat value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- The constructor-map injectivity condition identifies equal stamps with
equal flat constructor keys and arities. This is Flapjack infrastructure. -/
theorem constructor_lookup_eq_iff (genv : GlobalEnv) (ok : genvCOk genv.c)
    (cn1 cn2 : FlatLang.CtorId × FlatLang.TypeId) (arity1 arity2 : Nat) (s1 s2 : Stamp)
    (h1 : genv.c.lookup (cn1, arity1) = some s1)
    (h2 : genv.c.lookup (cn2, arity2) = some s2) :
    s1 = s2 ↔ cn1 = cn2 ∧ arity1 = arity2 := by
  constructor
  · intro h
    cases h
    exact ok.2.2.2.2 cn1 cn2 arity1 arity2 s1 h1 h2
  · rintro ⟨rfl, rfl⟩
    exact Option.some.inj (h1.symm.trans h2)

/-- Named-constructor equality follows from the list induction hypothesis and
the original constructor-map consistency conditions. This is a Flapjack case
lemma over the factored value relation. -/
theorem equality_constructor_step (genv : GlobalEnv) (ok : genvCOk genv.c)
    (s1 s2 : Stamp) (cn1 cn2 : FlatLang.CtorId × FlatLang.TypeId)
    (xs ys : List SemanticPrimitivesHOL.Value) (fxs fys : List FlatSem.Value)
    (relXs : List.Forall₂ (ValueRel genv) xs fxs) (relYs : List.Forall₂ (ValueRel genv) ys fys)
    (lookup1 : genv.c.lookup (cn1, xs.length) = some s1)
    (lookup2 : genv.c.lookup (cn2, ys.length) = some s2)
    (listIH : FlatSem.doEqList fxs fys = SemanticPrimitivesHOL.doEqList xs ys) :
    FlatSem.doEq (.conv (some cn1) fxs) (.conv (some cn2) fys) =
      SemanticPrimitivesHOL.doEq (.conv (some s1) xs) (.conv (some s2) ys) := by
  have lenXs := relXs.length_eq
  have lenYs := relYs.length_eq
  have keyEq := constructor_lookup_eq_iff genv ok cn1 cn2 xs.length ys.length s1 s2 lookup1 lookup2
  have typeEq := ok.2.2.2.1 cn1 cn2 xs.length ys.length s1 s2 lookup1 lookup2
  have matchEq : (s1 = s2 ∧ xs.length = ys.length) ↔
      (cn1 = cn2 ∧ fxs.length = fys.length) := by
    simp only [← lenXs, ← lenYs]
    constructor
    · rintro ⟨h, _⟩
      exact keyEq.mp h
    · rintro ⟨hc, hl⟩
      exact ⟨keyEq.mpr ⟨hc, hl⟩, hl⟩
  by_cases sourceMatch : s1 = s2 ∧ xs.length = ys.length
  · have flatMatch := matchEq.mp sourceMatch
    simp [FlatSem.doEq, SemanticPrimitivesHOL.doEq, sourceMatch, flatMatch, listIH]
  · have flatMismatch : ¬ (cn1 = cn2 ∧ fxs.length = fys.length) :=
      fun h => sourceMatch (matchEq.mpr h)
    by_cases sameType : SemanticPrimitivesHOL.ctorSameType (some s1) (some s2) = true
    · have flatSame := typeEq.mp sameType
      simp [FlatSem.doEq, SemanticPrimitivesHOL.doEq, sourceMatch, flatMismatch, sameType, flatSame]
    · have flatDifferent : ¬ FlatSem.ctorSameType (some cn1) (some cn2) :=
        fun h => sameType (typeEq.mpr h)
      simp [FlatSem.doEq, SemanticPrimitivesHOL.doEq, sourceMatch, flatMismatch, sameType, flatDifferent]

/-- Tuple equality follows from the list induction hypothesis. This is a
Flapjack case lemma over the factored value relation. -/
theorem equality_tuple_step (genv : GlobalEnv)
    (xs ys : List SemanticPrimitivesHOL.Value) (fxs fys : List FlatSem.Value)
    (relXs : List.Forall₂ (ValueRel genv) xs fxs) (relYs : List.Forall₂ (ValueRel genv) ys fys)
    (listIH : FlatSem.doEqList fxs fys = SemanticPrimitivesHOL.doEqList xs ys) :
    FlatSem.doEq (.conv none fxs) (.conv none fys) =
      SemanticPrimitivesHOL.doEq (.conv none xs) (.conv none ys) := by
  have lenXs := relXs.length_eq
  have lenYs := relYs.length_eq
  simp [FlatSem.doEq, SemanticPrimitivesHOL.doEq, SemanticPrimitivesHOL.ctorSameType,
    FlatSem.ctorSameType, ← lenXs, ← lenYs, listIH]

/-- Vector equality follows from the list induction hypothesis. This is a
Flapjack case lemma over the factored value relation. -/
theorem equality_vector_step (genv : GlobalEnv)
    (xs ys : List SemanticPrimitivesHOL.Value) (fxs fys : List FlatSem.Value)
    (relXs : List.Forall₂ (ValueRel genv) xs fxs) (relYs : List.Forall₂ (ValueRel genv) ys fys)
    (listIH : FlatSem.doEqList fxs fys = SemanticPrimitivesHOL.doEqList xs ys) :
    FlatSem.doEq (.vectorv fxs) (.vectorv fys) =
      SemanticPrimitivesHOL.doEq (.vectorv xs) (.vectorv ys) := by
  have lenXs := relXs.length_eq
  have lenYs := relYs.length_eq
  simp [FlatSem.doEq, SemanticPrimitivesHOL.doEq, ← lenXs, ← lenYs, listIH]

/-- The nonempty list case composes the head and tail induction hypotheses.
This is Flapjack infrastructure for the mutual equality proof. -/
theorem equality_list_cons_step (x y : SemanticPrimitivesHOL.Value) (xs ys : List SemanticPrimitivesHOL.Value)
    (fx fy : FlatSem.Value) (fxs fys : List FlatSem.Value)
    (headIH : FlatSem.doEq fx fy = SemanticPrimitivesHOL.doEq x y)
    (tailIH : FlatSem.doEqList fxs fys = SemanticPrimitivesHOL.doEqList xs ys) :
    FlatSem.doEqList (fx :: fxs) (fy :: fys) = SemanticPrimitivesHOL.doEqList (x :: xs) (y :: ys) := by
  simp only [FlatSem.doEqList, SemanticPrimitivesHOL.doEqList, headIH]
  cases SemanticPrimitivesHOL.doEq x y with
  | typeError => rfl
  | val b => cases b <;> simp [tailIH]

mutual
/-- Equality preservation for the source-to-flat value relation. This is
Flapjack proof infrastructure for the HOL-shaped equality simulation below. -/
theorem equality_preserved (genv : GlobalEnv) (ok : genvCOk genv.c)
    (a b : SemanticPrimitivesHOL.Value) (fa fb : FlatSem.Value)
    (ha : ValueRel genv a fa) (hb : ValueRel genv b fb) :
    FlatSem.doEq fa fb = SemanticPrimitivesHOL.doEq a b := by
  cases ha <;> cases hb <;>
    try (solve | simp [FlatSem.doEq, SemanticPrimitivesHOL.doEq,
      FlatSem.ctorSameType, SemanticPrimitivesHOL.ctorSameType])
  case constructor.constructor =>
    rename_i s1 cn1 xs fxs relXs lookup1 s2 cn2 ys fys relYs lookup2
    exact equality_constructor_step genv ok s1 s2 cn1 cn2 xs ys fxs fys
      ((valueListRel_iff genv xs fxs).mp relXs) ((valueListRel_iff genv ys fys).mp relYs)
      lookup1 lookup2 (equality_list_preserved genv ok xs ys fxs fys relXs relYs)
  case tuple.tuple =>
    rename_i xs fxs relXs ys fys relYs
    exact equality_tuple_step genv xs ys fxs fys
      ((valueListRel_iff genv xs fxs).mp relXs) ((valueListRel_iff genv ys fys).mp relYs)
      (equality_list_preserved genv ok xs ys fxs fys relXs relYs)
  case vector.vector =>
    rename_i xs fxs relXs ys fys relYs
    exact equality_vector_step genv xs ys fxs fys
      ((valueListRel_iff genv xs fxs).mp relXs) ((valueListRel_iff genv ys fys).mp relYs)
      (equality_list_preserved genv ok xs ys fxs fys relXs relYs)
termination_by sizeOf a

/-- List case of equality preservation for the factored relation. -/
theorem equality_list_preserved (genv : GlobalEnv) (ok : genvCOk genv.c)
    (xs ys : List SemanticPrimitivesHOL.Value) (fxs fys : List FlatSem.Value)
    (hx : ValueListRel genv xs fxs) (hy : ValueListRel genv ys fys) :
    FlatSem.doEqList fxs fys = SemanticPrimitivesHOL.doEqList xs ys := by
  cases hx <;> cases hy <;>
    try (solve | simp [FlatSem.doEqList, SemanticPrimitivesHOL.doEqList])
  case cons.cons =>
    rename_i x fx xs fxs hx tx y fy ys fys hy ty
    exact equality_list_cons_step x y xs ys fx fy fxs fys
      (equality_preserved genv ok x y fx fy hx hy)
      (equality_list_preserved genv ok xs ys fxs fys tx ty)
termination_by sizeOf xs
end

namespace EqualityPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end EqualityPort

/-- Equality of values and lists is preserved by the value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_eq"
  (fmap_as_finite_support := [c, tys])]
theorem equality_simulation (genv : GlobalEnv) (ok : genvCOk genv.c) :
    (∀ a b result fa fb, SemanticPrimitivesHOL.doEq a b = result ∧
      ValueRel genv a fa ∧ ValueRel genv b fb → FlatSem.doEq fa fb = result) ∧
    (∀ xs ys result fxs fys, SemanticPrimitivesHOL.doEqList xs ys = result ∧
      List.Forall₂ (ValueRel genv) xs fxs ∧ List.Forall₂ (ValueRel genv) ys fys →
      FlatSem.doEqList fxs fys = result) := by
  constructor
  · intro a b result fa fb ⟨sourceEq, ha, hb⟩
    exact (equality_preserved genv ok a b fa fb ha hb).trans sourceEq
  · intro xs ys result fxs fys ⟨sourceEq, hx, hy⟩
    exact (equality_list_preserved genv ok xs ys fxs fys
      ((valueListRel_iff genv xs fxs).mpr hx) ((valueListRel_iff genv ys fys).mpr hy)).trans sourceEq

end Flapjack.Compiler.Backend.SourceToFlat
