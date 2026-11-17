module

public import Flapjack.Compiler.Inference.TypeDCanon
public import Flapjack.Misc.PredSet

@[expose] public section

/-! Inverse identifier renamings for canonical declaration typing. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

/-- Use the optional inverse when it exists, falling back to the original map. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "LINVI_def"]
noncomputable def linvi {α : Type} (f : α → α) (s : α → Prop) (y : α) : α :=
  match holLinvOpt f s y with
  | some x => x
  | none => f y

mutual
/-- Composing identifier renamings is the same as renaming by their composition. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_compose"]
theorem tsTidRenameCompose (g : Nat → Nat) (t : SemanticT) (f : Nat → Nat) :
    tsTidRename f (tsTidRename g t) = tsTidRename (f ∘ g) t := by
  cases t with
  | var name => simp [tsTidRename]
  | varDb n => simp [tsTidRename]
  | app args id => simp [tsTidRename, tsTidRenameComposeList g args f]
termination_by sizeOf t

/-- List traversal for the source renaming-composition induction. -/
private theorem tsTidRenameComposeList (g : Nat → Nat) (ts : List SemanticT) (f : Nat → Nat) :
    tsTidRenameList f (tsTidRenameList g ts) = tsTidRenameList (f ∘ g) ts := by
  cases ts with
  | nil => simp [tsTidRenameList]
  | cons t ts => simp [tsTidRenameList, tsTidRenameCompose g t f, tsTidRenameComposeList g ts f]
termination_by sizeOf ts
end

/-- Renaming a type environment twice composes the identifier maps. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenv_compose"]
theorem remapTenvCompose (f g : Nat → Nat) (env : TypeEnv) :
    remapTenv f (remapTenv g env) = remapTenv (f ∘ g) env := by
  simp [remapTenv, nsMapCompose, Function.comp_def, List.map_map, tsTidRenameCompose]

mutual
/-- Two renamings agree exactly when they agree on the identifiers in a type. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_eq_f"]
theorem tsTidRenameEqF (f : Nat → Nat) (t : SemanticT) (g : Nat → Nat) :
    tsTidRename f t = tsTidRename g t ↔ ∀ x, setTids t x → f x = g x := by
  cases t with
  | var name => simp [tsTidRename, setTids]
  | varDb index => simp [tsTidRename, setTids]
  | app xs id => simp [tsTidRename, setTids, tsTidRenameEqFList f xs g, and_comm]
termination_by sizeOf t

/-- List traversal for the source equality-of-renamings induction. -/
private theorem tsTidRenameEqFList (f : Nat → Nat) (xs : List SemanticT) (g : Nat → Nat) :
    tsTidRenameList f xs = tsTidRenameList g xs ↔ ∀ x, setTidsList xs x → f x = g x := by
  cases xs with
  | nil => simp [tsTidRenameList, setTidsList]
  | cons x xs =>
    simp only [tsTidRenameList, List.cons.injEq, tsTidRenameEqF f x g, tsTidRenameEqFList f xs g, setTidsList]
    constructor
    · rintro ⟨head, tail⟩ id (member | member)
      · exact head id member
      · exact tail id member
    · intro all
      exact ⟨fun id member => all id (Or.inl member), fun id member => all id (Or.inr member)⟩
termination_by sizeOf xs
end


/-- A type is unchanged exactly when every identifier occurring in it is fixed. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_eq_id"]
theorem tsTidRenameEqId (f : Nat → Nat) (t : SemanticT) :
    tsTidRename f t = t ↔ ∀ id, setTids t id → f id = id := by
  simpa [tsTidRenameId] using tsTidRenameEqF f t id

/-- The optional inverse recovers each domain element of an injection. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "INJ_LINVI"]
theorem injLinvi {α : Type} (f : α → α) (s t : α → Prop) (x : α) :
    holInj f s t ∧ s x → linvi f s (f x) = x := by
  rintro ⟨inj, member⟩
  have found := (holInjLinvOpt f s t inj x (f x)).2 ⟨rfl, member, inj.1 x member⟩
  simp [linvi, found]

/-- Applying the original injection after the inverse restores each image element. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "LINVI_RINV"]
theorem linviRinv {α : Type} (f : α → α) (s t : α → Prop) (y : α) :
    holInj f s t ∧ (∃ x, s x ∧ f x = y) → f (linvi f s y) = y := by
  rintro ⟨inj, x, member, rfl⟩
  rw [injLinvi f s t x ⟨inj, member⟩]

/-- The extended inverse of a good renaming fixes primitive identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "good_remap_LINVI"]
theorem goodRemapLinvi (f : Nat → Nat) (s t : Nat → Prop) :
    goodRemap f ∧ primTids true s ∧ holInj f s t → goodRemap (linvi f s) := by
  rintro ⟨good, prim, inj⟩
  have fixed := mapFixedOnMembers f (TlistNum :: TboolNum :: primTypeNums) good
  unfold goodRemap
  calc
    (TlistNum :: TboolNum :: primTypeNums).map (linvi f s) =
        (TlistNum :: TboolNum :: primTypeNums).map id := by
      apply List.map_congr_left
      intro n member
      have fn := fixed n member
      have inv := injLinvi f s t n ⟨inj, (prim n member).2 rfl⟩
      simpa [fn] using inv
    _ = _ := List.map_id _

/-- A left inverse composed with a good renaming fixes primitive identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "good_remap_LINV"]
theorem goodRemapLinv (f : Nat → Nat) (s t : Nat → Prop) :
    goodRemap f ∧ primTids true s ∧ holInj f s t → goodRemap (holLinv f s ∘ f) := by
  rintro ⟨_, prim, inj⟩
  unfold goodRemap
  calc
    (TlistNum :: TboolNum :: primTypeNums).map (holLinv f s ∘ f) =
        (TlistNum :: TboolNum :: primTypeNums).map id := by
      apply List.map_congr_left
      intro n member
      exact holLinvDef f s t inj n ((prim n member).2 rfl)
    _ = _ := List.map_id _

/-- Renaming back with the left inverse restores every type whose IDs are in the domain. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_LINV"]
theorem tsTidRenameLinv (s t : Nat → Prop) (f : Nat → Nat) (x : SemanticT) :
    holInj f s t ∧ setTidsSubset s x → tsTidRename (holLinv f s) (tsTidRename f x) = x := by
  rintro ⟨inj, subset⟩
  rw [tsTidRenameCompose]
  apply (tsTidRenameEqId _ x).2
  intro id member
  exact holLinvDef f s t inj id (subset id member)

/-- The extended inverse restores types whose identifiers lie in the injection domain. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_LINVI"]
theorem tsTidRenameLinvi (s t : Nat → Prop) (f : Nat → Nat) (x : SemanticT) :
    holInj f s t ∧ setTidsSubset s x → tsTidRename (linvi f s) (tsTidRename f x) = x := by
  rintro ⟨inj, subset⟩
  rw [tsTidRenameCompose]
  apply (tsTidRenameEqId _ x).2
  intro id member
  exact injLinvi f s t id ⟨inj, subset id member⟩

mutual
/-- Renaming equal types back is injective under the source cross-ID condition. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "inj_ts_tid_rename_eq"]
theorem injTsTidRenameEq (f : Nat → Nat) (t1 t2 : SemanticT) :
    (∀ x y, setTids t1 x ∧ setTids t2 y ∧ f x = f y → x = y) ∧
      tsTidRename f t1 = tsTidRename f t2 → t1 = t2 := by
  rintro ⟨inj, eq⟩
  cases t1 with
  | var name => cases t2 <;> simp_all [tsTidRename]
  | varDb index => cases t2 <;> simp_all [tsTidRename]
  | app xs a =>
    cases t2 with
    | var name => simp [tsTidRename] at eq
    | varDb index => simp [tsTidRename] at eq
    | app ys b =>
      simp only [tsTidRename, SemanticT.app.injEq] at eq
      have ab : a = b := inj a b ⟨by simp [setTids], by simp [setTids], eq.2⟩
      have lists : xs = ys := injTsTidRenameEqList f xs ys (by
        intro x y hx hy equal
        apply inj x y
        exact ⟨by simp [setTids, hx], by simp [setTids, hy], equal⟩) eq.1
      simp [ab, lists]
termination_by sizeOf t1

/-- List traversal for the source cross-type renaming induction. -/
private theorem injTsTidRenameEqList (f : Nat → Nat) (xs ys : List SemanticT)
    (inj : ∀ x y, setTidsList xs x → setTidsList ys y → f x = f y → x = y)
    (eq : tsTidRenameList f xs = tsTidRenameList f ys) : xs = ys := by
  cases xs with
  | nil => cases ys <;> simp_all [tsTidRenameList]
  | cons x xs =>
    cases ys with
    | nil => simp [tsTidRenameList] at eq
    | cons y ys =>
      simp only [tsTidRenameList, List.cons.injEq] at eq
      have head : x = y := injTsTidRenameEq f x y ⟨by
        intro a b hab
        exact inj a b (by simp [setTidsList, hab.1]) (by simp [setTidsList, hab.2.1]) hab.2.2, eq.1⟩
      have tail : xs = ys := injTsTidRenameEqList f xs ys (by
        intro a b ha hb equal
        exact inj a b (by simp [setTidsList, ha]) (by simp [setTidsList, hb]) equal) eq.2
      simp [head, tail]
termination_by sizeOf xs
end

end Flapjack.Compiler.Inference.TypeDCanon
