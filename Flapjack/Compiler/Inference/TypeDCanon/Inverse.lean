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
/-- A type is unchanged exactly when every identifier occurring in it is fixed. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_eq_id"]
theorem tsTidRenameEqId (f : Nat → Nat) (t : SemanticT) :
    tsTidRename f t = t ↔ ∀ id, setTids t id → f id = id := by
  cases t with
  | var name => simp [tsTidRename, setTids]
  | varDb n => simp [tsTidRename, setTids]
  | app args id =>
    simp [tsTidRename, setTids, tsTidRenameListEqId f args, and_comm]
termination_by sizeOf t

/-- List traversal for the source characterization of identity renaming. -/
private theorem tsTidRenameListEqId (f : Nat → Nat) (ts : List SemanticT) :
    tsTidRenameList f ts = ts ↔ ∀ id, setTidsList ts id → f id = id := by
  cases ts with
  | nil => simp [tsTidRenameList, setTidsList]
  | cons t ts =>
    simp only [tsTidRenameList, List.cons.injEq, tsTidRenameEqId f t, tsTidRenameListEqId f ts, setTidsList]
    constructor
    · rintro ⟨head, tail⟩ id (member | member)
      · exact head id member
      · exact tail id member
    · intro all
      exact ⟨fun id member => all id (Or.inl member), fun id member => all id (Or.inr member)⟩
termination_by sizeOf ts
end

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

end Flapjack.Compiler.Inference.TypeDCanon
