module

public import Flapjack.Compiler.Inference.TypeDCanon.Inverse
public import Flapjack.Compiler.Inference.TypeDCanon.Bijection

@[expose] public section

/-! Inverse renaming for declarative type environments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps Flapjack.Compiler.Inference.TypeDCanon

/-- Flapjack lookup infrastructure: a map fixing every visible value preserves
namespace equivalence. The source proof establishes this inline through lookups. -/
private theorem nsAll2MapFixed {M N V : Type} [DecidableEq M] [DecidableEq N]
    (h : V → V) (env : Namespace M N V)
    (fixed : ∀ id v, nsLookup env id = some v → h v = v) :
    nsAll2 (fun _ a b => a = b) (nsMap h env) env := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro id v found
    rw [nsLookup_nsMap] at found
    cases source : nsLookup env id with
    | none => simp [source] at found
    | some value =>
      simp [source] at found
      subst v
      exact ⟨value, rfl, fixed id value source⟩
  · intro path absent
    simp [nsLookupMod_nsMap, absent]
  · intro id v found
    exact ⟨h v, by simp [nsLookup_nsMap, found], fixed id v found⟩
  · intro path absent
    rw [nsLookupMod_nsMap] at absent
    cases source : nsLookupMod env path <;> simp [source] at absent ⊢

/-- Flapjack proof infrastructure shared by the two HOL environment inverse laws;
its pointwise premise is discharged by the corresponding inverse theorem. -/
private theorem remapTenvFixed (f : Nat → Nat) (s : Nat → Prop) (env : TypeEnv)
    (fixed : ∀ id, s id → f id = id) (bound : setTidsTenv s env) :
    tenvEquiv (remapTenv f env) env := by
  obtain ⟨types, constructors, values⟩ := bound
  refine ⟨?_, ?_, ?_⟩
  · apply nsAll2MapFixed
    intro id entry found
    have h := types id entry found
    have fixedType := (tsTidRenameEqId f entry.2).2 (fun id member => fixed id (h id member))
    simp [fixedType]
  · apply nsAll2MapFixed
    intro id entry found
    have ⟨typesBound, idBound⟩ := constructors id entry found
    have fixedTypes : entry.2.1.map (tsTidRename f) = entry.2.1 := by
      calc
        _ = entry.2.1.map (fun x => x) := by
          apply List.map_congr_left
          intro typ member
          exact (tsTidRenameEqId f typ).2 (fun n h => fixed n (typesBound typ member n h))
        _ = _ := List.map_id _
    simp [fixedTypes, fixed _ idBound]
  · apply nsAll2MapFixed
    intro id entry found
    have h := values id entry found
    have fixedType := (tsTidRenameEqId f entry.2).2 (fun id member => fixed id (h id member))
    simp [fixedType]

/-- A good bijection's left inverse also fixes all primitive identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "good_remap_BIJ"]
theorem goodRemapBij (f : Nat → Nat) (s t : Set Nat) :
    goodRemap f ∧ primTids true s ∧ Set.BijOn f s t → goodRemap (holLinv f s) := by
  rintro ⟨good, prim, bij⟩
  have inj : holInj f s t := ⟨fun _ hx => bij.1 hx, fun _ _ h eq => bij.2.1 h.1 h.2 eq⟩
  have fixed := mapFixedOnMembers f (TlistNum :: TboolNum :: primTypeNums) good
  unfold goodRemap
  calc
    (TlistNum :: TboolNum :: primTypeNums).map (holLinv f s) =
        (TlistNum :: TboolNum :: primTypeNums).map id := by
      apply List.map_congr_left
      intro n member
      have inv := holLinvDef f s t inj n ((prim n member).2 rfl)
      simpa [fixed n member] using inv
    _ = _ := List.map_id _

/-- The extended inverse restores an environment up to HOL lookup equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenv_LINVI"]
theorem remapTenvLinvi (f : Nat → Nat) (s t : Nat → Prop) (env : TypeEnv) :
    holInj f s t ∧ setTidsTenv s env → tenvEquiv (remapTenv (linvi f s) (remapTenv f env)) env := by
  rintro ⟨inj, bound⟩
  rw [remapTenvCompose]
  apply remapTenvFixed _ s env ?_ bound
  intro id member
  exact injLinvi f s t id ⟨inj, member⟩

/-- A bijection and its left inverse restore an environment up to lookup equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenv_LINV"]
theorem remapTenvLinv (f : Nat → Nat) (s t : Set Nat) (env : TypeEnv) :
    Set.BijOn f s t ∧ setTidsTenv s env → tenvEquiv (remapTenv (holLinv f s) (remapTenv f env)) env := by
  rintro ⟨bij, bound⟩
  have inj : holInj f s t := ⟨fun x hx => bij.1 hx, fun x y h eq => bij.2.1 h.1 h.2 eq⟩
  rw [remapTenvCompose]
  apply remapTenvFixed _ s env ?_ bound
  intro id member
  exact holLinvDef f s t inj id member

end Flapjack.Compiler.Inference.TypeDCanon
