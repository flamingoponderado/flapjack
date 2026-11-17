module

public import Flapjack.Compiler.Inference.TypeDCanon
public import Flapjack.Misc.PredSet

@[expose] public section

/-! Inverse identifier renamings for canonical declaration typing. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

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

mutual
/-- Renaming back with the left inverse restores every type whose IDs are in the domain. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "ts_tid_rename_LINV"]
theorem tsTidRenameLinv (s t : Nat → Prop) (f : Nat → Nat) (x : SemanticT) :
    holInj f s t ∧ setTidsSubset s x → tsTidRename (holLinv f s) (tsTidRename f x) = x := by
  rintro ⟨inj, subset⟩
  cases x with
  | var name => simp [tsTidRename]
  | varDb n => simp [tsTidRename]
  | app args id =>
    have idMem : s id := subset id (by simp [setTids])
    have argsSubset : ∀ n, setTidsList args n → s n := by
      intro n hn
      exact subset n (by simp [setTids, hn])
    simp [tsTidRename, tsTidRenameList_eq_map, holLinvDef f s t inj id idMem,
      tsTidRenameLinvList s t f args inj argsSubset]
termination_by sizeOf x

/-- List traversal used by the source type-renaming induction. -/
private theorem tsTidRenameLinvList (s t : Nat → Prop) (f : Nat → Nat) (xs : List SemanticT)
    (inj : holInj f s t) (subset : ∀ n, setTidsList xs n → s n) :
    (xs.map (tsTidRename f)).map (tsTidRename (holLinv f s)) = xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    have head : setTidsSubset s x := by
      intro n hn
      exact subset n (by simp [setTidsList, hn])
    have tail : ∀ n, setTidsList xs n → s n := by
      intro n hn
      exact subset n (by simp [setTidsList, hn])
    simp [tsTidRenameLinv s t f x ⟨inj, head⟩, tsTidRenameLinvList s t f xs inj tail]
termination_by sizeOf xs
end

end Flapjack.Compiler.Inference.TypeDCanon
