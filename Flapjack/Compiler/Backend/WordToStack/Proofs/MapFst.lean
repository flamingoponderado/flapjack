import Flapjack.HolRef

namespace Flapjack.WordToStackProofs

/-- Map the first component of each pair, retaining order and second components. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FST_def"]
def mapFst {α β γ : Type} (f : α → β) (xs : List (α × γ)) : List (β × γ) :=
  xs.map (fun (x, y) => (f x, y))

/-- Key renaming preserves the entire value projection, with no function premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_SND_MAP_FST"]
theorem mapSndMapFst {α β γ : Type} (xs : List (α × γ)) (f : α → β) :
    (mapFst f xs).map Prod.snd = xs.map Prod.snd := by
  simp [mapFst, List.map_map, Function.comp_def]

end Flapjack.WordToStackProofs
