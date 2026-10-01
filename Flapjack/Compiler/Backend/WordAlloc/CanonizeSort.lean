import Flapjack.Basis.Pure.MlList

namespace Flapjack.WordAlloc

/-! Source audit: word_allocScript.sml:1653 resolves `sort` through ancestor
`mllist`; mllistScript.sml:287-289 aliases mergesort$mergesort_tail. The existing
native MlList helpers were compared clause by clause with the read-only HOL
checkout a390cbabd3a4521bab4ee20281e3e42933a8a3ae,
src/sort/mergesortScript.sml:101-159 (captured span SHA256
b17fc2bc0ce0c81299cffe879fe945fba21d2e69cfe7238ecc2d7a8a3f120aaf).
This audit records source provenance; it does not expand the reference checker's
external-source allowlist or claim the untagged external helpers are pinned. -/

/-- Flapjack infrastructure naming the inline comparison used by
`canonize_moves`. There is no standalone HOL declaration for this comparison,
so it is untagged. Coordinates precede priority, and every comparison is strict. -/
def canonizeMoveLess (left right : Nat × (Nat × Nat)) : Bool :=
  let (leftPriority, (leftX, leftY)) := left
  let (rightPriority, (rightX, rightY)) := right
  if leftX = rightX then
    if leftY = rightY then leftPriority < rightPriority
    else leftY < rightY
  else leftX < rightX

/-- Flapjack infrastructure applying the existing reviewed native mllist sort
to the inline comparison. This is the sorting prerequisite for the full
`canonize_moves` port, not that full equation. Normalization and grouping are
separate source clauses; production routing remains separate work. -/
def sortCanonizeMoves (moves : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  Basis.Pure.MlList.sort canonizeMoveLess moves

end Flapjack.WordAlloc
