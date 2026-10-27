/-! Generated from pinned Pancake feature history by
`scripts/generate-cake-features.py`. This String-backed table is
CLI infrastructure, not a reviewed HOL mlstring port. -/
namespace Flapjack.CakeFeatures

/-- Whether the pinned compiler advertises a feature. -/
def enabled (name : String) : Bool := ["varshifts", "exndecls", "add_with_carry", "structs", "inline", "16bitshmem", "shapedecls", "shapechecks", "globals", "top", "staticchecks", "annots", "emptyblocks", "st", "biw", "32bitshmem", "main_return", "explore", "mep", "swcomp", "andor"].contains name

end Flapjack.CakeFeatures
