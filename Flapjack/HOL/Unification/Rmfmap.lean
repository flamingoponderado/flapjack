module

public import Flapjack.HOL.Transfer.Fmsp
public import Flapjack.HOL.Unification.Subst

@[expose] public section

/-! Well-formed first-order substitutions stored in sparse trees. -/
namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/compilation/rmfmapScript.sml" "swfs_def"]
def swfs {α : Type} (tree : Spt (Term α)) : Prop :=
  wfs (Flapjack.HOL.Transfer.Fmsp.sp2fm tree)

end Flapjack.HOL.Unification
