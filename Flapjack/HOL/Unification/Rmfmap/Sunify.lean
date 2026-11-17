module

public import Flapjack.HOL.Transfer.Fmsp.Inverse
public import Flapjack.HOL.Unification.UnifDef.Choice

@[expose] public section

/-! Sparse-tree model of HOL's specified first-order unifier. -/
namespace Flapjack.HOL.Unification
open Flapjack.HOL.Transfer.Fmsp

/-- Select a source-specification unifier and convert a successful map to a
    sparse tree. This is untagged because agreement with HOL's selected
    unifier outside the well-formedness guard is not established. -/
noncomputable def sunifyModel {α : Type} (s : Spt (Term α)) (a b : Term α) :
    Option (Spt (Term α)) :=
  (specifiedUnify (sp2fm s) a b).map fm2sp

end Flapjack.HOL.Unification
