import Flapjack.PanToCrepExceptionRelation

namespace Flapjack.Test.PanToCrepExceptionRelation

open Flapjack

def declarations : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .decl .one "x" (.const 0),
   .exnDecl "F" (.comb [.one, .one])]

def actualCodes : InfoMap Nat :=
  [("E", 17), ("F", 23)]

/-! A concrete fixture for Cake's `get_eids_imp_excp_rel`: the target values
are deliberately different from the source numbering; only the domain is
shared, while the source table's values are injective. -/
end Flapjack.Test.PanToCrepExceptionRelation
