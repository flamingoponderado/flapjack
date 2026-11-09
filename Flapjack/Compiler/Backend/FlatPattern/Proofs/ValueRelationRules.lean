import Flapjack.Compiler.Backend.FlatPattern.Proofs.ValueRelation

/-! Source-shaped introduction rules for the flat-pattern value relation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.FlatProps

/-- The basic-value case of the original mutual relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel"]
theorem valueRel_basic_source (left right : Value)
    (premises : simpleBasicValRel left right ∧
      List.Forall₂ ValueRel (valueContainerXs left) (valueContainerXs right)) :
    ValueRel left right :=
  .basic premises.1 premises.2

/-- The closure case of the original mutual relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel"]
theorem valueRel_closure_source (n : Nat) (left : Environment Value)
    (name : Flapjack.AstHOL.VarN) (body : FlatLang.Exp) (right : Environment Value)
    (cfg : Config) (premises : EnvRel n left right ∧ (compileExp cfg body).1 < n) :
    ValueRel (.closure left name body) (.closure right name (compileExp cfg body).2.2) :=
  .closure premises.1 premises.2

/-- The recursive-closure case of the original mutual relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel"]
theorem valueRel_recclosure_source (n : Nat) (left : Environment Value)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (name : Flapjack.AstHOL.VarN) (right : Environment Value) (cfg : Config)
    (premises : EnvRel n left right ∧
      ∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n) :
    ValueRel (.recclosure left funs name)
      (.recclosure right (funs.map fun (f, x, body) => (f, x, (compileExp cfg body).2.2)) name) :=
  .recclosure premises.1 premises.2

/-- The environment case of the original mutual relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel"]
theorem envRel_source (n : Nat) (left right : Environment Value)
    (premise : aLookupRel (fun name => decNameToNum name < n) ValueRel left.v right.v) :
    EnvRel n left right :=
  (envRel_iff_lookup n left right).mpr premise

end Flapjack.Compiler.Backend.FlatPattern
