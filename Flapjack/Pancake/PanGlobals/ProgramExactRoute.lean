import Flapjack.Pancake.PanGlobals.CallHandlerExact

namespace Flapjack

open Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang

/-- Flapjack cross-carrier routing infrastructure, with no separate HOL
original. Assembles the literal recursive compiler clauses under the parser
name/shape invariants; it does not assume a compiler simulation. -/
theorem compileProgCakeOfExact_eq_exact [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (hshapes : GlobalContextListShapesByteRanged context) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      compileProgCakeOfExact context program =
        progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
          (progToHOL program)) := by
  apply compileProgCake.induct (cakeContextOfPass context)
    (motive := fun program => ProgByteRanged program →
      compileProgCakeOfExact context program =
        progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
          (progToHOL program)))
  all_goals intros
  all_goals try simp only [ProgByteRanged] at *
  all_goals repeat first | (rename_i h; rcases h with ⟨_, _⟩)
  case case29 =>
    rename_i program hdec hag hal hp hs h32 hb hseq hif hw hc hdc he hr hret hl hsm hrange
    cases program <;> first
      | solve_by_elim
      | simp_all [compileProgCakeOfExact, compileProgExactHOL,
      progToHOL, progOfHOL, ProgByteRanged, toStringOfBytes_ofString_of_bytes]
  all_goals first
    | apply compileProgCakeOfExact_call_global_handler_exact_bridge <;> solve_by_elim
    | apply compileProgCakeOfExact_call_global_return_no_handler_exact_bridge <;> solve_by_elim
    | apply compileProgCakeOfExact_shMemLoad_global_exact_bridge <;> solve_by_elim
    | apply compileProgCakeOfExact_global_assign_exact_bridge <;> solve_by_elim
    | simp_all [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
        compileExpRouteCake, compileExpRouteCakeArgs_eq_exact,
        toStringOfBytes_ofString_of_bytes, shapeOfHOL_shapeToHOL]

end Flapjack
