import Flapjack.Compiler.Backend.FlatElim.Proofs.ValueGlobals

/-! Constructor equations for the flat elimination dynamic-Eval analysis. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.AstHOL Flapjack.Compiler.Backend

private theorem hasEvalList_eq_any (es : List FlatLang.Exp) :
    hasEvalList es = es.any hasEval := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [hasEvalList, ih]

private theorem hasEvalPats_eq_any (pes : List (FlatLang.Pat × FlatLang.Exp)) :
    hasEvalPats pes = (pes.map Prod.snd).any hasEval := by
  induction pes with
  | nil => rfl
  | cons pe pes ih => cases pe; simp [hasEvalPats, ih]

/-- The original local constructor equations, including the complete list
traversals in each expression case. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "has_Eval_def"]
theorem hasEval_cases (htrace : BackendCommon.Tra) (e : FlatLang.Exp)
    (pes : List (FlatLang.Pat × FlatLang.Exp)) (ctrace : BackendCommon.Tra)
    (c : Option (FlatLang.CtorId × FlatLang.TypeId)) (es : List FlatLang.Exp)
    (ftrace farg : VarN) (t : BackendCommon.Tra) (op : FlatLang.Op)
    (e1 e2 e3 : FlatLang.Exp) (ltrace : BackendCommon.Tra) (opt : Option VarN)
    (rtrace : VarN) (funs : List (VarN × VarN × FlatLang.Exp))
    (xtrace vtrace : BackendCommon.Tra) (varnum : VarN) (littrace : BackendCommon.Tra) (v : Lit) :
    (hasEval (.handle htrace e pes) = (hasEval e || (pes.map Prod.snd).any hasEval)) ∧
    (hasEval (.con ctrace c es) = es.any hasEval) ∧
    (hasEval (.fn ftrace farg e) = hasEval e) ∧
    (hasEval (.app t op es) = (decide (op = .src .eval) || es.any hasEval)) ∧
    (hasEval (.if_ t e1 e2 e3) = (hasEval e1 || (hasEval e2 || hasEval e3))) ∧
    (hasEval (.mat t e pes) = (hasEval e || (pes.map Prod.snd).any hasEval)) ∧
    (hasEval (.let_ ltrace opt e1 e2) = (hasEval e1 || hasEval e2)) ∧
    (hasEval (.letrec rtrace funs e) = (hasEval e || (funs.map (fun (_, _, body) => body)).any hasEval)) ∧
    (hasEval (.raise xtrace e) = hasEval e) ∧
    (hasEval (.varLocal vtrace varnum) = false) ∧
    (hasEval (.lit littrace v) = false) := by
  cases op <;> simp [hasEval, hasEvalList_eq_any, hasEvalPats_eq_any, hasEvalFuns_eq_map, BEq.beq,
    Bool.or_assoc]

end Flapjack.Compiler.Backend.FlatElim
