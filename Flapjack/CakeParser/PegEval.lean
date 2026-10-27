import Flapjack.CakeParser.PegGrammar

/-! A bounded direct interpreter for successful CakeML PEG parses. This is
Flapjack infrastructure: its fuel counts recursive calls and it does not
implement the original machine's error locations or diagnostic stack. -/
namespace Flapjack.CakeParser.PegEval
open Flapjack.Misc.Location PegActions PegChecks PegSyntax PegGrammar

@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_tok_map_def"]
def evalTokenMap (m : TokenMap) (input : Token × Locs) : List ParseTree :=
  let leaf := ParseTree.leaf (.inr input.1) input.2
  match m with
  | .leaf => [leaf]
  | .empty => []
  | .bindNT n => [.node n input.2 [leaf]]

inductive Result where
  | exhausted
  | failure
  | success : List ParseTree → List (Token × Locs) → Result

/-- Evaluate grammar expressions with bounded recursion. Failure backtracks to
its caller's input. Exhaustion is distinguished from ordinary parse failure. -/
def eval : Nat → PegExpr → List (Token × Locs) → Result
  | 0, _, _ => .exhausted
  | fuel + 1, e, input =>
    match e with
    | .empty v => .success v input
    | .any m => match input with
      | [] => .failure
      | x :: xs => .success (evalTokenMap m x) xs
    | .token check m => match input with
      | [] => .failure
      | x :: xs => if evalToken check x then .success (evalTokenMap m x) xs else .failure
    | .nt rule action => match ntRule rule with
      | none => .exhausted
      | some e => match eval fuel e input with
        | .success values rest => .success (evalUnary action values) rest
        | .failure => .failure
        | .exhausted => .exhausted
    | .seq first second action => match eval fuel first input with
      | .success left rest => match eval fuel second rest with
        | .success right rest' => .success (evalBinary action left right) rest'
        | .failure => .failure
        | .exhausted => .exhausted
      | .failure => .failure
      | .exhausted => .exhausted
    | .choice first second => match eval fuel first input with
      | .failure => eval fuel second input
      | result => result
    | .repeat e => match eval fuel e input with
      | .failure => .success [] input
      | .exhausted => .exhausted
      | .success values rest => match eval fuel (.repeat e) rest with
        | .success values' rest' => .success (values ++ values') rest'
        | .failure => .failure
        | .exhausted => .exhausted
    | .not e values => match eval fuel e input with
      | .success _ _ => .failure
      | .failure => .success values input
      | .exhausted => .exhausted
    | .error _ => .failure

end Flapjack.CakeParser.PegEval
