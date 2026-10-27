import Flapjack.CakeParser.ParseTree

/-! First-order semantic actions of CakeML's executable PEG. -/
namespace Flapjack.CakeParser.PegActions
open ParseTree

/-- Unary actions of the original first-order PEG. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "sem_u"]
inductive Unary where
  | id
  | bindNT : Rule → Unary

/-- Binary actions of the original first-order PEG. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "sem_b"]
inductive Binary where
  | first | second | append
  | mkLinfix : Rule → Binary
  | foldEapp | foldDType | pappCtor | ebaseParen
  | bindNT0 : Rule → Binary

private def nt (n : Nonterminal) : Rule := .inl n

/-- Evaluate a unary PEG action. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_unary_def"]
def evalUnary : Unary → List ParseTree → List ParseTree
  | .id, xs => xs
  | .bindNT n, xs => [mkNode n xs]

/-- Left-associate the alternating operator and operand sequence. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "mk_linfix_fo_def"]
def mkLinfix (target : Rule) : ParseTree → List ParseTree → ParseTree
  | acc, [] | acc, [_] => acc
  | acc, op :: value :: rest => mkLinfix target (mkNode target [acc, op, value]) rest

private def foldNodes (target : Rule) (xs : List ParseTree) : List ParseTree :=
  match xs with
  | [] => []
  | x :: rest => [rest.foldl (fun acc y => mkNode target [acc, y]) (mkNode target [x])]

private def papply0 : ParseTree → List ParseTree → List ParseTree
  | _, [] => []
  | c, [x] => [mkNode (nt .nPapp) [c, x]]
  | c, x :: xs => papply0 (mkNode (nt .nPConApp) [c, x]) xs

private def papply : List ParseTree → List ParseTree
  | [] | [_] => []
  | c :: rest => papply0 (mkNode (nt .nPConApp) [c]) rest

private def pappCtor : List ParseTree → List ParseTree
  | [] => []
  | [x] => [mkNode (nt .nPapp) [mkNode (nt .nPbase) [x]]]
  | xs => papply xs

private def ebaseParen : List ParseTree → List ParseTree
  | [lp, es, rp] => [mkNode (nt .nEbase) [lp, mkNode (nt .nEseq) [es], rp]]
  | [lp, e, sep, es, rp] =>
      match sep.token with
      | none => []
      | some token =>
          if token == .commaT then
            [mkNode (nt .nEbase) [mkNode (nt .nEtuple) [lp, mkNode (nt .nElist2) [e, sep, es], rp]]]
          else [mkNode (nt .nEbase) [lp, mkNode (nt .nEseq) [e, sep, es], rp]]
  | _ => []

/-- Evaluate a binary PEG action, preserving the original argument order. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_binary_def"]
def evalBinary (action : Binary) (left right : List ParseTree) : List ParseTree :=
  match action with
  | .first => left
  | .second => right
  | .append => left ++ right
  | .mkLinfix target => match left with
      | [] => []
      | h :: _ => [mkLinfix target (mkNode target [h]) right]
  | .foldEapp => foldNodes (nt .nEapp) (left ++ right)
  | .foldDType => foldNodes (nt .nDType) (left ++ right)
  | .pappCtor => pappCtor (left ++ right)
  | .ebaseParen => ebaseParen left
  | .bindNT0 target => [mkNode target (left ++ right)]

end Flapjack.CakeParser.PegActions
