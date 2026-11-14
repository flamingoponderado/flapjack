module

public import Flapjack.CakeParser.ParseTree
public import Flapjack.Misc.Grammar

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

/-- Evaluate a unary PEG action.

    Tag withdrawn (task 147): HOL `eval_unary_def` applies `eval_unary` to `(α, MMLnonT, locs)
    parsetree list` with the terminal type `α` generic, while Lean's `ParseTree` fixes the terminal
    type to CakeML's `Token`. The clauses are HOL's, but a specialised instance is not an exact
    port; a faithful port needs a parsetree carrier generic in the terminal type. The exact
    generic port is `evalUnaryHOL` below. -/
def evalUnary : Unary → List ParseTree → List ParseTree
  | .id, xs => xs
  | .bindNT n, xs => [mkNode n xs]

/-- Left-associate the alternating operator and operand sequence.

    Tag withdrawn (task 147): HOL `mk_linfix_fo_def` is generic in the terminal type `α` and the
    rule-index type `β` of `(α, β, locs) parsetree` and `β + num`, while Lean's `ParseTree`/`Rule`
    fix them to `Token` and `Sum Nonterminal Nat`. The clauses are HOL's, but a specialised
    instance is not an exact port; a faithful port needs a parsetree carrier generic in both
    type parameters. The exact generic port is `mkLinfixHOL` below. -/
def mkLinfix (target : Rule) : ParseTree → List ParseTree → ParseTree
  | acc, [] | acc, [_] => acc
  | acc, op :: value :: rest => mkLinfix target (mkNode target [acc, op, value]) rest

/-- Exact port of HOL `mkNd_fo_def`: build a node carrying the merged location
    of its children. Generic in HOL's terminal type `α` and rule-index type `β`;
    `ptree_list_loc` fixes the location type to HOL's `locs`. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "mkNd_fo_def"]
def mkNdHOL {α β : Type} (nt : Sum β Nat)
    (children : List (Misc.Grammar.ParseTree α β Misc.Location.Locs)) :
    Misc.Grammar.ParseTree α β Misc.Location.Locs :=
  .node (nt, Misc.Grammar.treeListLoc children) children

/-- Exact port of HOL `eval_unary_def` over the generic grammar tree: the
    terminal type `α` is generic while the nonterminal type is `MMLnonT` and
    the location type is `locs`. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "eval_unary_def"]
def evalUnaryHOL {α : Type} :
    Unary → List (Misc.Grammar.ParseTree α Nonterminal Misc.Location.Locs) →
      List (Misc.Grammar.ParseTree α Nonterminal Misc.Location.Locs)
  | .id, v => v
  | .bindNT nt, v => [.node (nt, Misc.Grammar.treeListLoc v) v]

/-- Exact port of HOL `mk_linfix_fo_def`, generic in the terminal type `α` and
    the rule-index type `β` of HOL's `(α, β, locs) parsetree`. -/
@[hol "cakeml/compiler/parsing/pegexec_cml_foScript.sml" "mk_linfix_fo_def"]
def mkLinfixHOL {α β : Type} (target : Sum β Nat) :
    Misc.Grammar.ParseTree α β Misc.Location.Locs →
      List (Misc.Grammar.ParseTree α β Misc.Location.Locs) →
        Misc.Grammar.ParseTree α β Misc.Location.Locs
  | acc, [] => acc
  | acc, [_] => acc
  | acc, op :: value :: rest =>
      mkLinfixHOL target (mkNdHOL target [acc, op, value]) rest

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
