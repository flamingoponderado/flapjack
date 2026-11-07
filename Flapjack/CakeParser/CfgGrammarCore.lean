import Flapjack.CakeParser.PegChecks
import Flapjack.CakeParser.Nonterminal
import Flapjack.Misc.Grammar

/-! Flapjack representation of CakeML context-free production patterns. The
complete generated grammar and PEG-to-CFG correspondence still need review. -/
namespace Flapjack.CakeParser.CfgGrammar
open Flapjack.Misc.Grammar Flapjack.Misc.Location Flapjack.CakeParser.PegChecks

/-- A fixed nonterminal, fixed terminal, or source grammar token class. -/
inductive Atom where
  | nonterminal : Nonterminal → Atom
  | terminal : Token → Atom
  | check : TokenCheck → Atom
  | anyAlpha | anySymbol | anyLongid

/-- Match a source grammar atom against one generic grammar symbol. -/
def matchesAtom : Atom → Symbol Token Nonterminal → Bool
  | .nonterminal expected, .nt (.inl actual) => decide (expected = actual)
  | .terminal expected, .tok actual => decide (expected = actual)
  | .check check, .tok actual => evalToken check (actual, unknownLoc)
  | .anyAlpha, .tok (.alphaT _) => true
  | .anySymbol, .tok (.symbolT _) => true
  | .anyLongid, .tok (.longidT _ _) => true
  | _, _ => false

/-- Match an entire production, retaining its original length and order. -/
def matchesProduction : List Atom → List (Symbol Token Nonterminal) → Bool
  | [], [] => true
  | atom :: atoms, symbol :: symbols => matchesAtom atom symbol && matchesProduction atoms symbols
  | _, _ => false

end Flapjack.CakeParser.CfgGrammar
