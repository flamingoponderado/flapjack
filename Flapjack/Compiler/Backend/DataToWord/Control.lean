import Flapjack.Compiler.Backend.DataLang.Syntax
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Variables
import Flapjack.Pancake.WordLang

/-! Checked control-flow cases of data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Flapjack's partial control-flow traversal. Unsupported allocation,
assignment and thunk cases return `none`; this is not HOL's total `comp`. -/
def compileControl? {width : Nat} [NeZero width] (conf : Config) (secn : Nat) :
    Nat → DataLang.Prog → Option (WordLangProgHOL (BitVec width) × Nat)
  | l, .skip => some (.skip, l)
  | l, .tick => some (.tick, l)
  | l, .raise n => some (.raise (adjustVar n), l)
  | l, .return ns => some (.return 0 (ns.map adjustVar), l)
  | l, .move dst src => some (.move 0 [(adjustVar dst, adjustVar src)], l)
  | l, .seq x y => do
      let (x, l) ← compileControl? conf secn l x
      let (y, l) ← compileControl? conf secn l y
      pure (.seq x y, l)
  | l, .ifThenElse n x y => do
      let (x, l) ← compileControl? conf secn l x
      let (y, l) ← compileControl? conf secn l y
      pure (.ite .equal (adjustVar n) (.imm 18) x y, l)
  | l, .call none target args _ => some (.call none target (0 :: args.map adjustVar) none, l)
  | l, .call (some (ns, names)) target args none =>
      some (.call (some (ns.map adjustVar, adjustSets names, .skip, secn, l))
        target (args.map adjustVar) none, l + 1)
  | l, .call (some (ns, names)) target args (some (n, handler)) => do
      let (handler, next) ← compileControl? conf secn (l + 2) handler
      pure (.call (some (ns.map adjustVar, adjustSets names, .skip, secn, l))
        target (args.map adjustVar) (some (adjustVar n, handler, secn, l + 1)), next)
  | _, _ => none

end Flapjack.Compiler.Backend.DataToWord
