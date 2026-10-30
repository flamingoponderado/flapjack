import Flapjack.Pancake.WordLang

/-! Syntax of the bignum generator's mini-language. -/
namespace Flapjack.Compiler.Backend.WordBignum

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "address"]
inductive Address where
  | in1 | in2 | out
  deriving DecidableEq, Repr

/-- Mini-program syntax over a word-expression carrier. The HOL type variable
is a word dimension; this generic carrier must be instantiated with a reviewed
word model before claiming source correspondence. -/
inductive Mini (α : Type) where
  | skip
  | assign (destination : Nat) (value : WordLangExpHOL α)
  | delete (registers : List Nat)
  | seq (first second : Mini α)
  | load (destination index : Nat) (address : Address)
  | store (value index : Nat)
  | ite (operator : Cmp) (left : Nat) (right : WordRegImm α) (yes no : Mini α)
  | swap
  | add (out carry left : Nat) (right carryIn : WordRegImm α)
  | sub (out carry left : Nat) (right carryIn : WordRegImm α)
  | mul (out carry left right : Nat)
  | div (out carry left right divisor : Nat)
  | loop (recursiveCalls : Bool) (live : List Nat) (body : Mini α)
  | continue
  | recurse (save names : List Nat)
  | loopBody (body : Mini α)

/-- Positive-width word instance of the source mini-language carrier. The
generic `Mini` constructor arguments match the HOL datatype in source order;
the payload word dimension is represented by `BitVec width`. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "mini"
  (words_as_type_indexed_bitvec)]
abbrev MiniHOL (width : Nat) [NeZero width] := Mini (BitVec width)

end Flapjack.Compiler.Backend.WordBignum
