import Flapjack.Pancake.LoopToWord.ExpCarrierCodec
import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec
import Flapjack.Pancake.LoopToWord.WordContextCodec

/-!
# Width-specialized expression compiler bridge

This Flapjack-specific theorem relates the polymorphic production
`wordCompileExp` to the exact HOL `compExpHOL` through the reviewed source and
target carrier codecs. It has no HOL theorem original and does not route any
production call site through `compExpHOL`.
-/

namespace Flapjack

/-- A successful exact-source decode identifies the executable expression with
the canonical executable view of that HOL expression. -/
theorem holLoopExpToExecutable_of_executableLoopExpToHol {width : Nat}
    [NeZero width] (expression : LoopExp (BitVec width))
    (exactExpression : HolLoopExp width)
    (hdecode : executableLoopExpToHol expression = some exactExpression) :
    holLoopExpToExecutable exactExpression = expression := by
  refine LoopExp.rec
    (motive_1 := fun expression =>
      ∀ exactExpression,
        executableLoopExpToHol expression = some exactExpression →
          holLoopExpToExecutable exactExpression = expression)
    (motive_2 := fun expressions =>
      ∀ exactExpressions,
        executableLoopExpToHol.executableLoopExpListToHol expressions =
            some exactExpressions →
          exactExpressions.map holLoopExpToExecutable = expressions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression exactExpression hdecode
  · intro value exactExpression hdecode
    simp [executableLoopExpToHol] at hdecode
    cases hdecode
    simp [holLoopExpToExecutable]
  · intro name exactExpression hdecode
    simp [executableLoopExpToHol] at hdecode
    cases hdecode
    simp [holLoopExpToExecutable]
  · intro address exactExpression hdecode
    simp [executableLoopExpToHol] at hdecode
    cases hdecode
    simp [holLoopExpToExecutable]
  · intro address ih exactExpression hdecode
    cases haddress : executableLoopExpToHol address with
    | none => simp [executableLoopExpToHol, haddress] at hdecode
    | some exactAddress =>
        simp [executableLoopExpToHol, haddress] at hdecode
        cases hdecode
        simp [holLoopExpToExecutable, ih exactAddress haddress]
  · intro operator args ih exactExpression hdecode
    cases hargs : executableLoopExpToHol.executableLoopExpListToHol args with
    | none => simp [executableLoopExpToHol, hargs] at hdecode
    | some exactArgs =>
        simp [executableLoopExpToHol, hargs] at hdecode
        cases hdecode
        simp [holLoopExpToExecutable, ih exactArgs hargs]
  · intro operator args ih exactExpression hdecode
    simp at hdecode
  · intro operator left right ihLeft ihRight exactExpression hdecode
    simp at hdecode
  · intro operator left right ihLeft ihRight exactExpression hdecode
    cases hleft : executableLoopExpToHol left with
    | none => simp [executableLoopExpToHol, hleft] at hdecode
    | some exactLeft =>
        cases hright : executableLoopExpToHol right with
        | none => simp [executableLoopExpToHol, hleft, hright] at hdecode
        | some exactRight =>
            simp [executableLoopExpToHol, hleft, hright] at hdecode
            cases hdecode
            simp [holLoopExpToExecutable, ihLeft exactLeft hleft,
              ihRight exactRight hright]
  · intro exactExpression hdecode
    simp [executableLoopExpToHol] at hdecode
    cases hdecode
    simp [holLoopExpToExecutable]
  · intro exactExpression hdecode
    simp [executableLoopExpToHol] at hdecode
    cases hdecode
    simp [holLoopExpToExecutable]
  · intro exactExpressions hdecode
    simp [executableLoopExpToHol.executableLoopExpListToHol] at hdecode
    cases hdecode
    simp
  · intro head tail ihHead ihTail exactExpressions hdecode
    cases hhead : executableLoopExpToHol head with
    | none => simp [executableLoopExpToHol.executableLoopExpListToHol, hhead]
        at hdecode
    | some exactHead =>
        cases htail : executableLoopExpToHol.executableLoopExpListToHol tail with
        | none => simp [executableLoopExpToHol.executableLoopExpListToHol,
            hhead, htail] at hdecode
        | some exactTail =>
            simp [executableLoopExpToHol.executableLoopExpListToHol,
              hhead, htail] at hdecode
            cases hdecode
            simp [ihHead exactHead hhead, ihTail exactTail htail]

/-- Width-specialized exact-route expression result. Production-only
`LoopExp` constructors are rejected by the source codec. -/
def wordCompileExpThroughHOL {width : Nat} [NeZero width]
    (context : WordContext) (expression : LoopExp (BitVec width)) :
    Option (WordExp (BitVec width)) :=
  (executableLoopExpToHol expression).map fun exactExpression =>
    wordExpFromHOL
      (LoopToWord.compExpHOL (wordContextToHOLContext context) exactExpression)

/-- At a fixed width, production compilation of an expression encoded from
exact HOL syntax agrees with decoding HOL `comp_exp`. This is a bridge theorem,
not a claim that production call sites are routed through the HOL definition. -/
theorem wordCompileExp_holLoopExpToExecutable {width : Nat} [NeZero width]
    (context : WordContext) (expression : HolLoopExp width) :
    wordCompileExp context (holLoopExpToExecutable expression) =
      some (wordExpFromHOL
        (LoopToWord.compExpHOL (wordContextToHOLContext context) expression)) := by
  refine HolLoopExp.rec
    (motive_1 := fun expression =>
      wordCompileExp context (holLoopExpToExecutable expression) =
        some (wordExpFromHOL
          (LoopToWord.compExpHOL (wordContextToHOLContext context) expression)))
    (motive_2 := fun expressions =>
      wordCompileExp.wordCompileExpList context
          (expressions.map holLoopExpToExecutable) =
        some (expressions.map fun expression =>
          wordExpFromHOL
            (LoopToWord.compExpHOL (wordContextToHOLContext context) expression)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value
    simp [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL]
  · intro name
    simp only [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL, wordContextToHOLContext, Option.some.injEq]
    exact congrArg WordExp.var (findVarHOL_wordFindVar context name).symm
  · intro address
    simp [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL, wordStoreFromHOL]
  · intro address ih
    simpa [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL] using congrArg (Option.map WordExp.load) ih
  · intro operator args ih
    simp [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL, ih]
  · intro operator left right ihLeft ihRight
    simp [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL, ihLeft, ihRight]
  · simp [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL, wordStoreFromHOL]
  · simp [wordCompileExp, holLoopExpToExecutable, wordExpFromHOL,
      LoopToWord.compExpHOL, wordStoreFromHOL]
  · simp [wordCompileExp.wordCompileExpList]
  · intro head tail ihHead ihTail
    simp [wordCompileExp.wordCompileExpList, ihHead, ihTail]

/-- For any production expression accepted by the exact source codec, the
production compiler result equals the decoded exact HOL `comp_exp` result. -/
theorem wordCompileExp_eq_compExpHOL_of_codec {width : Nat} [NeZero width]
    (context : WordContext) (expression : LoopExp (BitVec width))
    (exactExpression : HolLoopExp width)
    (hdecode : executableLoopExpToHol expression = some exactExpression) :
    wordCompileExp context expression =
      some (wordExpFromHOL
        (LoopToWord.compExpHOL (wordContextToHOLContext context) exactExpression)) := by
  rw [← holLoopExpToExecutable_of_executableLoopExpToHol
    expression exactExpression hdecode]
  exact wordCompileExp_holLoopExpToExecutable context exactExpression

end Flapjack
