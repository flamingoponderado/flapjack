import Flapjack.CakeParser.LexerImpl

/-! Replay the token and location rows of `cake_lexer_probe.out`. -/
namespace Flapjack.Test.CakeLexerParity
open Flapjack.CakeParser Flapjack.CakeParser.Lexer
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def loc (r c r' c' : Nat) : Locs := .locs (.posn r c) (.posn r' c')
private def lex (s : String) := lexFuel 1000 (ofString s).explode (.posn 0 0)

#guard decide (lex "val x = 0w10; Foo.Bar.< ~12" = some [
  (.valT, loc 0 0 0 3), (.alphaT (ofString "x"), loc 0 5 0 6), (.equalsT, loc 0 8 0 9),
  (.wordT 10, loc 0 11 0 14), (.semicolonT, loc 0 15 0 16),
  (.longidT (.mod (ofString "Foo") (.mod (ofString "Bar") .end)) (ofString "<"), loc 0 18 0 25),
  (.intT (-12), loc 0 27 0 30)])

#guard decide (lex "(* a (* b *) *)\nlet x=0x2f in x end;" = some [
  (.letT, loc 1 0 1 3), (.alphaT (ofString "x"), loc 1 5 1 6), (.equalsT, loc 1 7 1 8),
  (.intT 47, loc 1 9 1 11), (.inT, loc 1 13 1 15), (.alphaT (ofString "x"), loc 1 17 1 18),
  (.endT, loc 1 20 1 23), (.semicolonT, loc 1 24 1 25)])

#guard decide (lex "\"A\\n\" #\"B\" #( f o)" = some [
  (.stringT (ofString "A\n"), loc 0 0 0 4), (.charT 66, loc 0 6 0 9),
  (.ffiT (ofString "fo"), loc 0 11 0 19)])

#guard decide ([lex "0wz", lex "*)", lex "Foo.", lex "while _ 'a", lex "\"unterminated"] = [
  some [(.lexErrorT, loc 0 0 0 0), (.alphaT (ofString "z"), loc 0 1 0 2)],
  some [(.lexErrorT, loc 0 0 0 2)], some [(.lexErrorT, loc 0 0 0 3)],
  some [(.alphaT (ofString "while"), loc 0 0 0 5), (.underbarT, loc 0 7 0 7), (.tyvarT (ofString "'a"), loc 0 9 0 10)],
  some [(.lexErrorT, loc 0 0 0 13)]])

#guard decide ((do
  let tokens ← lex "val x=1; let val y=2; in y end; val z=3"
  Flapjack.CakeParser.LexerImpl.lexAllTokensFuel 100 tokens) = some [
    [(.valT, loc 0 0 0 3), (.alphaT (ofString "x"), loc 0 5 0 6), (.equalsT, loc 0 7 0 8),
     (.intT 1, loc 0 9 0 9), (.semicolonT, loc 0 10 0 11)],
    [(.letT, loc 0 13 0 16), (.valT, loc 0 18 0 21), (.alphaT (ofString "y"), loc 0 23 0 24),
     (.equalsT, loc 0 25 0 26), (.intT 2, loc 0 27 0 27), (.semicolonT, loc 0 28 0 29),
     (.inT, loc 0 31 0 33), (.alphaT (ofString "y"), loc 0 35 0 36), (.endT, loc 0 38 0 41),
     (.semicolonT, loc 0 42 0 43)]])

#guard decide ([lex "0x", lex "0wx", lex "0w", lex "~9", lex "A.B.+", lex "\"\\255\"", lex "\"\\256\""] = [
  some [(.intT 0, loc 0 0 0 0)], some [(.wordT 0, loc 0 0 0 2)],
  some [(.lexErrorT, loc 0 0 0 0)], some [(.intT (-9), loc 0 0 0 2)],
  some [(.longidT (.mod (ofString "A") (.mod (ofString "B") .end)) (ofString "+"), loc 0 0 0 3)],
  some [(.stringT (.implode [255]), loc 0 0 0 5)],
  some [(.lexErrorT, loc 0 0 0 1), (.intT 256, loc 0 2 0 4), (.lexErrorT, loc 0 5 0 6)]])

end Flapjack.Test.CakeLexerParity
