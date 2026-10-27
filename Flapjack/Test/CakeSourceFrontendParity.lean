import Flapjack.CakeParser.Frontend

/-! Parse source bytes end to end and compare with the original HOL lexer,
PEG, and top-level conversion captures. -/
namespace Flapjack.Test.CakeSourceFrontendParity
open Flapjack.CakeParser.Frontend Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def loc (a b : Nat) : Locs := .locs (.posn 0 a) (.posn 0 b)

#guard match parseSourceFuel 500 500 (ofString "").explode with
  | .success [] => true
  | _ => false

#guard match parseSourceFuel 500 500 (ofString "val x = 1;").explode with
  | .success [.dlet span (.pvar name) (.lannot (.lit (.intLit 1)) valueSpan)] =>
      name == ofString "x" && span == loc 0 11 && valueSpan == loc 11 11
  | _ => false

#guard match parseSourceFuel 500 500 (ofString "datatype t = A | B;").explode with
  | .success [.dtype span [([], name, [(a, []), (b, [])])]] =>
      span == .locs (.posn 0 0) .unknownPt && name == ofString "t" && a == ofString "A" && b == ofString "B"
  | _ => false

#guard match parseSourceFuel 500 500 (ofString "structure M = struct val x = 1; end;").explode with
  | .success [.dmod name [.dlet span (.pvar x) (.lannot (.lit (.intLit 1)) valueSpan)]] =>
      name == ofString "M" && x == ofString "x" && span == loc 25 36 && valueSpan == loc 36 36
  | _ => false

#guard match parseSourceFuel 500 500 (ofString "1;").explode with
  | .success [.dlet span (.pvar name) (.lannot (.lit (.intLit 1)) valueSpan)] =>
      name == ofString "it" && span == .locs (.posn 0 0) .unknownPt && valueSpan == loc 0 0
  | _ => false

end Flapjack.Test.CakeSourceFrontendParity
