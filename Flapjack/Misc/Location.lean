import Flapjack.HolRef

/-!
# HOL `location` source positions

Counterpart of the pinned `HOL/examples/formal-languages/context-free/locationScript.sml`
carriers used by CakeML's abstract syntax (`ast$dec` and `ast$exp` store `locs`):
the position carrier `locn`, the span carrier `locs`, and the constants
`default_loc`, `start_locs` and `unknown_loc`.
-/

namespace Flapjack.Misc.Location

/-- Complete original `locn = UNKNOWNpt | EOFpt | POSN num num`; constructor order
and payloads retained. -/
@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "locn"]
inductive Locn where
  | unknownPt
  | eofPt
  | posn : Nat → Nat → Locn
  deriving DecidableEq, Repr

/-- Complete original `locs = Locs locn locn`. -/
@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "locs"]
inductive Locs where
  | locs : Locn → Locn → Locs
  deriving DecidableEq, Repr

/-- Exact HOL `default_loc_def`: `default_loc = POSN 0 0`. -/
@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "default_loc_def"]
def defaultLoc : Locn := .posn 0 0

/-- Exact HOL `start_locs_def`: `start_locs = Locs default_loc default_loc`. -/
@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "start_locs_def"]
def startLocs : Locs := .locs defaultLoc defaultLoc

/-- Exact HOL `unknown_loc_def`: `unknown_loc = Locs UNKNOWNpt UNKNOWNpt`
(HOL's local overload `unknown_locn` is `UNKNOWNpt`). -/
@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "unknown_loc_def"]
def unknownLoc : Locs := .locs .unknownPt .unknownPt

end Flapjack.Misc.Location
