module

public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-! CakeML concrete-syntax token carriers. HOL strings use byte lists and
`mlstring` retains its constructor-for-constructor representation. -/
namespace Flapjack.CakeParser
open Flapjack.Basis.Pure.MlString

/-- Module path carried by a qualified CakeML identifier. -/
@[hol "cakeml/semantics/tokensScript.sml" "path"]
inductive Path where
  | mod : MlString → Path → Path
  | «end»
  deriving DecidableEq, Repr

/-- Complete CakeML token datatype in source constructor order. -/
@[hol "cakeml/semantics/tokensScript.sml" "token"]
inductive Token where
  | whitespaceT : Nat → Token
  | newlineT | lexErrorT
  | hashT | lparT | rparT | starT | commaT | arrowT | dotsT | colonT | sealT
  | semicolonT | equalsT | darrowT | lbrackT | rbrackT | underbarT | lbraceT
  | barT | rbraceT | andT | andalsoT | asT | caseT | datatypeT
  | elseT | endT | eqtypeT | exceptionT | fnT | funT | handleT | ifT
  | inT | includeT | letT | localT | ofT | opT
  | openT | orelseT | raiseT | recT | sharingT | sigT | signatureT | structT
  | structureT | thenT | typeT | valT | whereT | whileT | withT | withtypeT
  | intT : Int → Token
  | hexintT : MlString → Token
  | wordT : Nat → Token
  | realT : MlString → Token
  | stringT : MlString → Token
  | charT : HolChar → Token
  | tyvarT : MlString → Token
  | alphaT : MlString → Token
  | symbolT : MlString → Token
  | longidT : Path → MlString → Token
  | ffiT : MlString → Token
  | replidT : MlString → Token
  deriving DecidableEq, Repr

/-- Exact port of HOL `destLongidT` (`tokenUtilsScript.sml:63`): the module path
    and name of a qualified identifier token. -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destLongidT_def"]
def destLongidT : Token → Option (Path × MlString)
  | .longidT path s => some (path, s)
  | _ => none

/-- Exact port of HOL `destAlphaT` (`tokenUtilsScript.sml:87`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destAlphaT_def"]
def destAlphaT : Token → Option MlString
  | .alphaT s => some s
  | _ => none

/-- Exact port of HOL `destSymbolT` (`tokenUtilsScript.sml:97`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destSymbolT_def"]
def destSymbolT : Token → Option MlString
  | .symbolT s => some s
  | _ => none

/-- Exact port of HOL `destIntT` (`tokenUtilsScript.sml:108`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destIntT_def"]
def destIntT : Token → Option Int
  | .intT i => some i
  | _ => none

/-- Exact port of HOL `destCharT` (`tokenUtilsScript.sml:113`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destCharT_def"]
def destCharT : Token → Option HolChar
  | .charT c => some c
  | _ => none

/-- Exact port of HOL `destStringT` (`tokenUtilsScript.sml:118`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destStringT_def"]
def destStringT : Token → Option MlString
  | .stringT s => some s
  | _ => none

/-- Exact port of HOL `destWordT` (`tokenUtilsScript.sml:123`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destWordT_def"]
def destWordT : Token → Option Nat
  | .wordT w => some w
  | _ => none

/-- Exact port of HOL `destFFIT` (`tokenUtilsScript.sml:128`). -/
@[hol "cakeml/semantics/tokenUtilsScript.sml" "destFFIT_def"]
def destFFIT : Token → Option MlString
  | .ffiT s => some s
  | _ => none

end Flapjack.CakeParser
