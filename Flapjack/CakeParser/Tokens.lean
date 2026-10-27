import Flapjack.Basis.Pure.MlString

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

end Flapjack.CakeParser
