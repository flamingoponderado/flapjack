import Flapjack.AstHOL.LitOp
import Flapjack.Compiler.Backend.BackendCommon.Trace
import Flapjack.Compiler.Backend.BackendCommon.BoolTags

/-!
# `flatLangScript`: the flatLang abstract syntax

Primary counterpart of `cakeml/compiler/backend/flatLangScript.sml`: the `op`
datatype, the `ctor_id`/`type_id`/`type_group_id` abbreviations, `pat`,
`pat_bindings_def` (with its mutual `pats_bindings`), `exp`, `bool_id_def`,
`Bool_def` and `SmartIf_def`. Source `ast$op`, `lit` and `varN` are the
`Flapjack.AstHOL` carriers, `tra` is `BackendCommon.Tra`, and HOL `num` is `Nat`.
Constructor order and payloads match the source; constructor names are lower
camel case.

The pinned script declares no `dec` datatype: flatLang declarations are
expressions (`compile_decs` returns `exp list`), so there is nothing further to
port for it. The size lemmas `exp*_size` concern HOL's generated size function
and have no counterpart here.
-/

namespace Flapjack.Compiler.Backend.FlatLang

open Flapjack.AstHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- Complete original flatLang `op`: source operators via `src`, then the seven
flatLang-specific operators in source order. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
inductive Op where
  | src : AstHOL.Op → Op
  | globalVarAlloc : Nat → Op
  | globalVarInit : Nat → Op
  | globalVarLookup : Nat → Op
  | tagLenEq : Nat → Nat → Op
  | lenEq : Nat → Op
  | el : Nat → Op
  | id
  deriving DecidableEq, Repr

/-- Literal source abbreviation `ctor_id = num`. -/
@[hol "cakeml/compiler/backend/flatLangScript.sml" "ctor_id"]
abbrev CtorId := Nat

/-- Literal source abbreviation `type_id = num option`; `none` is the exception
type. -/
@[hol "cakeml/compiler/backend/flatLangScript.sml" "type_id"]
abbrev TypeId := Option Nat

/-- Literal source abbreviation
`type_group_id = (num # (ctor_id # num) list) option`. -/
@[hol "cakeml/compiler/backend/flatLangScript.sml" "type_group_id"]
abbrev TypeGroupId := Option (Nat × List (CtorId × Nat))

/-- Complete original flatLang `pat`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
inductive Pat where
  | pany
  | pvar : VarN → Pat
  | plit : Lit → Pat
  | pcon : Option (CtorId × TypeGroupId) → List Pat → Pat
  | pas : Pat → VarN → Pat
  | pref : Pat → Pat

mutual
/-- Exact HOL `pat_bindings_def` (the `pat_bindings` clauses). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def patBindings : Pat → List VarN
  | .pany => []
  | .pvar n => [n]
  | .plit _ => []
  | .pcon _ ps => patsBindings ps
  | .pas p i => patBindings p ++ [i]
  | .pref p => patBindings p

/-- Exact HOL `pat_bindings_def` (the mutual `pats_bindings` clauses); note
that the tail's bindings precede the head's, as in the source. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def patsBindings : List Pat → List VarN
  | [] => []
  | p :: ps => patsBindings ps ++ patBindings p
end

/-- Complete original flatLang `exp`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
inductive Exp where
  | raise : Tra → Exp → Exp
  | handle : Tra → Exp → List (Pat × Exp) → Exp
  | lit : Tra → Lit → Exp
  | con : Tra → Option (CtorId × TypeId) → List Exp → Exp
  | varLocal : Tra → VarN → Exp
  | fn : VarN → VarN → Exp → Exp
  | app : Tra → Op → List Exp → Exp
  | if_ : Tra → Exp → Exp → Exp → Exp
  | mat : Tra → Exp → List (Pat × Exp) → Exp
  | let_ : Tra → Option VarN → Exp → Exp → Exp
  | letrec : VarN → List (VarN × VarN × Exp) → Exp → Exp

/-- Exact HOL `bool_id_def`. -/
@[hol "cakeml/compiler/backend/flatLangScript.sml" "bool_id_def"]
def boolId : Nat := 0

/-- Exact HOL `Bool_def`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def mkBool (t : Tra) (b : Bool) : Exp :=
  .con t (some (boolToTag b, some boolId)) []

/-- Exact HOL `SmartIf_def`; the source `case` has a single specific pattern
and a catch-all, rendered as the same two-way match. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def smartIf (t : Tra) (e p q : Exp) : Exp :=
  match e with
  | .con _ (some (tag, some id)) [] =>
      if id = boolId then
        if tag = trueTag then p
        else if tag = falseTag then q
        else .if_ t e p q
      else .if_ t e p q
  | _ => .if_ t e p q

end Flapjack.Compiler.Backend.FlatLang
