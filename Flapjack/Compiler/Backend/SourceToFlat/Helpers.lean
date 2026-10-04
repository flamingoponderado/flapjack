import Flapjack.AstHOL.Syntax
import Flapjack.Compiler.Backend.FlatLang
import Flapjack.Compiler.Backend.SourceToFlat.Config

/-!
# `source_to_flatScript`: helper definitions (lines 46-340)

The source-to-flat helpers preceding `compile_exp`/`compile_decs`:
`compile_var`, `compile_pat`, `pat_tups`, `astOp_to_flatOp`,
`type_group_id_type`, `str_sep`, `join_all_names_aux`, `join_all_names`,
`om_tra`, `alloc_defs`, `make_varls`, `empty_env`, `extend_env`, `lift_env`,
`lookup_inc`, `alloc_tags1`, `alloc_tags`, `env_id_tuple` and `simple_dlet`.
Source `ast` syntax is `Flapjack.AstHOL`, flatLang is `FlatLang`, `tra` is
`BackendCommon.Tra` (`None` is `.none`), `num_map` is `Spt` with HOL
`sptree$lookup`/`insert` as `sptLookup`/`sptInsert`, and HOL `int` is `Int`.
Where HOL infers independent type variables (`type_group_id_type`,
`alloc_defs`, `alloc_tags1`, `alloc_tags`), the Lean definitions keep them as
independent type parameters (checked against the typed probe capture).
-/

namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString Flapjack.AstHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- Exact HOL `compile_var_def`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compileVar (t : Tra) : VarName → FlatLang.Exp
  | .glob _ i => .app t (.globalVarLookup i) []
  | .localName _ s => .varLocal t s

/-- Exact HOL `compile_pat_def`: `OPTION_JOIN (OPTION_MAP (nsLookup env.c) id)`
is `Option.bind`, and the type annotation of `Ptannot` is dropped. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compilePat (env : Environment) : AstHOL.Pat → FlatLang.Pat
  | .pvar v => .pvar v
  | .pany => .pany
  | .plit l => .plit l
  | .pcon id ps => .pcon (id.bind (nsLookup env.c)) (ps.map (compilePat env))
  | .pref p => .pref (compilePat env p)
  | .pas p i => .pas (compilePat env p) i
  | .ptannot p _ => compilePat env p

/-- Exact HOL `pat_tups_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "pat_tups_def"]
def patTups (t : Tra) : List VarN → List (VarN × VarName)
  | [] => []
  | x :: xs =>
      let t' := mkCons t (xs.length + 1)
      (x, .localName t' x) :: patTups t xs

/-- Exact HOL `astOp_to_flatOp_def`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def astOpToFlatOp (op : AstHOL.Op) : FlatLang.Op :=
  match op with
  | .opderef => .el 0
  | _ => .src op

/-- Exact HOL `type_group_id_type_def`; HOL infers the fully polymorphic type
`(α # (β # γ) option) option -> (α # β option) option`, kept here. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "type_group_id_type_def"]
def typeGroupIdType {α β γ : Type} : Option (α × Option (β × γ)) → Option (α × Option β)
  | none => none
  | some (cn, none) => some (cn, none)
  | some (cn, some (tyId, _)) => some (cn, some tyId)

/-- Exact HOL `str_sep_def`: the one-character string `«_»` (character code 95). -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "str_sep_def"]
def strSep : MlString := .implode [95]

/-- Exact HOL `join_all_names_aux_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "join_all_names_aux_def"]
def joinAllNamesAux : List MlString → List MlString → List MlString
  | [], ys => ys
  | x :: xs, ys =>
      match ys with
      | [] => joinAllNamesAux xs (x :: ys)
      | _ => joinAllNamesAux xs (x :: strSep :: ys)

/-- Exact HOL `join_all_names_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "join_all_names_def"]
def joinAllNames (xs : List MlString) : MlString :=
  match xs with
  | [x] => x
  | _ => MlString.concat (joinAllNamesAux xs [])

/-- Exact HOL `om_tra_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "om_tra_def"]
def omTra : Tra := .cons orphanTrace 1

/-- Exact HOL `alloc_defs_def`; the unused counter `n` is retained, and the
name type is the polymorphic `α` HOL infers. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "alloc_defs_def"]
def allocDefs {α : Type} : Nat → Nat → List α → List (α × VarName)
  | _, _, [] => []
  | n, next, x :: xs => (x, .glob omTra next) :: allocDefs (n + 1) (next + 1) xs

/-- Exact HOL `make_varls_def`; the singleton clause precedes the general cons
clause, as in HOL's clause order. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def makeVarls : Nat → Tra → Nat → List VarN → FlatLang.Exp
  | _, _, _, [] => .con .none none []
  | _, _, idx, [x] => .app .none (.globalVarInit idx) [.varLocal .none x]
  | n, _, idx, x :: xs =>
      .let_ .none none (.app .none (.globalVarInit idx) [.varLocal .none x])
        (makeVarls (n + 1) .none (idx + 1) xs)

/-- Exact HOL `empty_env_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "empty_env_def"]
def emptyEnv : Environment := { c := nsEmpty, v := nsEmpty }

/-- Exact HOL `extend_env_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "extend_env_def"]
def extendEnv (e1 e2 : Environment) : Environment :=
  { v := nsAppend e1.v e2.v, c := nsAppend e1.c e2.c }

/-- Exact HOL `lift_env_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "lift_env_def"]
def liftEnv (mn : ModN) (e : Environment) : Environment :=
  { v := nsLift mn e.v, c := nsLift mn e.c }

/-- Exact HOL `lookup_inc_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "lookup_inc_def"]
def lookupInc (i : Nat) (t : Spt Nat) : Nat × Spt Nat :=
  match sptLookup i t with
  | none => (0, sptInsert i 1 t)
  | some n => (n, sptInsert i (n + 1) t)

/-- Exact HOL `alloc_tags1_def`; HOL infers independent types for the module
names, constructor names and the (only measured) constructor argument lists. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "alloc_tags1_def"]
def allocTags1 {ModuleName Name Arg : Type} :
    List (Name × List Arg) → Namespace ModuleName Name Nat × Spt Nat × List (Nat × Nat)
  | [] => (nsEmpty, .ln, [])
  | (cn, ts) :: ctors =>
      let (ns, cids, tagList) := allocTags1 ctors
      let arity := ts.length
      let (tag, newCids) := lookupInc arity cids
      (nsBind cn tag ns, newCids, (tag, arity) :: tagList)

/-- Exact HOL `alloc_tags_def`. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "alloc_tags_def"]
def allocTags {ModuleName Name Arg TypeIdent : Type} (tid : TypeIdent)
    (ctors : List (Name × List Arg)) :
    Namespace ModuleName Name (Nat × Option (TypeIdent × List (Nat × Nat))) × Spt Nat :=
  let (conNs, cidSpt, tagList) := (allocTags1 ctors.reverse :
    Namespace ModuleName Name Nat × Spt Nat × List (Nat × Nat))
  let data := some (tid, tagList.reverse)
  (nsMap (fun tag => (tag, data)) conNs, cidSpt)

/-- Exact HOL `env_id_tuple_def`; `&` is the `Nat`-to-`Int` injection. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def envIdTuple (gen id : Nat) : FlatLang.Exp :=
  .con .none none [.lit .none (.intLit (gen : Int)), .lit .none (.intLit (id : Int))]

/-- Exact HOL `simple_dlet_def`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def simpleDlet (p : AstHOL.Pat) (e : AstHOL.Exp) : Option (VarN × Ident ModN VarN) :=
  match p with
  | .pvar pv =>
      match e with
      | .var v => some (pv, v)
      | _ => none
  | _ => none

end Flapjack.Compiler.Backend.SourceToFlat
