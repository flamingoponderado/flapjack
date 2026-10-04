import Flapjack.Compiler.Backend.SourceToFlat.Helpers

/-!
# `source_to_flat$compile_exp`

Counterpart of the mutual `compile_exp_def` of
`cakeml/compiler/backend/source_to_flatScript.sml` (lines 120-228):
`compile_exp`, `compile_exps`, `compile_pes` and `compile_funs`, clause for
clause. HOL's trace `None` is `BackendCommon.Tra.none`, `OPTION_JOIN (OPTION_MAP f
o)` is `o.bind f`, `FOLDR (Let None NONE) b l` is `List.foldr`, the mlstring
literals `«»`, `«bytes»`, `«words»` and `«r»` are `MlString.ofString` of their
ASCII text, and `env with v := x` is the structure update.
-/

namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendCommon

mutual
/-- Exact HOL `compile_exp_def`, `compile_exp` clauses. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_exp_def"]
def compileExp (t : List MlString) (env : Environment) : AstHOL.Exp → FlatLang.Exp
  | .raise e => .raise .none (compileExp t env e)
  | .handle e pes => .handle .none (compileExp t env e) (compilePes t env pes)
  | .lit l => .lit .none l
  | .con cn es =>
      .con .none (cn.bind fun c => typeGroupIdType (nsLookup env.c c)) (compileExps t env es)
  | .var x =>
      match nsLookup env.v x with
      | none => .varLocal .none (ofString "")
      | some x => compileVar .none x
  | .fn x e =>
      .fn (joinAllNames t) x (compileExp t { env with v := nsBind x (.localName .none x) env.v } e)
  | .app op es =>
      if op = .aallocEmpty then
        (compileExps t env es).reverse.foldr (FlatLang.Exp.let_ .none none)
          (.app .none (.src .aalloc) [.lit .none (.intLit 0), .lit .none (.intLit 0)])
      else if op = .eval then
        .mat .none (.con .none none (compileExps t env es))
          [(.pcon none [.pany, .pany, .pany, .pany, .pvar (ofString "bytes"),
              .pvar (ofString "words")],
            .let_ .none none (.app .none (.src .eval)
                ([ofString "bytes", ofString "words"].map (.varLocal .none)))
              (.let_ .none (some (ofString "r")) (.app .none (.globalVarLookup 0) [])
                (.app .none (.el 0) [.varLocal .none (ofString "r")])))]
      else if op = .envId then
        match es with
        | [_] =>
            match compileExps t env es with
            | x :: _ => x
            | _ => .varLocal .none (ofString "")
        | _ => .app .none (.el 0) (compileExps t env es)
      else
        .app .none (astOpToFlatOp op) (compileExps t env es)
  | .log lop e1 e2 =>
      match lop with
      | .andalso => .if_ .none (compileExp t env e1) (compileExp t env e2) (FlatLang.mkBool .none false)
      | .orelse => .if_ .none (compileExp t env e1) (FlatLang.mkBool .none true) (compileExp t env e2)
  | .if_ e1 e2 e3 => .if_ .none (compileExp t env e1) (compileExp t env e2) (compileExp t env e3)
  | .mat e pes => .mat .none (compileExp t env e) (compilePes t env pes)
  | .let_ (some x) e1 e2 =>
      .let_ .none (some x) (compileExp (x :: t) env e1)
        (compileExp t { env with v := nsBind x (.localName .none x) env.v } e2)
  | .let_ none e1 e2 => .let_ .none none (compileExp t env e1) (compileExp t env e2)
  | .letrec funs e =>
      let funNames := funs.map Prod.fst
      let newEnv := nsBindList (funNames.map fun x => (x, VarName.localName .none x)) env.v
      .letrec (joinAllNames t) (compileFuns t { env with v := newEnv } funs)
        (compileExp t { env with v := newEnv } e)
  | .tannot e _ => compileExp t env e
  | .lannot e (.locs _ _) => compileExp t env e

/-- Exact HOL `compile_exp_def`, `compile_exps` clauses. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_exp_def"]
def compileExps (t : List MlString) (env : Environment) : List AstHOL.Exp → List FlatLang.Exp
  | [] => []
  | e :: es => compileExp t env e :: compileExps t env es

/-- Exact HOL `compile_exp_def`, `compile_pes` clauses. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_exp_def"]
def compilePes (t : List MlString) (env : Environment) :
    List (AstHOL.Pat × AstHOL.Exp) → List (FlatLang.Pat × FlatLang.Exp)
  | [] => []
  | (p, e) :: pes =>
      let pbs := AstHOL.patBindings p
      let pts := patTups .none pbs
      (compilePat env p, compileExp t { env with v := nsBindList pts env.v } e) ::
        compilePes t env pes

/-- Exact HOL `compile_exp_def`, `compile_funs` clauses. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_exp_def"]
def compileFuns (t : List MlString) (env : Environment) :
    List (MlString × MlString × AstHOL.Exp) → List (MlString × MlString × FlatLang.Exp)
  | [] => []
  | (f, x, e) :: funs =>
      (f, x, compileExp (f :: t) { env with v := nsBind x (.localName .none x) env.v } e) ::
        compileFuns t env funs
end

end Flapjack.Compiler.Backend.SourceToFlat
