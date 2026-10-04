import Flapjack.Compiler.Backend.SourceToFlat.CompileExp

/-!
# `source_to_flat$compile_decs` and `empty_config`

Counterparts of `cakeml/compiler/backend/source_to_flatScript.sml`'s
`compile_decs_def` (342-411) and `empty_config_def` (421-428). The result is
HOL's five-tuple `(n, next, env, envs, decs)`; `sptree$insert` is `sptInsert`
and `LN` is `.ln`.
-/

namespace Flapjack.Compiler.Backend.SourceToFlat

open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendCommon

/-- Exact HOL `compile_decs_def`. HOL's singleton-list clauses are the `[d]`
cases; its final `d::ds` clause is reached only when `ds` is non-empty (every
singleton is matched earlier), so it is written `d :: d2 :: ds`. Termination is
HOL's measure, the size of the declaration list. -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "compile_decs_def"]
def compileDecs (t : List MlString) (n : Nat) (next : NextIndices) (env : Environment)
    (envs : EnvironmentGenerationStore) :
    List AstHOL.Dec →
      Nat × NextIndices × Environment × EnvironmentGenerationStore × List FlatLang.Exp
  | [.dlet _ p e] =>
      match simpleDlet p e with
      | some (pv, v) =>
          match nsLookup env.v v with
          | some (.glob t' i) =>
              (n, next, { v := alistToNs [(pv, .glob t' i)], c := nsEmpty }, envs, [])
          | _ => (n, next, { v := nsEmpty, c := nsEmpty }, envs, [])
      | none =>
          let n' := n + 4
          let xs := (AstHOL.patBindings p).reverse
          let e' := compileExp (xs ++ t) env e
          let l := xs.length
          let n'' := n' + l
          (n'', { next with vidx := next.vidx + l },
            { v := alistToNs (allocDefs n' next.vidx xs), c := nsEmpty },
            envs,
            [.mat .none e' [(compilePat env p, makeVarls 0 .none next.vidx xs)]])
  | [.dletrec _ funs] =>
      let funNames := funs.map Prod.fst
      let newEnv := nsBindList (funNames.map fun x => (x, VarName.localName .none x)) env.v
      let flatFuns := compileFuns t { env with v := newEnv } funs
      let n' := n + 1
      let env' : Environment :=
        { v := alistToNs (allocDefs n' next.vidx funNames.reverse), c := nsEmpty }
      (n' + funs.length, { next with vidx := next.vidx + funs.length }, env', envs,
        [.letrec (joinAllNames t) flatFuns (makeVarls 0 .none next.vidx funNames.reverse)])
  | [.dtype _ typeDef] =>
      let newEnv := typeDef.zipIdx.map fun (td, tid) => allocTags (next.tidx + tid) td.2.2
      (n, { next with tidx := next.tidx + typeDef.length },
        { v := nsEmpty, c := newEnv.foldl (fun ns lc => nsAppend lc.1 ns) nsEmpty },
        envs, [])
  | [.dtabbrev _ _ _ _] => (n, next, emptyEnv, envs, [])
  | [.dexn _ cn _] =>
      (n, { next with eidx := next.eidx + 1 },
        { v := nsEmpty, c := nsSing cn (next.eidx, none) }, envs, [])
  | [.dmod mn ds] =>
      let (n', next', newEnv, envs', ds') := compileDecs (mn :: t) n next env envs ds
      (n', next', liftEnv mn newEnv, envs', ds')
  | [.dlocal lds ds] =>
      let (n', next1, newEnv1, envs', lds') := compileDecs t n next env envs lds
      let (n'', next2, newEnv2, envs'', ds') :=
        compileDecs t n' next1 (extendEnv newEnv1 env) envs' ds
      (n'', next2, newEnv2, envs'', lds' ++ ds')
  | [.denv nenv] =>
      (n + 1, { next with vidx := next.vidx + 1 },
        { v := nsBind nenv (.glob .none next.vidx) nsEmpty, c := nsEmpty },
        { envs with next := envs.next + 1, envs := sptInsert envs.next env envs.envs },
        [.app .none (.globalVarInit next.vidx) [envIdTuple envs.generation envs.next]])
  | [] => (n, next, emptyEnv, envs, [])
  | d :: d2 :: ds =>
      let (n', next1, newEnv1, envs1, d') := compileDecs t n next env envs [d]
      let (n'', next2, newEnv2, envs2, ds') :=
        compileDecs t n' next1 (extendEnv newEnv1 env) envs1 (d2 :: ds)
      (n'', next2, extendEnv newEnv2 newEnv1, envs2, d' ++ ds')
termination_by decs => sizeOf decs
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have : 0 < sizeOf d2 := by cases d2 <;> simp <;> omega
       omega)

/-- Exact HOL `empty_config_def` (`source_to_flatScript.sml:421-428`). -/
@[hol "cakeml/compiler/backend/source_to_flatScript.sml" "empty_config_def"]
def emptyConfig : Config :=
  { next := { vidx := 0, tidx := 0, eidx := 0 }
    modEnv := emptyEnv
    patternCfg := FlatPattern.initConfig 0
    envs := { next := 0, envGens := .ln } }

end Flapjack.Compiler.Backend.SourceToFlat
