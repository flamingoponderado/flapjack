import Flapjack.Compiler.Inference.Infer
import Flapjack.Compiler.Inference.Unify
import Flapjack.AstHOL.Syntax

/-! Bounded executable inference infrastructure. The result distinguishes
unsupported forms from rejected inputs and resource exhaustion. It does not
yet preserve HOL's diagnostic strings or error-state result. -/
namespace Flapjack.Compiler.Inference.Infer.Core
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL
open Flapjack.Compiler.Inference.Unify

inductive Error where
  | exhausted | unsupported | mismatch | undefinedName | invalidPattern | valueRestriction
  | typeMismatch : InferT → InferT → Error
  | typeMismatchNames : List (Nat × MlString) → InferT → InferT → Error
  | duplicatePatternVariable : MlString → Error
  | duplicateDefinitionVariable : MlString → Error
  | duplicateFunctionName : MlString → Bool → Error
  | duplicateAbbreviationVariable : MlString → MlString → Error
  | constructorArity : Ident MlString MlString → Nat → Nat → Error
  | typeConstructorArity : Ident MlString MlString → Nat → Nat → Error
  | duplicateTypeName : MlString → Error
  | duplicateConstructor : MlString → MlString → Error
  | duplicateTypeVariable : MlString → MlString → Error
  | undefinedVariable : Ident MlString MlString → Error
  | undefinedConstructor : Ident MlString MlString → Error
  | undefinedTypeConstructor : Ident MlString MlString → Error
  | located : Flapjack.Misc.Location.Locs → Error → Error
  deriving Repr

abbrev M (α : Type) := StateT State (Except Error) α

private def fail (e : Error) : M α := fun _ => .error e

private def firstRepeatedName : List MlString → Option MlString
  | [] => none
  | name :: rest => if name ∈ rest then some name else firstRepeatedName rest

/-- Preserve the innermost source location for errors that carry enough
information for original-style rendering. Other error classes remain unchanged. -/
private def typeNamesFuel : Nat → MlString → Namespace MlString MlString
    (List MlString × TypeSystemHOL.SemanticT) → List (Nat × MlString)
  | 0, _, _ => []
  | fuel + 1, path, .bind entries modules =>
    entries.filterMap (fun (name, _, typ) => match typ with
      | .app _ id => some (id, MlString.concat [path, name])
      | _ => none) ++
    modules.flatMap (fun (name, env) =>
      typeNamesFuel fuel (MlString.concat [path, name, ofString "."]) env)

private def withLoc (loc : Flapjack.Misc.Location.Locs) (env : Env) (action : M α) : M α := fun state =>
  match action state with
  | .error .valueRestriction => .error (.located loc .valueRestriction)
  | .error (.undefinedVariable name) => .error (.located loc (.undefinedVariable name))
  | .error (.undefinedConstructor name) => .error (.located loc (.undefinedConstructor name))
  | .error (.undefinedTypeConstructor name) => .error (.located loc (.undefinedTypeConstructor name))
  | .error (.typeMismatch left right) => .error (.located loc
      (.typeMismatchNames (typeNamesFuel 10000 (ofString "") env.infT) left right))
  | .error (.duplicatePatternVariable name) => .error (.located loc (.duplicatePatternVariable name))
  | .error (.duplicateDefinitionVariable name) => .error (.located loc (.duplicateDefinitionVariable name))
  | .error (.duplicateFunctionName name isLocal) => .error (.located loc (.duplicateFunctionName name isLocal))
  | .error (.duplicateAbbreviationVariable name typ) => .error (.located loc (.duplicateAbbreviationVariable name typ))
  | .error (.constructorArity name actual expected) => .error (.located loc (.constructorArity name actual expected))
  | .error (.typeConstructorArity name actual expected) => .error (.located loc (.typeConstructorArity name actual expected))
  | .error (.duplicateTypeName name) => .error (.located loc (.duplicateTypeName name))
  | .error (.duplicateConstructor name typ) => .error (.located loc (.duplicateConstructor name typ))
  | .error (.duplicateTypeVariable name typ) => .error (.located loc (.duplicateTypeVariable name typ))
  | other => other
private def fresh : M InferT := do
  let s ← get
  let (t, s) := freshUvar s
  set s
  return t

private def freshMany (n : Nat) : M (List InferT) := do
  let s ← get
  let (ts, s) := freshUvars n s
  set s
  return ts

private def constrain (fuel : Nat) (a b : InferT) : M Unit := do
  let s ← get
  match unifyFuel fuel s.subst a b with
  | none => fail .exhausted
  | some none =>
    match walkStarFuel fuel s.subst a, walkStarFuel fuel s.subst b with
    | some left, some right => fail (.typeMismatch left right)
    | _, _ => fail .mismatch
  | some (some subst) => set { s with subst }

private def constrainMany (fuel : Nat) : List InferT → List InferT → M Unit
  | [], [] => pure ()
  | x :: xs, y :: ys => do
    constrain fuel x y
    constrainMany fuel xs ys
  | _, _ => fail .mismatch

private def litType : Lit → Option InferT
  | .intLit _ => some (.app [] 5)
  | .char _ => some (.app [] 2)
  | .strLit _ => some (.app [] 8)
  | .word8 _ => some (.app [] 12)
  | .word64 _ => some (.app [] 11)
  | .float64 _ => some (.app [] 14)

private def ctorInfo (env : Env) (name : Ident MlString MlString) : M (List MlString × List TypeSystemHOL.SemanticT × Nat) :=
  match nsLookup env.infC name with
  | none => fail (.undefinedConstructor name)
  | some x => pure x


mutual
private def semanticSubst (s : List (MlString × TypeSystemHOL.SemanticT)) :
    TypeSystemHOL.SemanticT → TypeSystemHOL.SemanticT
  | .var v => (s.lookup v).getD (.var v)
  | .varDb n => .varDb n
  | .app ts name => .app (semanticSubstList s ts) name
termination_by t => sizeOf t

private def semanticSubstList (s : List (MlString × TypeSystemHOL.SemanticT)) :
    List TypeSystemHOL.SemanticT → List TypeSystemHOL.SemanticT
  | [] => []
  | x :: xs => semanticSubst s x :: semanticSubstList s xs
termination_by ts => sizeOf ts
end

mutual
private def annotationWorker : Nat → Env → List MlString → AstT → Except Error TypeSystemHOL.SemanticT
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, env, free, typ => do
    match typ with
    | .atvar v => if v ∈ free then .ok (.var v) else .error .mismatch
    | .attup ts => return .app (← annotationsWorker fuel env free ts) 9
    | .atfun a b => return .app [← annotationWorker fuel env free a, ← annotationWorker fuel env free b] 4
    | .atapp ts name =>
      let ts ← annotationsWorker fuel env free ts
      match nsLookup env.infT name with
      | none => .error (.undefinedTypeConstructor name)
      | some (params, body) =>
        if params.length != ts.length then .error (.typeConstructorArity name ts.length params.length)
        else .ok (semanticSubst (List.zip params ts) body)

private def annotationsWorker : Nat → Env → List MlString → List AstT → Except Error (List TypeSystemHOL.SemanticT)
  | 0, _, _, _ => .error .exhausted
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, env, free, t :: ts => do
    let t ← annotationWorker fuel env free t
    let ts ← annotationsWorker fuel env free ts
    return t :: ts
end

private def annotation (fuel : Nat) (env : Env) (t : AstT) : M InferT := do
  match annotationWorker fuel env [] t with
  | .error e => fail e
  | .ok t => pure (inferTypeSubst [] t)

mutual
private def inferPatWorker : Nat → Nat → Env → Pat → M (InferT × List (MlString × InferT))
  | 0, _, _, _ => fail .exhausted
  | fuel + 1, unifFuel, env, p => do
    match p with
    | .pvar v => let t ← fresh; return (t, [(v, t)])
    | .pany => let t ← fresh; return (t, [])
    | .plit (.float64 _) => fail .invalidPattern
    | .plit lit => match litType lit with
      | some t => return (t, [])
      | none => fail .unsupported
    | .pcon none ps =>
      let (ts, bindings) ← inferPatsWorker fuel unifFuel env ps
      return (.app ts 9, bindings)
    | .pcon (some name) ps =>
      let (vars, expected, typeId) ← ctorInfo env name
      let (actual, bindings) ← inferPatsWorker fuel unifFuel env ps
      let freshVars ← freshMany vars.length
      if actual.length != expected.length then fail (.constructorArity name actual.length expected.length) else
      constrainMany unifFuel actual (expected.map (inferTypeSubst (List.zip vars freshVars)))
      return (.app freshVars typeId, bindings)
    | .pref p =>
      let (t, bindings) ← inferPatWorker fuel unifFuel env p
      return (.app [t] 7, bindings)
    | .pas p v =>
      let (t, bindings) ← inferPatWorker fuel unifFuel env p
      return (t, bindings ++ [(v, t)])
    | .ptannot p typ =>
      let (t, bindings) ← inferPatWorker fuel unifFuel env p
      let typ ← annotation fuel env typ
      constrain unifFuel t typ
      return (t, bindings)

private def inferPatsWorker : Nat → Nat → Env → List Pat → M (List InferT × List (MlString × InferT))
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure ([], [])
  | fuel + 1, unifFuel, env, p :: ps => do
    let (t, bindings) ← inferPatWorker fuel unifFuel env p
    let (ts, rest) ← inferPatsWorker fuel unifFuel env ps
    return (t :: ts, rest ++ bindings)
end

/-- Infer a pattern with explicit bounds. HOL's error messages and exact error-state behavior are not yet implemented. -/
def inferPatternFuel (fuel unifFuel : Nat) (env : Env) (p : Pat) (s : State) :
    Except Error ((InferT × List (MlString × InferT)) × State) :=
  (inferPatWorker fuel unifFuel env p) s


private def primNum : PrimType → Nat
  | .boolT => 1 | .intT => 5 | .charT => 2 | .strT => 8
  | .wordT .w8 => 12 | .wordT .w64 => 11 | .float64T => 14

private def arithArity (a : Arith) : PrimType → Option Nat
  | .intT => if a ∈ [Arith.add, .sub, .mul, .div, .mod] then some 2 else none
  | .float64T => if a ∈ [Arith.abs, .neg, .sqrt] then some 1
    else if a ∈ [Arith.add, .sub, .mul, .div] then some 2
    else if a == .fma then some 3 else none
  | .wordT _ => if a ∈ [Arith.add, .sub, .and, .or, .xor] then some 2 else none
  | .boolT => if a == .not then some 1 else none
  | _ => none

private def supportedTest (test : Test) (typ : PrimType) : Bool :=
  match test with
  | .equal => true
  | .compare _ => typ ∈ [PrimType.intT, .charT, .wordT .w8, .float64T, .strT]
  | .altCompare _ => typ == .strT

private def supportedConversion (a b : PrimType) : Bool :=
  match a, b with
  | .wordT _, .intT | .intT, .wordT _ | .charT, .intT | .intT, .charT
  | .charT, .wordT .w8 | .wordT .w8, .charT | .float64T, .wordT .w64
  | .wordT .w64, .float64T => true
  | _, _ => false

private def simpleOp : Op → Option (List InferT × InferT)
  | .arith a typ => do
    let n ← arithArity a typ
    let t := InferT.app [] (primNum typ)
    some (List.replicate n t, t)
  | .fromTo a b =>
    if supportedConversion a b then some ([.app [] (primNum a)], .app [] (primNum b)) else none
  | .test test typ =>
    if supportedTest test typ then some ([.app [] (primNum typ), .app [] (primNum typ)], .app [] 1) else none
  | .shift size _ _ =>
    let n := match size with | .w8 => 12 | .w64 => 11
    some ([.app [] n], .app [] n)
  | .aw8alloc => some ([.app [] 5, .app [] 12], .app [] 13)
  | .aw8sub => some ([.app [] 13, .app [] 5], .app [] 12)
  | .aw8length => some ([.app [] 13], .app [] 5)
  | .aw8update => some ([.app [] 13, .app [] 5, .app [] 12], .app [] 9)
  | .copyStrStr => some ([.app [] 8, .app [] 5, .app [] 5], .app [] 8)
  | .copyStrAw8 => some ([.app [] 8, .app [] 5, .app [] 5, .app [] 13, .app [] 5], .app [] 9)
  | .copyAw8Str => some ([.app [] 13, .app [] 5, .app [] 5], .app [] 8)
  | .copyAw8Aw8 => some ([.app [] 13, .app [] 5, .app [] 5, .app [] 13, .app [] 5], .app [] 9)
  | .strsub => some ([.app [] 8, .app [] 5], .app [] 2)
  | .strlen => some ([.app [] 8], .app [] 5)
  | .configGC => some ([.app [] 5, .app [] 5], .app [] 9)
  | .ffi _ => some ([.app [] 8, .app [] 13], .app [] 9)
  | .implode => some ([.app [.app [] 2] 6], .app [] 8)
  | .explode => some ([.app [] 8], .app [.app [] 2] 6)
  | .strcat => some ([.app [.app [] 8] 6], .app [] 8)
  | _ => none

private def inferOp (fuel : Nat) (op : Op) (ts : List InferT) : M InferT := do
  if let some (args, result) := simpleOp op then
    constrainMany fuel ts args
    return result
  match op, ts with
  | .opapp, [f, x] =>
    let r ← fresh
    constrain fuel f (.app [x, r] 4)
    return r
  | .equality, [x, y] =>
    constrain fuel x y
    return .app [] 1
  | .opref, [x] => return .app [x] 7
  | .opderef, [x] =>
    let r ← fresh
    constrain fuel x (.app [r] 7)
    return r
  | .opassign, [x, y] =>
    constrain fuel x (.app [y] 7)
    return .app [] 9
  | .vfromList, [x] =>
    let t ← fresh
    constrain fuel x (.app [t] 6)
    return .app [t] 10
  | .vsub, [xs, index] =>
    let t ← fresh
    constrain fuel xs (.app [t] 10)
    constrain fuel index (.app [] 5)
    return t
  | .vlength, [xs] =>
    let t ← fresh
    constrain fuel xs (.app [t] 10)
    return .app [] 5
  | .aalloc, [size, value] =>
    constrain fuel size (.app [] 5)
    return .app [value] 0
  | .aallocEmpty, [unit] =>
    let t ← fresh
    constrain fuel unit (.app [] 9)
    return .app [t] 0
  | .asub, [xs, index] =>
    let t ← fresh
    constrain fuel xs (.app [t] 0)
    constrain fuel index (.app [] 5)
    return t
  | .alength, [xs] =>
    let t ← fresh
    constrain fuel xs (.app [t] 0)
    return .app [] 5
  | .aupdate, [xs, index, value] =>
    constrain fuel xs (.app [value] 0)
    constrain fuel index (.app [] 5)
    return .app [] 9
  | .listAppend, [x, y] =>
    let r ← fresh
    constrain fuel x (.app [r] 6)
    constrain fuel y (.app [r] 6)
    return .app [r] 6
  | .ffi _, [x, y] =>
    constrain fuel x (.app [] 8)
    constrain fuel y (.app [] 13)
    return .app [] 9
  | _, _ => fail .unsupported

private def bindVars (env : Env) (bindings : List (MlString × InferT)) : Env :=
  { env with infV := nsAppend (alistToNs (bindings.map (fun (name, t) => (name, (0, t))))) env.infV }

mutual
private def inferExprWorker : Nat → Nat → Env → Exp → M InferT
  | 0, _, _, _ => fail .exhausted
  | fuel + 1, unifFuel, env, expr => do
    match expr with
    | .lit lit => match litType lit with
      | some t => return t
      | none => fail .unsupported
    | .var name => match nsLookup env.infV name with
      | none => fail (.undefinedVariable name)
      | some (n, t) =>
        let freshVars ← freshMany n
        return inferDeBruijnSubst freshVars t
    | .con none es =>
      let ts ← inferExprsWorker fuel unifFuel env es
      return .app ts 9
    | .con (some name) es =>
      let (vars, expected, typeId) ← ctorInfo env name
      let actual ← inferExprsWorker fuel unifFuel env es
      let freshVars ← freshMany vars.length
      if actual.length != expected.length then fail (.constructorArity name actual.length expected.length) else
      constrainMany unifFuel actual (expected.map (inferTypeSubst (List.zip vars freshVars)))
      return .app freshVars typeId
    | .fn v body =>
      let arg ← fresh
      let body ← inferExprWorker fuel unifFuel (bindVars env [(v, arg)]) body
      return .app [arg, body] 4
    | .app op es =>
      let ts ← inferExprsWorker fuel unifFuel env es
      inferOp unifFuel op ts
    | .log _ a b =>
      let a ← inferExprWorker fuel unifFuel env a
      let b ← inferExprWorker fuel unifFuel env b
      constrain unifFuel a (.app [] 1)
      constrain unifFuel b (.app [] 1)
      return .app [] 1
    | .if_ guard yes no =>
      let guard ← inferExprWorker fuel unifFuel env guard
      constrain unifFuel guard (.app [] 1)
      let yes ← inferExprWorker fuel unifFuel env yes
      let no ← inferExprWorker fuel unifFuel env no
      constrain unifFuel yes no
      return yes
    | .raise e =>
      let t ← inferExprWorker fuel unifFuel env e
      constrain unifFuel t (.app [] 3)
      fresh
    | .handle e clauses =>
      if clauses.isEmpty then fail .invalidPattern else
      let t ← inferExprWorker fuel unifFuel env e
      inferClausesWorker fuel unifFuel env clauses (.app [] 3) t
      return t
    | .mat e clauses =>
      if clauses.isEmpty then fail .invalidPattern else
      let t ← inferExprWorker fuel unifFuel env e
      let result ← fresh
      inferClausesWorker fuel unifFuel env clauses t result
      return result
    | .let_ name value body =>
      let t ← inferExprWorker fuel unifFuel env value
      let env := match name with | none => env | some n => bindVars env [(n, t)]
      inferExprWorker fuel unifFuel env body
    | .lannot body loc => withLoc loc env (inferExprWorker fuel unifFuel env body)
    | .tannot body typ =>
      let t ← inferExprWorker fuel unifFuel env body
      let typ ← annotation fuel env typ
      constrain unifFuel t typ
      return t
    | .letrec funs body =>
      let names := funs.map (fun (name, _, _) => name)
      if let some name := firstRepeatedName names then fail (.duplicateFunctionName name true) else
      let vars ← freshMany funs.length
      let env := bindVars env (List.zip names vars)
      let types ← inferFunsWorker fuel unifFuel env funs
      constrainMany unifFuel vars types
      inferExprWorker fuel unifFuel env body


private def inferFunsWorker : Nat → Nat → Env → List (MlString × MlString × Exp) → M (List InferT)
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure []
  | fuel + 1, unifFuel, env, (_, arg, body) :: rest => do
    let argType ← fresh
    let bodyType ← inferExprWorker fuel unifFuel (bindVars env [(arg, argType)]) body
    let rest ← inferFunsWorker fuel unifFuel env rest
    return .app [argType, bodyType] 4 :: rest

private def inferExprsWorker : Nat → Nat → Env → List Exp → M (List InferT)
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure []
  | fuel + 1, unifFuel, env, e :: es => do
    let t ← inferExprWorker fuel unifFuel env e
    let ts ← inferExprsWorker fuel unifFuel env es
    return t :: ts

private def inferClausesWorker : Nat → Nat → Env → List (Pat × Exp) → InferT → InferT → M Unit
  | 0, _, _, _, _, _ => fail .exhausted
  | _ + 1, _, _, [], _, _ => pure ()
  | fuel + 1, unifFuel, env, (p, e) :: ps, input, output => do
    let (pType, bindings) ← inferPatWorker fuel unifFuel env p
    if let some name := firstRepeatedName (bindings.map Prod.fst) then fail (.duplicatePatternVariable name) else
    constrain unifFuel input pType
    let eType ← inferExprWorker fuel unifFuel (bindVars env bindings) e
    constrain unifFuel output eType
    inferClausesWorker fuel unifFuel env ps input output
end

/-- Infer the supported expression forms with explicit bounds. Unsupported
forms are distinguished from type mismatches; diagnostic fidelity and the
remaining cases are not implemented. -/
def inferExprFuel (fuel unifFuel : Nat) (env : Env) (e : Exp) (s : State) :
    Except Error (InferT × State) :=
  (inferExprWorker fuel unifFuel env e) s


private def extendEnv (new old : Env) : Env :=
  ⟨nsAppend new.infV old.infV, nsAppend new.infC old.infC, nsAppend new.infT old.infT⟩

private def liftEnv (name : MlString) (env : Env) : Env :=
  ⟨nsLift name env.infV, nsLift name env.infC, nsLift name env.infT⟩

mutual
private def isValue : Exp → Bool
  | .lit _ | .var _ | .fn _ _ => true
  | .con _ es => isValueList es
  | .tannot e _ | .lannot e _ => isValue e
  | _ => false
termination_by e => sizeOf e

private def isValueList : List Exp → Bool
  | [] => true
  | e :: es => isValue e && isValueList es
termination_by es => sizeOf es
end

private def applyFull (fuel : Nat) (ts : List InferT) : M (List InferT) := do
  let s ← get
  match walkStarListFuel fuel s.subst ts with
  | none => fail .exhausted
  | some ts => pure ts

private def asCheckedType (fuel : Nat) (env : Env) (free : List MlString) (t : AstT) : M TypeSystemHOL.SemanticT := do
  match annotationWorker fuel env free t with
  | .error e => fail e
  | .ok t => pure t

private def asCheckedTypes (fuel : Nat) (env : Env) (free : List MlString) (ts : List AstT) : M (List TypeSystemHOL.SemanticT) := do
  match annotationsWorker fuel env free ts with
  | .error e => fail e
  | .ok ts => pure ts

private def datatypeEnv (fuel : Nat) (env : Env) (defs : TypeDef) : M Env := do
  let names := defs.map (fun (_, name, _) => name)
  if let some name := firstRepeatedName names then fail (.duplicateTypeName name) else
  let s ← get
  let (ids, s) := freshIds defs.length s
  set s
  let tenv := alistToNs ((List.zip defs ids).map (fun ((vars, name, _), id) =>
    (name, (vars, TypeSystemHOL.SemanticT.app (vars.map TypeSystemHOL.SemanticT.var) id))))
  let checkEnv := { env with infT := nsAppend tenv env.infT }
  let mut constructors := []
  for ((vars, typeName, ctors), id) in List.zip defs ids do
    if let some name := firstRepeatedName (ctors.map Prod.fst) then
      fail (.duplicateConstructor name typeName)
    if let some name := firstRepeatedName vars then
      fail (.duplicateTypeVariable name typeName)
    let mut block := []
    for (name, ts) in ctors do
      let ts ← asCheckedTypes fuel checkEnv vars ts
      block := (name, (vars, ts, id)) :: block
    constructors := block ++ constructors
  return { emptyEnv with infC := alistToNs constructors, infT := tenv }

mutual
private def inferDeclWorker : Nat → Nat → Env → Dec → M Env
  | 0, _, _, _ => fail .exhausted
  | fuel + 1, unifFuel, env, decl => do
    match decl with
    | .dlet loc pat expr => withLoc loc env do
      let st ← get
      set (resetState st)
      let exprType ← withLoc loc env (inferExprWorker fuel unifFuel env expr)
      let (patType, bindings) ← inferPatWorker fuel unifFuel env pat
      if let some name := firstRepeatedName (bindings.map Prod.fst) then fail (.duplicateDefinitionVariable name) else
      constrain unifFuel exprType patType
      let ts ← applyFull unifFuel (bindings.map Prod.snd)
      let (count, _, ts) := generaliseList 0 0 .ln ts
      if count != 0 && !isValue expr then fail .valueRestriction else
      let vars := List.zip (bindings.map Prod.fst) (ts.map (fun t => (count, t)))
      return { emptyEnv with infV := alistToNs vars }
    | .dletrec loc funs => withLoc loc env do
      let names := funs.map (fun (name, _, _) => name)
      if let some name := firstRepeatedName names then fail (.duplicateFunctionName name false) else
      let st ← get
      set (resetState st)
      let vars ← freshMany funs.length
      let env' := bindVars env (List.zip names vars)
      let types ← inferFunsWorker fuel unifFuel env' funs
      constrainMany unifFuel vars types
      let ts ← applyFull unifFuel vars
      let (count, _, ts) := generaliseList 0 0 .ln ts
      return { emptyEnv with infV := alistToNs (List.zip names (ts.map (fun t => (count, t)))) }
    | .dtype loc defs => withLoc loc env (datatypeEnv fuel env defs)
    | .dtabbrev loc vars name t => withLoc loc env do
      if let some varName := firstRepeatedName vars then fail (.duplicateAbbreviationVariable varName name) else
      let t ← asCheckedType fuel env vars t
      return { emptyEnv with infT := alistToNs [(name, (vars, t))] }
    | .dexn loc name ts => withLoc loc env do
      let ts ← asCheckedTypes fuel env [] ts
      return { emptyEnv with infC := alistToNs [(name, ([], ts, 3))] }
    | .dmod name ds =>
      let env' ← inferDeclsWorker fuel unifFuel env ds
      return liftEnv name env'
    | .dlocal ds body =>
      let env' ← inferDeclsWorker fuel unifFuel env ds
      inferDeclsWorker fuel unifFuel (extendEnv env' env) body
    | .denv _ => fail .unsupported

private def inferDeclsWorker : Nat → Nat → Env → List Dec → M Env
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure emptyEnv
  | fuel + 1, unifFuel, env, d :: ds => do
    let first ← inferDeclWorker fuel unifFuel env d
    let rest ← inferDeclsWorker fuel unifFuel (extendEnv first env) ds
    return extendEnv rest first
end

/-- Infer declarations with explicit bounds. Diagnostic messages and failure
states still differ from HOL, and the bounded workers need correspondence proofs. -/
def inferDeclsFuel (fuel unifFuel : Nat) (env : Env) (decls : List Dec) (state : State) :
    Except Error (Env × State) :=
  (inferDeclsWorker fuel unifFuel env decls) state

/-- The successful whole-program inference environment, starting with CakeML's
primitive type environment and the first non-primitive type identifier. -/
def inferProgramFuel (fuel unifFuel : Nat) (decls : List Dec) : Except Error Env := do
  let (env, _) ← inferDeclsFuel fuel unifFuel initConfig decls ⟨0, .ln, 15⟩
  return extendEnv env initConfig

end Flapjack.Compiler.Inference.Infer.Core
