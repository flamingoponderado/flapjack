module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Compiler.Inference.Unify
public import Flapjack.AstHOL.Syntax
public import Flapjack.TypeSystemHOL.Values
public import Flapjack.Compiler.Inference.Infer.Duplicates
public import Flapjack.Compiler.Inference.Infer.TypeNameCheckSub
public import Flapjack.Compiler.Inference.Infer.TypeDefinitions
public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.TypeSystemHOL.TypeNames

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Bounded executable inference infrastructure. The result distinguishes
unsupported forms from rejected inputs and resource exhaustion. The state
APIs retain failure state; the legacy fuel APIs omit it. Full correspondence
with HOL's diagnostics and state transitions remains to be proved. -/
namespace Flapjack.Compiler.Inference.Infer.Core
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL
open Flapjack.Compiler.Inference.Unify
open Flapjack.Compiler.Inference.Infer.Duplicates

deriving instance Repr for Flapjack.NamespaceHOL.Namespace

inductive Error where
  | exhausted | unsupported | mismatch | badConstraintLists | undefinedName | valueRestriction | envDeclaration
  | floatPattern | emptyCase | emptyHandle
  | unsafeOperation | thunkOperation | primitiveTypeMismatch
  | primitiveArity : Op → Nat → Error
  | typeMismatch : InferT → InferT → Error
  | typeMismatchEnv : TypeSystemHOL.TenvAbbrev → InferT → InferT → Error
  | unboundTypeVariable : MlString → Error
  | annotationTypeVariable : MlString → Error
  | abbreviationTypeVariable : MlString → MlString → Error
  | exceptionTypeVariable : MlString → MlString → Error
  | duplicatePatternVariable : MlString → Error
  | duplicateDefinitionVariable : MlString → Error
  | duplicateFunctionName : MlString → Bool → Error
  | duplicateAbbreviationVariable : MlString → MlString → Error
  | constructorArity : Ident MlString MlString → Nat → Nat → Error
  | sourceTypeMessage : MlString → Error
  | undefinedVariable : Ident MlString MlString → Error
  | undefinedConstructor : Ident MlString MlString → Error
  | located : Flapjack.Misc.Location.Locs → Error → Error
  deriving Repr

abbrev M (α : Type) := ExceptT Error (StateM State) α

private def fail (e : Error) : M α := fun s => (.error e, s)

/-- Adapt the state-preserving execution result to the existing public API. -/
def discardFailureState (action : M α) (s : State) : Except Error (α × State) :=
  match action s with
  | (.ok value, next) => .ok (value, next)
  | (.error error, _) => .error error

/-- Preserve the innermost source location for errors that carry enough
information for original-style rendering. Other error classes remain unchanged. -/
private def locateError (loc : Flapjack.Misc.Location.Locs) (env : Env) : Error → Error
  | .valueRestriction => .located loc .valueRestriction
  | .floatPattern => .located loc .floatPattern
  | .emptyCase => .located loc .emptyCase
  | .emptyHandle => .located loc .emptyHandle
  | .unsafeOperation => .located loc .unsafeOperation
  | .thunkOperation => .located loc .thunkOperation
  | .primitiveTypeMismatch => .located loc .primitiveTypeMismatch
  | .badConstraintLists => .located loc .badConstraintLists
  | .primitiveArity op actual => .located loc (.primitiveArity op actual)
  | .undefinedVariable name => .located loc (.undefinedVariable name)
  | .undefinedConstructor name => .located loc (.undefinedConstructor name)
  | .sourceTypeMessage message => .located loc (.sourceTypeMessage message)
  | .typeMismatch left right => .located loc (.typeMismatchEnv env.infT left right)
  | .annotationTypeVariable name => .located loc (.annotationTypeVariable name)
  | .abbreviationTypeVariable name typ => .located loc (.abbreviationTypeVariable name typ)
  | .exceptionTypeVariable name ctor => .located loc (.exceptionTypeVariable name ctor)
  | .duplicatePatternVariable name => .located loc (.duplicatePatternVariable name)
  | .duplicateDefinitionVariable name => .located loc (.duplicateDefinitionVariable name)
  | .duplicateFunctionName name isLocal => .located loc (.duplicateFunctionName name isLocal)
  | .duplicateAbbreviationVariable name typ => .located loc (.duplicateAbbreviationVariable name typ)
  | .constructorArity name actual expected => .located loc (.constructorArity name actual expected)
  | other => other

def withLoc (loc : Flapjack.Misc.Location.Locs) (env : Env) (action : M α) : M α := fun state =>
  match action state with
  | (.error error, next) => (.error (locateError loc env error), next)
  | (.ok value, next) => (.ok value, next)
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

/-- Executable constraint step. Its error carrier is Flapjack-specific;
    source and executable behavior are related in the constraint proof. -/
def constrain (_fuel : Nat) (a b : InferT) : M Unit := fun s =>
  match unifyPartial s.subst a b with
  | none => (.error .exhausted, s)
  | some none =>
    match walkStar s.subst a, walkStar s.subst b with
    | some left, some right => (.error (.typeMismatch left right), s)
    | _, _ => (.error .mismatch, s)
  | some (some subst) => (.ok (), { s with subst })

/-- Execute paired constraints in order, stopping at the first failure. -/
def constrainMany (fuel : Nat) : List InferT → List InferT → M Unit
  | [], [] => pure ()
  | x :: xs, y :: ys => do
    constrain fuel x y
    constrainMany fuel xs ys
  | _, _ => fail .badConstraintLists

/-- Execution equations for comparing the executable list operation with
    the source-state operation. These are Flapjack infrastructure. -/
theorem constrainManyNil (fuel : Nat) (s : State) :
    constrainMany fuel [] [] s = (.ok (), s) := rfl

/-- Flapjack execution equation for an unmatched right-hand constraint. -/
theorem constrainManyNilCons (fuel : Nat) (y : InferT) (ys : List InferT) (s : State) :
    constrainMany fuel [] (y :: ys) s = (.error .badConstraintLists, s) := rfl

/-- Flapjack execution equation for an unmatched left-hand constraint. -/
theorem constrainManyConsNil (fuel : Nat) (x : InferT) (xs : List InferT) (s : State) :
    constrainMany fuel (x :: xs) [] s = (.error .badConstraintLists, s) := rfl

/-- Flapjack execution equation for two nonempty constraint lists. -/
theorem constrainManyCons (fuel : Nat) (x y : InferT) (xs ys : List InferT) (s : State) :
    constrainMany fuel (x :: xs) (y :: ys) s =
      match constrain fuel x y s with
      | (.error e, next) => (.error e, next)
      | (.ok _, next) => constrainMany fuel xs ys next := by
  simp only [constrainMany, Bind.bind, ExceptT.bind, StateT.bind, ExceptT.mk]
  cases h : constrain fuel x y s with
  | mk result next => cases result <;> rfl

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


private def annotationWorker (env : Env) (free : List MlString) (typ : AstT) :
    Except Error TypeSystemHOL.SemanticT :=
  match TypeNameCheck.typeNameCheckSub ⟨none, env.infT⟩ env.infT free typ () with
  | (.success t, _) => .ok t
  | (.failure (_, .inr name), _) => .error (.unboundTypeVariable name)
  | (.failure (_, .inl message), _) => .error (.sourceTypeMessage message)

private def annotationsWorker (env : Env) (free : List MlString) (ts : List AstT) :
    Except Error (List TypeSystemHOL.SemanticT) :=
  match TypeNameCheck.typeNameCheckSubList ⟨none, env.infT⟩ env.infT free ts () with
  | (.success result, _) => .ok result
  | (.failure (_, .inr name), _) => .error (.unboundTypeVariable name)
  | (.failure (_, .inl message), _) => .error (.sourceTypeMessage message)

private def annotation (env : Env) (t : AstT) : M InferT := do
  match annotationWorker env [] t with
  | .error (.unboundTypeVariable name) => fail (.annotationTypeVariable name)
  | .error e => fail e
  | .ok t => pure (inferTypeSubst [] t)

mutual
private def inferPatWorker : Nat → Nat → Env → Pat → M (InferT × List (MlString × InferT))
  | 0, _, _, _ => fail .exhausted
  | fuel + 1, unifFuel, env, p => do
    match p with
    | .pvar v => let t ← fresh; return (t, [(v, t)])
    | .pany => let t ← fresh; return (t, [])
    | .plit (.float64 _) => fail .floatPattern
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
      let typ ← annotation env typ
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

/-- Execute bounded pattern inference, retaining state on failure. -/
def inferPatternState (fuel unifFuel : Nat) (env : Env) (p : Pat) (s : State) :
    Except Error (InferT × List (MlString × InferT)) × State :=
  (inferPatWorker fuel unifFuel env p) s

/-- Infer a pattern with the existing result API, which omits failure state. -/
def inferPatternFuel (fuel unifFuel : Nat) (env : Env) (p : Pat) (s : State) :
    Except Error ((InferT × List (MlString × InferT)) × State) :=
  discardFailureState (inferPatWorker fuel unifFuel env p) s


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

@[hol "cakeml/compiler/inference/inferScript.sml" "op_to_string_def"]
def opToString (op : Op) : MlString × Nat :=
  match op with
  | .arith a t => (ofString "Arith", (arithArity a t).getD 0)
  | .fromTo _ _ => (ofString "FromTo", 1) | .test _ _ => (ofString "Test", 2)
  | .shift _ _ _ => (ofString "Shift", 1) | .equality => (ofString "Equality", 2)
  | .opapp => (ofString "Opapp", 2) | .opassign => (ofString "Opassign", 2)
  | .opref => (ofString "Opref", 1) | .opderef => (ofString "Opderef", 1)
  | .aw8alloc => (ofString "Aw8alloc", 2) | .aw8sub => (ofString "Aw8sub", 2)
  | .aw8length => (ofString "Aw8length", 1) | .aw8update => (ofString "Aw8update", 3)
  | .copyStrStr => (ofString "CopyStrStr", 3) | .copyStrAw8 => (ofString "CopyStrAw8", 5)
  | .copyAw8Str => (ofString "CopyAw8Str", 3) | .copyAw8Aw8 => (ofString "CopyAw8Aw8", 5)
  | .implode => (ofString "Implode", 1) | .explode => (ofString "Explode", 1)
  | .strsub => (ofString "Strsub", 2) | .strlen => (ofString "Strlen", 1) | .strcat => (ofString "Strcat", 1)
  | .vfromList => (ofString "VfromList", 1) | .vsub => (ofString "Vsub", 2) | .vlength => (ofString "Vlength", 1)
  | .aalloc => (ofString "Aalloc", 2) | .aallocEmpty => (ofString "AallocEmpty", 1)
  | .asub => (ofString "Asub", 2) | .alength => (ofString "Alength", 1) | .aupdate => (ofString "Aupdate", 3)
  | .listAppend => (ofString "ListAppend", 2) | .configGC => (ofString "ConfigGC", 2) | .ffi _ => (ofString "FFI", 2)
  | .aw8subUnsafe => (ofString "Aw8sub_unsafe", 2)
  | .aw8updateUnsafe => (ofString "Aw8update_unsafe", 3)
  | .xorAw8StrUnsafe => (ofString "XorAw8Str_unsafe", 2)
  | .vsubUnsafe => (ofString "Vsub_unsafe", 2)
  | .asubUnsafe => (ofString "Asub_unsafe", 2)
  | .aupdateUnsafe => (ofString "Aupdate_unsafe", 3)
  | .aallocFixed => (ofString "AallocFixed", 1)
  | .eval => (ofString "Eval", 6) | .envId => (ofString "Env_id", 1)
  | .thunkOp .forceThunk => (ofString "ForceThunk", 1)
  | .thunkOp (.allocThunk _) => (ofString "AllocThunk", 1)
  | .thunkOp (.updateThunk _) => (ofString "UpdateThunk", 2)

@[hol "cakeml/compiler/inference/inferScript.sml" "op_n_args_msg_def"]
def opNArgsMessage (op : Op) (n : Nat) : MlString :=
  let (name, expected) := opToString op
  MlString.concat [ofString "Primitive ", name, ofString " given ",
    .implode (Flapjack.holNumToDecString n), ofString " arguments, but expects ",
    .implode (Flapjack.holNumToDecString expected)]

private def inferOp (fuel : Nat) (op : Op) (ts : List InferT) : M InferT := do
  if let some (args, result) := simpleOp op then
    if ts.length != args.length then
      fail (.primitiveArity op ts.length)
    constrainMany fuel ts args
    return result
  match op, ts with
  | .vsubUnsafe, _ | .asubUnsafe, _ | .aupdateUnsafe, _ | .aw8subUnsafe, _
  | .aw8updateUnsafe, _ | .xorAw8StrUnsafe, _ | .aallocFixed, _ | .eval, _ | .envId, _ =>
    fail .unsafeOperation
  | .thunkOp _, _ => fail .thunkOperation
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
  | .arith _ _, _ | .fromTo _ _, _ | .test _ _, _ => fail .primitiveTypeMismatch
  | _, _ =>
    fail (.primitiveArity op ts.length)

private def bindVars (env : Env) (bindings : List (MlString × InferT)) : Env :=
  { env with infV := nsAppend (alistToNs (bindings.map (fun (name, t) => (name, (0, t))))) env.infV }

mutual
private def inferExprWorker : Nat → Nat → Env → AstHOL.Exp → M InferT
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
      if clauses.isEmpty then fail .emptyHandle else
      let t ← inferExprWorker fuel unifFuel env e
      inferClausesWorker fuel unifFuel env clauses (.app [] 3) t
      return t
    | .mat e clauses =>
      if clauses.isEmpty then fail .emptyCase else
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
      let typ ← annotation env typ
      constrain unifFuel t typ
      return t
    | .letrec funs body =>
      let names := funs.map (fun (name, _, _) => name)
      if let some name := findDup names then fail (.duplicateFunctionName name true) else
      let vars ← freshMany funs.length
      let env := bindVars env (List.zip names vars)
      let types ← inferFunsWorker fuel unifFuel env funs
      constrainMany unifFuel vars types
      inferExprWorker fuel unifFuel env body


private def inferFunsWorker : Nat → Nat → Env →
    List (MlString × MlString × AstHOL.Exp) → M (List InferT)
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure []
  | fuel + 1, unifFuel, env, (_, arg, body) :: rest => do
    let argType ← fresh
    let bodyType ← inferExprWorker fuel unifFuel (bindVars env [(arg, argType)]) body
    let rest ← inferFunsWorker fuel unifFuel env rest
    return .app [argType, bodyType] 4 :: rest

private def inferExprsWorker : Nat → Nat → Env → List AstHOL.Exp → M (List InferT)
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure []
  | fuel + 1, unifFuel, env, e :: es => do
    let t ← inferExprWorker fuel unifFuel env e
    let ts ← inferExprsWorker fuel unifFuel env es
    return t :: ts

private def inferClausesWorker : Nat → Nat → Env → List (Pat × AstHOL.Exp) →
    InferT → InferT → M Unit
  | 0, _, _, _, _, _ => fail .exhausted
  | _ + 1, _, _, [], _, _ => pure ()
  | fuel + 1, unifFuel, env, (p, e) :: ps, input, output => do
    let (pType, bindings) ← inferPatWorker fuel unifFuel env p
    if let some name := findDup (bindings.map Prod.fst) then fail (.duplicatePatternVariable name) else
    constrain unifFuel input pType
    let eType ← inferExprWorker fuel unifFuel (bindVars env bindings) e
    constrain unifFuel output eType
    inferClausesWorker fuel unifFuel env ps input output
end

/-- Execute bounded expression inference, retaining state on failure. -/
def inferExprState (fuel unifFuel : Nat) (env : Env) (e : AstHOL.Exp) (s : State) :
    Except Error InferT × State :=
  (inferExprWorker fuel unifFuel env e) s

/-- Infer expressions with the existing result API, which omits failure state. -/
def inferExprFuel (fuel unifFuel : Nat) (env : Env) (e : AstHOL.Exp) (s : State) :
    Except Error (InferT × State) :=
  discardFailureState (inferExprWorker fuel unifFuel env e) s



private def applyFull (ts : List InferT) : M (List InferT) := do
  let s ← get
  match walkStarList s.subst ts with
  | none => fail .exhausted
  | some ts => pure ts

private def asCheckedType (env : Env) (free : List MlString) (t : AstT)
    (unbound : MlString → Error) : M TypeSystemHOL.SemanticT := do
  match annotationWorker env free t with
  | .error (.unboundTypeVariable name) => fail (unbound name)
  | .error e => fail e
  | .ok t => pure t

private def asCheckedTypes (env : Env) (free : List MlString) (ts : List AstT)
    (unbound : MlString → Error) : M (List TypeSystemHOL.SemanticT) := do
  match annotationsWorker env free ts with
  | .error (.unboundTypeVariable name) => fail (unbound name)
  | .error e => fail e
  | .ok ts => pure ts

private def datatypeEnv (env : Env) (defs : TypeDef) : M Env := do
  let s ← get
  let (ids, s) := freshIds defs.length s
  set s
  let tenv := alistToNs ((List.zip defs ids).map (fun ((vars, name, _), id) =>
    (name, (vars, TypeSystemHOL.SemanticT.app (vars.map TypeSystemHOL.SemanticT.var) id))))
  let checkEnv := nsAppend tenv env.infT
  match TypeDefinitions.checkTypeDefinition ⟨none, env.infT⟩ checkEnv defs () with
  | (.failure (_, message), _) => fail (.sourceTypeMessage message)
  | (.success (), _) =>
    return { emptyEnv with infC := TypeSystemHOL.buildCtorTenv checkEnv defs ids, infT := tenv }

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
      if let some name := findDup (bindings.map Prod.fst) then fail (.duplicateDefinitionVariable name) else
      constrain unifFuel exprType patType
      let ts ← applyFull (bindings.map Prod.snd)
      let (count, _, ts) := generaliseList 0 0 .ln ts
      if count != 0 && !TypeSystemHOL.isValue expr then fail .valueRestriction else
      let vars := List.zip (bindings.map Prod.fst) (ts.map (fun t => (count, t)))
      return { emptyEnv with infV := alistToNs vars }
    | .dletrec loc funs => withLoc loc env do
      let names := funs.map (fun (name, _, _) => name)
      if let some name := findDup names then fail (.duplicateFunctionName name false) else
      let st ← get
      set (resetState st)
      let vars ← freshMany funs.length
      let env' := bindVars env (List.zip names vars)
      let types ← inferFunsWorker fuel unifFuel env' funs
      constrainMany unifFuel vars types
      let ts ← applyFull vars
      let (count, _, ts) := generaliseList 0 0 .ln ts
      return { emptyEnv with infV := alistToNs (List.zip names (ts.map (fun t => (count, t)))) }
    | .dtype loc defs => withLoc loc env (datatypeEnv env defs)
    | .dtabbrev loc vars name t => withLoc loc env do
      if let some varName := findDup vars then fail (.duplicateAbbreviationVariable varName name) else
      let t ← asCheckedType env vars t (fun var => .abbreviationTypeVariable var name)
      return { emptyEnv with infT := alistToNs [(name, (vars, t))] }
    | .dexn loc name ts => withLoc loc env do
      let ts ← asCheckedTypes env [] ts (fun var => .exceptionTypeVariable var name)
      return { emptyEnv with infC := alistToNs [(name, ([], ts, 3))] }
    | .dmod name ds =>
      let env' ← inferDeclsWorker fuel unifFuel env ds
      return liftIenv name env'
    | .dlocal ds body =>
      let env' ← inferDeclsWorker fuel unifFuel env ds
      inferDeclsWorker fuel unifFuel (extendDecIenv env' env) body
    | .denv _ => fail .envDeclaration

private def inferDeclsWorker : Nat → Nat → Env → List Dec → M Env
  | 0, _, _, _ => fail .exhausted
  | _ + 1, _, _, [] => pure emptyEnv
  | fuel + 1, unifFuel, env, d :: ds => do
    let first ← inferDeclWorker fuel unifFuel env d
    let rest ← inferDeclsWorker fuel unifFuel (extendDecIenv first env) ds
    return extendDecIenv rest first
end

/-- Execute bounded declaration inference, retaining state on failure. -/
def inferDeclsState (fuel unifFuel : Nat) (env : Env) (decls : List Dec) (state : State) :
    Except Error Env × State :=
  (inferDeclsWorker fuel unifFuel env decls) state

/-- Infer declarations with the existing result API, which omits failure state. -/
def inferDeclsFuel (fuel unifFuel : Nat) (env : Env) (decls : List Dec) (state : State) :
    Except Error (Env × State) :=
  discardFailureState (inferDeclsWorker fuel unifFuel env decls) state

/-- The successful whole-program inference environment, starting with CakeML's
primitive type environment and the first non-primitive type identifier. -/
def inferProgramFuel (fuel unifFuel : Nat) (decls : List Dec) : Except Error Env := do
  let (env, _) ← inferDeclsFuel fuel unifFuel initConfig decls ⟨0, .ln, startTypeId⟩
  return extendDecIenv env initConfig

end Flapjack.Compiler.Inference.Infer.Core
