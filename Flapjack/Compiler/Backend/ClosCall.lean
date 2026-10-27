import Flapjack.Compiler.Backend.ClosLang.Pure
import Flapjack.Compiler.Backend.DbVars
import Flapjack.Compiler.Backend.BackendCommon.Trace

/-! Fuel-bounded implementation of the closure-to-direct-call pass. The HOL
totality and correctness proofs remain unported. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang DbVars

mutual
  /-- Annotate closure free variables using the source pass's unoptimized
  free-variable traversal. -/
  def freeFuel : Nat → Exp → Option (Exp × DbVarSet)
    | 0, _ => none
    | fuel + 1, e => do
      let visit := freeFuel fuel
      let visitList := freeListFuel fuel
      match e with
      | .var t v => pure (.var t v, .var v)
      | .ifThenElse t x y z =>
          let (x, a) ← visit x
          let (y, b) ← visit y
          let (z, c) ← visit z
          pure (.ifThenElse t x y z, mkUnion a (mkUnion b c))
      | .let t xs body =>
          let (xs, a) ← visitList xs
          let (body, b) ← visit body
          pure (.let t xs body, mkUnion a (.shift xs.length b))
      | .raise t x => let (x, a) ← visit x; pure (.raise t x, a)
      | .tick t x => let (x, a) ← visit x; pure (.tick t x, a)
      | .op t op xs => let (xs, a) ← visitList xs; pure (.op t op xs, a)
      | .app t loc x xs =>
          let (x, a) ← visit x
          let (xs, b) ← visitList xs
          pure (.app t loc x xs, mkUnion a b)
      | .fn name loc _ arity body =>
          let (body, a) ← visit body
          let a := DbVarSet.shift arity a
          pure (.fn name loc (some (varsToList a)) arity body, a)
      | .letrec names loc _ fns body =>
          let fs ← fns.mapM fun (n, x) => do
            let (x, a) ← visit x
            pure ((n, x), DbVarSet.shift (n + fns.length) a)
          let a := listMkUnion (fs.map Prod.snd)
          let (body, b) ← visit body
          pure (.letrec names loc (some (varsToList a)) (fs.map Prod.fst) body,
            mkUnion a (.shift fns.length b))
      | .handle t x y =>
          let (x, a) ← visit x
          let (y, b) ← visit y
          pure (.handle t x y, mkUnion a (.shift 1 b))
      | .call t ticks dest xs => let (xs, a) ← visitList xs; pure (.call t ticks dest xs, a)

  /-- Traverse free-variable inputs in their original order. -/
  def freeListFuel : Nat → List Exp → Option (List Exp × DbVarSet)
    | _, [] => some ([], .empty)
    | 0, _ :: _ => none
    | fuel + 1, x :: xs => do
      let (x, a) ← freeFuel fuel x
      let (xs, b) ← freeListFuel fuel xs
      pure (x :: xs, mkUnion a b)
end

/-- Check closure free-variable emptiness without changing the input. -/
def closedFuel (fuel : Nat) (e : Exp) : Option Bool := do
  let (_, free) ← freeFuel fuel e
  pure (sptToAList (dbToSet free)).isEmpty

abbrev State := NumSet × List (Nat × Nat × Exp)

private def insertEach (loc count : Nat) (state : State) : State :=
  ((List.range count).foldl (fun s i => sptInsert (loc + 2 * i) () s) state.1, state.2)
private def codeList (loc : Nat) (fns : List (Nat × Exp)) (state : State) : State :=
  (state.1, (fns.zip (List.range fns.length)).foldl
    (fun code ((arity, body), i) => (loc + 2 * i + 1, arity, body) :: code) state.2)
private def variables (t : BackendCommon.Tra) (arity : Nat) : List Exp :=
  (List.range arity).map (.var t)
private def callsList (loc : Nat) (fns : List (Nat × Exp)) : List (Nat × Exp) :=
  (fns.zip (List.range fns.length)).map fun ((arity, _), i) =>
    (arity, .call .none 0 (loc + 2 * i + 1) (variables .none arity))

mutual
  /-- Convert known closed closures into direct calls while threading the
  sparse set of known code locations and the generated auxiliary functions. -/
  def callsFuel : Nat → Exp → State → Option (Exp × State)
    | 0, _, _ => none
    | fuel + 1, e, state => do
      let visit := callsFuel fuel
      let visitList := callsListFuel fuel
      match e with
      | .var t n => pure (.var t n, state)
      | .ifThenElse t x y z =>
          let (x, state) ← visit x state
          let (y, state) ← visit y state
          let (z, state) ← visit z state
          pure (.ifThenElse t x y z, state)
      | .let t xs body =>
          let (xs, state) ← visitList xs state
          let (body, state) ← visit body state
          pure (.let t xs body, state)
      | .raise t x => let (x, state) ← visit x state; pure (.raise t x, state)
      | .tick t x => let (x, state) ← visit x state; pure (.tick t x, state)
      | .handle t x y =>
          let (x, state) ← visit x state
          let (y, state) ← visit y state
          pure (.handle t x y, state)
      | .call t ticks dest xs => let (xs, state) ← visitList xs state; pure (.call t ticks dest xs, state)
      | .op t op xs => let (xs, state) ← visitList xs state; pure (.op t op xs, state)
      | .app t loc x xs =>
          let (xs, state) ← visitList xs state
          let (x', state) ← visit x state
          match loc with
          | some loc =>
              if (sptLookup loc state.1).isSome then
                if ClosLang.pure x then pure (.call t xs.length (loc + 1) xs, state)
                else pure (.let (BackendCommon.mkCons t 0) (xs ++ [x'])
                  (.call (BackendCommon.mkCons t 1) xs.length (loc + 1) (variables .none xs.length)), state)
              else pure (.app t (some loc) x' xs, state)
          | none => pure (.app t none x' xs, state)
      | .fn name loc ws arity body =>
          let n := loc.getD 0
          let newState := insertEach n 1 state
          let (body', newState) ← visit body newState
          let newState := (newState.1, (n + 1, arity, body') :: newState.2)
          if ← closedFuel fuel (.fn name loc ws arity body') then
            pure (.fn name loc ws arity (.call .none 0 (n + 1) (variables .none arity)), newState)
          else
            let (body', state) ← visit body state
            pure (.fn name loc ws arity body', state)
      | .letrec names loc ws fns body =>
          let n := loc.getD 0
          let newState := insertEach n fns.length state
          let (bodies, newState) ← visitList (fns.map Prod.snd) newState
          let closed ← (fns.zip bodies).foldlM (fun all ((arity, _), code) => do
            if !all then pure false else closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity code)) true
          if closed then
            let newState := codeList n ((fns.map Prod.fst).zip bodies) newState
            let (body, state) ← visit body newState
            pure (.letrec names loc ws (callsList n fns) body, state)
          else
            let (bodies, state) ← visitList (fns.map Prod.snd) state
            let (body, state) ← visit body state
            pure (.letrec names loc ws ((fns.map Prod.fst).zip bodies) body, state)

  /-- Traverse a list, threading state in evaluation order. -/
  def callsListFuel : Nat → List Exp → State → Option (List Exp × State)
    | _, [], state => some ([], state)
    | 0, _ :: _, _ => none
    | fuel + 1, x :: xs, state => do
      let (x, state) ← callsFuel fuel x state
      let (xs, state) ← callsListFuel fuel xs state
      pure (x :: xs, state)
end

/-- Apply the bounded closure-call pass when enabled. -/
def compileFuel (fuel : Nat) (enabled : Bool) (es : List Exp) : Option (List Exp × State) :=
  if enabled then callsListFuel fuel es (.ln, []) else some (es, (.ln, []))

end Flapjack.Compiler.Backend.ClosCall
