import Flapjack.Compiler.Backend.BviInline

/-! Total source-shaped BVI inline pass traversals. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

mutual
/-- Flapjack infrastructure: total source-shaped inlining with a fixed sparse
cache. HOL statement and carrier review remains pending. -/
def inlineExpSource (cache : Spt (Nat × Exp)) : Exp → Exp
  | .var n => .var n
  | .ifThenElse x y z => .ifThenElse (inlineExpSource cache x) (inlineExpSource cache y) (inlineExpSource cache z)
  | .let xs body => .let (inlineExpsSource cache xs) (inlineExpSource cache body)
  | .raise body => .raise (inlineExpSource cache body)
  | .tick body => .tick (inlineExpSource cache body)
  | .call ticks target xs handler =>
      let args := inlineExpsSource cache xs
      match handler with
      | some body => .call ticks target args (some (inlineExpSource cache body))
      | none =>
        match target with
        | none => .call ticks none args none
        | some name =>
          match sptLookup name cache with
          | none => .call ticks (some name) args none
          | some (arity, body) =>
            if args.length = arity then .let args (mkTick (ticks + 1) body)
            else .call ticks (some name) args none
  | .force location index => .force location index
  | .op op args => .op op (inlineExpsSource cache args)
  | .letCall rets ticks target args body =>
      .letCall rets ticks target (inlineExpsSource cache args) (inlineExpSource cache body)
  | .return args => .return (inlineExpsSource cache args)
termination_by e => sizeOf e

/-- Flapjack infrastructure: source-shaped list traversal for inlining. -/
def inlineExpsSource (cache : Spt (Nat × Exp)) : List Exp → List Exp
  | [] => []
  | e :: rest => inlineExpSource cache e :: inlineExpsSource cache rest
termination_by es => sizeOf es
end

mutual
/-- Flapjack infrastructure: total tick removal following the source
constructor clauses. This remains untagged until the HOL carriers and the
executed traversal have been reviewed against this definition. -/
def removeTicksSource : Exp → Exp
  | .var n => .var n
  | .ifThenElse x y z => .ifThenElse (removeTicksSource x) (removeTicksSource y) (removeTicksSource z)
  | .let xs body => .let (removeTicksListSource xs) (removeTicksSource body)
  | .raise body => .raise (removeTicksSource body)
  | .tick body => removeTicksSource body
  | .call _ target args handler =>
      .call 0 target (removeTicksListSource args)
        (match handler with | none => none | some body => some (removeTicksSource body))
  | .force location index => .force location index
  | .op op args => .op op (removeTicksListSource args)
  | .letCall rets _ target args body => .letCall rets 0 target (removeTicksListSource args) (removeTicksSource body)
  | .return args => .return (removeTicksListSource args)
termination_by e => sizeOf e

/-- Flapjack infrastructure: source-shaped list traversal for tick removal. -/
def removeTicksListSource : List Exp → List Exp
  | [] => []
  | e :: rest => removeTicksSource e :: removeTicksListSource rest
termination_by es => sizeOf es
end

/-- Flapjack infrastructure: source-shaped inlining threads the sparse
wrapper cache in program order. -/
def inlineAllSource : Spt (Nat × Exp) → List (Nat × Nat × Exp) → Spt (Nat × Exp) × List (Nat × Nat × Exp)
  | cache, [] => (cache, [])
  | cache, (name, arity, body) :: rest =>
    let body := inlineExpSource cache body
    let cache := if canonicalWrapper name arity body then sptInsert name (arity, body) cache else cache
    let (cache, rest) := inlineAllSource cache rest
    (cache, (name, arity, body) :: rest)

/-- Flapjack infrastructure: total incremental inlining and tick cleanup. -/
def compileIncSource (cache : Spt (Nat × Exp)) (program : List (Nat × Nat × Exp)) :
    Spt (Nat × Exp) × List (Nat × Nat × Exp) :=
  let (cache, inlined) := inlineAllSource cache program
  (cache, inlined.map (fun (name, arity, body) => (name, arity, removeTicksSource body)))

end Flapjack.Compiler.Backend.BviInline
