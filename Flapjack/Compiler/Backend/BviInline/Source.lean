module

public import Flapjack.Compiler.Backend.BviInline

@[expose] public section

/-! Total source-shaped BVI inline pass traversals. -/
namespace Flapjack.Compiler.Backend.BviInline
open Bvi

mutual
/-- Inline eligible calls in an expression using a fixed sparse cache. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "inline_exp_def"]
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

/-- Inline eligible calls in each expression of a list. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "inline_exp_def"]
def inlineExpsSource (cache : Spt (Nat × Exp)) : List Exp → List Exp
  | [] => []
  | e :: rest => inlineExpSource cache e :: inlineExpsSource cache rest
termination_by es => sizeOf es
end

mutual
/-- Remove ticks from an expression, preserving its remaining structure. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "remove_ticks_exp_def"]
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

/-- Remove ticks from each expression in a list. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "remove_ticks_exp_def"]
def removeTicksListSource : List Exp → List Exp
  | [] => []
  | e :: rest => removeTicksSource e :: removeTicksListSource rest
termination_by es => sizeOf es
end

/-- Inline program bodies while threading the sparse wrapper cache. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "inline_all_def"]
def inlineAllSource : Spt (Nat × Exp) → List (Nat × Nat × Exp) → Spt (Nat × Exp) × List (Nat × Nat × Exp)
  | cache, [] => (cache, [])
  | cache, (name, arity, body) :: rest =>
    let body := inlineExpSource cache body
    let cache := if canonicalWrapper name arity body then sptInsert name (arity, body) cache else cache
    let (cache, rest) := inlineAllSource cache rest
    (cache, (name, arity, body) :: rest)

/-- Incrementally inline and then remove ticks from program bodies. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "compile_inc_def"]
def compileIncSource (cache : Spt (Nat × Exp)) (program : List (Nat × Nat × Exp)) :
    Spt (Nat × Exp) × List (Nat × Nat × Exp) :=
  let (cache, inlined) := inlineAllSource cache program
  (cache, inlined.map (fun (name, arity, body) => (name, arity, removeTicksSource body)))

/-- Inline a whole program starting with an empty wrapper cache. The executed
whole-program traversal agrees by `compileProgFuel_eq_source`. -/
@[hol "cakeml/compiler/backend/bvi_inlineScript.sml" "compile_prog_def"]
def compileProgSource (program : List (Nat × Nat × Exp)) :
    Spt (Nat × Exp) × List (Nat × Nat × Exp) := compileIncSource .ln program

end Flapjack.Compiler.Backend.BviInline
