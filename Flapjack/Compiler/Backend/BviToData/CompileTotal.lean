module

public import Flapjack.Compiler.Backend.BviToData.Assign
public import Flapjack.Compiler.Backend.BviToData.Optimise
public import Flapjack.Compiler.Backend.Bvi.Syntax

@[expose] public section

/-! Total source-shaped BVI-to-data expression lowering. -/
namespace Flapjack.Compiler.Backend.BviToData
open Classical

mutual
/-- Lower a single expression with the source's local-name and live-set rules. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_sing_def"]
noncomputable def compileSing (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat) :
    Bvi.Exp → DataLang.Prog × Nat × Nat
  | .var v =>
      let var := env[v]?.getD 0
      if tail then (.return [var], n, n + 1) else (.skip, var, max n (var + 1))
  | .ifThenElse x y z =>
      let (cx, vx, n1) := compileSing n env false live x
      let (cy, vy, n2) := compileSing n1 env tail live y
      let (cz, vz, n3) := compileSing n2 env tail live z
      if tail then (.seq cx (.ifThenElse vx cy cz), n3, n3 + 1)
      else (.seq cx (.ifThenElse vx (.seq cy (.move n3 vy)) (.seq cz (.move n3 vz))), n3, n3 + 1)
  | .let xs body =>
      let (code, vars, n1) := compileList n env live xs
      let (body, result, n2) := compileSing n1 (vars ++ env) tail live body
      (.seq code body, result, n2)
  | .raise x =>
      let (code, result, n1) := compileSing n env false live x
      (.seq code (.raise result), result, n1)
  | .return xs =>
      let (code, vars, n1) := compileList n env live xs
      (.seq code (.return vars), n1, n1 + 1)
  | .op op xs =>
      let (code, vars, n1) := compileList n env live xs
      let result := DataLang.Prog.seq code (iAssign n1 op vars.reverse live env)
      (if tail then .seq result (.return [n1]) else result, n1, n1 + 1)
  | .tick x =>
      let (code, result, n1) := compileSing n env tail live x
      (.seq .tick code, result, n1)
  | .force label v =>
      let var := env[v]?.getD 0
      let ret := if tail then none else some (n, namesOfList (live ++ env))
      (.force ret label var, n, max (n + 1) (var + 1))
  | .call ticks dest xs none =>
      let (code, vars, n1) := compileList n env live xs
      let ret := if tail then none else some ([n1], namesOfList (live ++ env))
      (.seq code (DataLang.mkTicks ticks (.call ret dest vars none)), n1, n1 + 1)
  | .call ticks dest xs (some handler) =>
      let (code, vars, n1) := compileList n env live xs
      let (h, value, n2) := compileSing (n1 + 1) (n1 :: env) false live handler
      let ret := some ([n2], namesOfList (live ++ env))
      let after := if tail then DataLang.Prog.return [n2] else .skip
      (.seq code (DataLang.mkTicks ticks (.seq (.call ret dest vars (some (n1, .seq h (.move n2 value)))) after)), n2, n2 + 1)
  | .letCall rets ticks dest xs body =>
      let (code, vars, n1) := compileList n env live xs
      if body = .return ((List.range rets).map Bvi.Exp.var) then
        (.seq code (DataLang.mkTicks ticks (.call none (some dest) vars none)), n1, n1 + 1)
      else
        let rs := (List.range rets).map (n1 + ·)
        let (body, value, n2) := compileSing (n1 + rets) (rs ++ env) tail live body
        let ret := some (rs, namesOfList (live ++ env))
        (.seq (.seq code (DataLang.mkTicks ticks (.call ret (some dest) vars none))) body, value, n2)
termination_by exp => sizeOf exp

/-- Lower a list of expressions, preserving evaluation and live-set order. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_sing_def"]
noncomputable def compileList (n : Nat) (env live : List Nat) :
    List Bvi.Exp → DataLang.Prog × List Nat × Nat
  | [] => (.skip, [], n)
  | x :: xs =>
      let (code, value, n1) := compileSing n env false live x
      if xs = [] then (code, [value], n1) else
        let (rest, values, n2) := compileList n1 env (value :: live) xs
        (.seq code rest, value :: values, n2)
termination_by xs => sizeOf xs
end

/-- Compile a complete expression, then apply the original optimization sequence.
HOL's `compile_exp_def` is the list-shaped `optimise (FST (compile arg_count
(COUNT_LIST arg_count) T [] [exp]))`; this definition instead uses the
singleton-threaded `compile_sing` form, which is the right-hand side of HOL's
`compile_exp_eq`. `compileExp_source` (Proofs/CompileSource.lean) proves the
two agree, but this is not the source-shaped definition: the exact port would
call the reviewed `compileSource` (`compile_def`) below `CompileSource`.

Former reference: `@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml"
"compile_exp_def"]`. -/
noncomputable def compileExp (argc : Nat) (exp : Bvi.Exp) : DataLang.Prog :=
  optimise (compileSing argc (List.range argc) true [] exp).1

/-- Compile one labeled BVI function. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_part_def"]
noncomputable def compilePart (part : Nat × Nat × Bvi.Exp) : Nat × Nat × DataLang.Prog :=
  (part.1, part.2.1, compileExp part.2.1 part.2.2)

/-- Compile each labeled BVI function in source order. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_prog_def"]
noncomputable def compileProg (program : List (Nat × Nat × Bvi.Exp)) : List (Nat × Nat × DataLang.Prog) :=
  program.map compilePart

end Flapjack.Compiler.Backend.BviToData
