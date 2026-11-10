module

public import Flapjack.Compiler.Backend.BviToData.CompileTotal
public import Flapjack.Compiler.Backend.Bvi.Budget
public import Flapjack.Misc.ListEl

@[expose] public section

/-! The original list-shaped BVI-to-data compiler. -/
namespace Flapjack.Compiler.Backend.BviToData
open Classical

private theorem listBudget_pos (xs : List Bvi.Exp) : 0 < Bvi.listBudget xs := by
  cases xs <;> simp [Bvi.listBudget] <;> omega

/-- The original compiler traverses expression lists directly, returning one
local name per expression. The executable uses the separate `compileSing` and
`compileList` rewrite, related by `compileSource_agrees`. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_def"]
noncomputable def compileSource (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat) :
    List Bvi.Exp → DataLang.Prog × List Nat × Nat
  | [] => (.skip, [], n)
  | x :: y :: xs =>
      let (c1, v1, n1) := compileSource n env false live [x]
      let (c2, vs, n2) := compileSource n1 env false ((Flapjack.holHd v1) :: live) (y :: xs)
      (.seq c1 c2, (Flapjack.holHd v1) :: vs, n2)
  | [.var v] =>
      let var := env[v]?.getD 0
      if tail then (.return [var], [n], n + 1) else (.skip, [var], max n (var + 1))
  | [.ifThenElse x y z] =>
      let (cx, vx, n1) := compileSource n env false live [x]
      let (cy, vy, n2) := compileSource n1 env tail live [y]
      let (cz, vz, n3) := compileSource n2 env tail live [z]
      if tail then (.seq cx (.ifThenElse (Flapjack.holHd vx) cy cz), [n3], n3 + 1)
      else (.seq cx (.ifThenElse (Flapjack.holHd vx) (.seq cy (.move n3 (Flapjack.holHd vy))) (.seq cz (.move n3 (Flapjack.holHd vz)))), [n3], n3 + 1)
  | [.let xs body] =>
      let (code, vars, n1) := compileSource n env false live xs
      let (body, result, n2) := compileSource n1 (vars ++ env) tail live [body]
      (.seq code body, result, n2)
  | [.raise x] =>
      let (code, result, n1) := compileSource n env false live [x]
      (.seq code (.raise (Flapjack.holHd result)), result, n1)
  | [.return xs] =>
      let (code, vars, n1) := compileSource n env false live xs
      (.seq code (.return vars), [n1], n1 + 1)
  | [.op op xs] =>
      let (code, vars, n1) := compileSource n env false live xs
      let result := DataLang.Prog.seq code (iAssign n1 op vars.reverse live env)
      (if tail then .seq result (.return [n1]) else result, [n1], n1 + 1)
  | [.tick x] =>
      let (code, result, n1) := compileSource n env tail live [x]
      (.seq .tick code, result, n1)
  | [.force label v] =>
      let var := env[v]?.getD 0
      let ret := if tail then none else some (n, namesOfList (live ++ env))
      (.force ret label var, [n], max (n + 1) (var + 1))
  | [.call ticks dest xs none] =>
      let (code, vars, n1) := compileSource n env false live xs
      let ret := if tail then none else some ([n1], namesOfList (live ++ env))
      (.seq code (DataLang.mkTicks ticks (.call ret dest vars none)), [n1], n1 + 1)
  | [.call ticks dest xs (some handler)] =>
      let (code, vars, n1) := compileSource n env false live xs
      let (h, value, n2) := compileSource (n1 + 1) (n1 :: env) false live [handler]
      let ret := some ([n2], namesOfList (live ++ env))
      let after := if tail then DataLang.Prog.return [n2] else .skip
      (.seq code (DataLang.mkTicks ticks (.seq (.call ret dest vars (some (n1, .seq h (.move n2 (Flapjack.holHd value))))) after)), [n2], n2 + 1)
  | [.letCall rets ticks dest xs body] =>
      let (code, vars, n1) := compileSource n env false live xs
      if body = .return ((List.range rets).map Bvi.Exp.var) then
        (.seq code (DataLang.mkTicks ticks (.call none (some dest) vars none)), [n1], n1 + 1)
      else
        let rs := (List.range rets).map (n1 + ·)
        let (body, value, n2) := compileSource (n1 + rets) (rs ++ env) tail live [body]
        let ret := some (rs, namesOfList (live ++ env))
        (.seq (.seq code (DataLang.mkTicks ticks (.call ret (some dest) vars none))) body, value, n2)
termination_by xs => Bvi.listBudget xs
decreasing_by
  all_goals try (have positive := listBudget_pos xs)
  all_goals simp_wf <;> simp [Bvi.listBudget, Bvi.expBudget] <;> omega

/-- Compile one complete expression and apply the source optimization sequence:
HOL's `optimise (FST (compile arg_count (COUNT_LIST arg_count) T [] [exp]))`. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_exp_def"]
noncomputable def compileExp (argc : Nat) (exp : Bvi.Exp) : DataLang.Prog :=
  optimise (compileSource argc (List.range argc) true [] [exp]).1

/-- Compile one labeled BVI function. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_part_def"]
noncomputable def compilePart (part : Nat × Nat × Bvi.Exp) : Nat × Nat × DataLang.Prog :=
  (part.1, part.2.1, compileExp part.2.1 part.2.2)

/-- Compile each labeled BVI function in source order. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_prog_def"]
noncomputable def compileProg (program : List (Nat × Nat × Bvi.Exp)) :
    List (Nat × Nat × DataLang.Prog) :=
  program.map compilePart

end Flapjack.Compiler.Backend.BviToData
