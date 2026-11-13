module

public import Flapjack.Compiler.Backend.BviToData.Compile
public import Flapjack.Compiler.Backend.BviToData.CompileTotal
public import Flapjack.Compiler.Backend.Bvi.Budget
public import Flapjack.Misc.ListEl
-- Only the agreement proofs below use `aesop`; nothing exported needs it.
import Aesop

@[expose] public section

/-! The original list-shaped BVI-to-data compiler. -/
namespace Flapjack.Compiler.Backend.BviToData
open Classical

private theorem listBudget_pos (xs : List Bvi.Exp) : 0 < Bvi.listBudget xs := by
  cases xs
  · simp [Bvi.listBudget]
  · simp [Bvi.listBudget]
    omega

/-- The executable variable-sequence test recognizes exactly the mapped range. -/
private theorem variablesFrom_eq_range (xs : List Bvi.Exp) (n : Nat) :
    isVariablesFrom xs n = true ↔ xs = (List.range' n xs.length).map Bvi.Exp.var := by
  induction xs generalizing n with
  | nil => simp [isVariablesFrom]
  | cons head tail ih =>
    cases head <;> simp [isVariablesFrom, List.range', ih]

/-- The executable tail-return test is the source's return-shape comparison. -/
private theorem tailReturn_eq_return (rets : Nat) (body : Bvi.Exp) :
    isTailReturn rets body = true ↔ body = .return ((List.range rets).map Bvi.Exp.var) := by
  cases body <;> simp [isTailReturn, variablesFrom_eq_range, List.range_eq_range']
  case «return» xs =>
    constructor
    · rintro ⟨length, eq⟩
      simpa [length] using eq
    · intro eq
      subst xs
      simp

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
  all_goals
    simp_wf
    simp [Bvi.listBudget, Bvi.expBudget] <;> omega

/-- Executable twin of the reviewed `compileSource`: the same clauses, with
`List.headD 0` in place of HOL's unspecified `HD []`. Every `HD` argument is
the name list of a singleton compilation, which is nonempty, so the twin is
equal to `compileSource` (`compileSource_eq_impl`) and the compiler uses it as
the `@[csimp]` replacement for the noncomputable source definition. -/
def compileSourceImpl (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat) :
    List Bvi.Exp → DataLang.Prog × List Nat × Nat
  | [] => (.skip, [], n)
  | x :: y :: xs =>
      let (c1, v1, n1) := compileSourceImpl n env false live [x]
      let (c2, vs, n2) := compileSourceImpl n1 env false (v1.headD 0 :: live) (y :: xs)
      (.seq c1 c2, v1.headD 0 :: vs, n2)
  | [.var v] =>
      let var := env[v]?.getD 0
      if tail then (.return [var], [n], n + 1) else (.skip, [var], max n (var + 1))
  | [.ifThenElse x y z] =>
      let (cx, vx, n1) := compileSourceImpl n env false live [x]
      let (cy, vy, n2) := compileSourceImpl n1 env tail live [y]
      let (cz, vz, n3) := compileSourceImpl n2 env tail live [z]
      if tail then (.seq cx (.ifThenElse (vx.headD 0) cy cz), [n3], n3 + 1)
      else (.seq cx (.ifThenElse (vx.headD 0) (.seq cy (.move n3 (vy.headD 0)))
        (.seq cz (.move n3 (vz.headD 0)))), [n3], n3 + 1)
  | [.let xs body] =>
      let (code, vars, n1) := compileSourceImpl n env false live xs
      let (body, result, n2) := compileSourceImpl n1 (vars ++ env) tail live [body]
      (.seq code body, result, n2)
  | [.raise x] =>
      let (code, result, n1) := compileSourceImpl n env false live [x]
      (.seq code (.raise (result.headD 0)), result, n1)
  | [.return xs] =>
      let (code, vars, n1) := compileSourceImpl n env false live xs
      (.seq code (.return vars), [n1], n1 + 1)
  | [.op op xs] =>
      let (code, vars, n1) := compileSourceImpl n env false live xs
      let result := DataLang.Prog.seq code (iAssign n1 op vars.reverse live env)
      (if tail then .seq result (.return [n1]) else result, [n1], n1 + 1)
  | [.tick x] =>
      let (code, result, n1) := compileSourceImpl n env tail live [x]
      (.seq .tick code, result, n1)
  | [.force label v] =>
      let var := env[v]?.getD 0
      let ret := if tail then none else some (n, namesOfList (live ++ env))
      (.force ret label var, [n], max (n + 1) (var + 1))
  | [.call ticks dest xs none] =>
      let (code, vars, n1) := compileSourceImpl n env false live xs
      let ret := if tail then none else some ([n1], namesOfList (live ++ env))
      (.seq code (DataLang.mkTicks ticks (.call ret dest vars none)), [n1], n1 + 1)
  | [.call ticks dest xs (some handler)] =>
      let (code, vars, n1) := compileSourceImpl n env false live xs
      let (h, value, n2) := compileSourceImpl (n1 + 1) (n1 :: env) false live [handler]
      let ret := some ([n2], namesOfList (live ++ env))
      let after := if tail then DataLang.Prog.return [n2] else .skip
      (.seq code (DataLang.mkTicks ticks (.seq (.call ret dest vars
        (some (n1, .seq h (.move n2 (value.headD 0))))) after)), [n2], n2 + 1)
  | [.letCall rets ticks dest xs body] =>
      let (code, vars, n1) := compileSourceImpl n env false live xs
      if isTailReturn rets body then
        (.seq code (DataLang.mkTicks ticks (.call none (some dest) vars none)), [n1], n1 + 1)
      else
        let rs := (List.range rets).map (n1 + ·)
        let (body, value, n2) := compileSourceImpl (n1 + rets) (rs ++ env) tail live [body]
        let ret := some (rs, namesOfList (live ++ env))
        (.seq (.seq code (DataLang.mkTicks ticks (.call ret (some dest) vars none)))
          body, value, n2)
termination_by xs => Bvi.listBudget xs
decreasing_by
  all_goals try (have positive := listBudget_pos xs)
  all_goals
    simp_wf
    simp [Bvi.listBudget, Bvi.expBudget] <;> omega

/-- The executable twin agrees with the executable single/list rewrites, the
same target as `compileSource_agrees`. -/
theorem compileSourceImpl_agrees (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (xs : List Bvi.Exp) :
    compileSourceImpl n env tail live xs =
      match xs with
      | [] => (.skip, [], n)
      | [x] => let (code, name, next) := compileSing n env tail live x; (code, [name], next)
      | _ => compileList n env live xs := by
  fun_induction compileSourceImpl n env tail live xs <;>
    simp_all [compileSing, compileList, tailReturn_eq_return] <;>
    aesop (add simp [compileList, Flapjack.holHd])

/-- The source traversal agrees with the single-expression and non-tail list
rewrites used by the executable compiler. -/
theorem compileSource_agrees (n : Nat) (env : List Nat) (tail : Bool) (live : List Nat)
    (xs : List Bvi.Exp) :
    compileSource n env tail live xs =
      match xs with
      | [] => (.skip, [], n)
      | [x] => let (code, name, next) := compileSing n env tail live x; (code, [name], next)
      | _ => compileList n env live xs := by
  fun_induction compileSource n env tail live xs <;>
    simp_all [compileSing, compileList, Flapjack.holHd] <;>
    aesop (add simp [compileList, Flapjack.holHd])

/-- Kernel-checked compiler replacement for the noncomputable source
definition: the twin agrees with the source through the shared executable
single/list rewrites. -/
@[csimp] theorem compileSource_eq_impl : @compileSource = @compileSourceImpl := by
  funext n env tail live xs
  rw [compileSource_agrees, compileSourceImpl_agrees]

/-- Compile one complete expression and apply the source optimization sequence:
HOL's `optimise (FST (compile arg_count (COUNT_LIST arg_count) T [] [exp]))`. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_exp_def"]
def compileExp (argc : Nat) (exp : Bvi.Exp) : DataLang.Prog :=
  optimise (compileSource argc (List.range argc) true [] [exp]).1

/-- Compile one labeled BVI function. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_part_def"]
def compilePart (part : Nat × Nat × Bvi.Exp) : Nat × Nat × DataLang.Prog :=
  (part.1, part.2.1, compileExp part.2.1 part.2.2)

/-- Compile each labeled BVI function in source order. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "compile_prog_def"]
def compileProg (program : List (Nat × Nat × Bvi.Exp)) :
    List (Nat × Nat × DataLang.Prog) :=
  program.map compilePart

end Flapjack.Compiler.Backend.BviToData
