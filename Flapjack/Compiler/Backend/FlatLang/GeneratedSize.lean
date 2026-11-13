module

public import Flapjack.Compiler.Backend.FlatLang
public import Flapjack.AstHOL.GeneratedSize
public import Flapjack.Compiler.Backend.BackendCommon.Trace.GeneratedSize
public import Flapjack.Misc.GeneratedSize

@[expose] public section

namespace Flapjack.Compiler.Backend.FlatLang

/-- HOL's datatype-generated `flatLang$op_size`. The typed equations are
captured as `flat_op_size_def_typed` in `flat_elim_value_globals_probe.out`;
the function is needed to reproduce HOL's generated expression size. -/
def opSizeHOL : Op → Nat
  | .src op => 1 + AstHOL.opSizeHOL op
  | .globalVarAlloc n => 1 + n
  | .globalVarInit n => 1 + n
  | .globalVarLookup n => 1 + n
  | .tagLenEq a b => 1 + (a + b)
  | .lenEq n => 1 + n
  | .el n => 1 + n
  | .id => 0

mutual
/-- HOL's generated `pat_size`. Its complete typed equations are captured as
`flat_pat_size_def_typed` in `flat_elim_value_globals_probe.out`. -/
def patSizeHOL : Pat → Nat
  | .pany => 0
  | .pvar name => 1 + mlstringSizeHOL name
  | .plit lit => 1 + AstHOL.litSizeHOL lit
  | .pcon tag pats =>
      1 + (optionSizeHOL (pairSizeHOL id
        (optionSizeHOL (pairSizeHOL id (listSizeHOL (pairSizeHOL id id))))) tag +
        patListSizeHOL pats)
  | .pas pat name => 1 + (patSizeHOL pat + mlstringSizeHOL name)
  | .pref pat => 1 + patSizeHOL pat

/-- The list component `pat1_size` generated along with `pat_size`. -/
def patListSizeHOL : List Pat → Nat
  | [] => 0
  | pat :: pats => 1 + (patSizeHOL pat + patListSizeHOL pats)
end

mutual
/-- HOL's datatype-generated flat expression size. The full typed equations,
including all six auxiliary sizes, are captured in
`flat_elim_value_globals_probe.out` as `flat_exp_size_def_typed`. -/
def expSizeHOL : Exp → Nat
  | .raise tr e => 1 + (BackendCommon.traSizeHOL tr + expSizeHOL e)
  | .handle tr e branches =>
      1 + (BackendCommon.traSizeHOL tr + (expSizeHOL e + exp3SizeHOL branches))
  | .lit tr lit => 1 + (BackendCommon.traSizeHOL tr + AstHOL.litSizeHOL lit)
  | .con tr tag es =>
      1 + (BackendCommon.traSizeHOL tr +
        (optionSizeHOL (pairSizeHOL id (optionSizeHOL id)) tag + exp6SizeHOL es))
  | .varLocal tr name => 1 + (BackendCommon.traSizeHOL tr + mlstringSizeHOL name)
  | .fn name arg body => 1 + (mlstringSizeHOL name + (mlstringSizeHOL arg + expSizeHOL body))
  | .app tr op es => 1 + (BackendCommon.traSizeHOL tr + (opSizeHOL op + exp6SizeHOL es))
  | .if_ tr c t e =>
      1 + (BackendCommon.traSizeHOL tr + (expSizeHOL c + (expSizeHOL t + expSizeHOL e)))
  | .mat tr e branches =>
      1 + (BackendCommon.traSizeHOL tr + (expSizeHOL e + exp3SizeHOL branches))
  | .let_ tr name value body =>
      1 + (BackendCommon.traSizeHOL tr +
        (optionSizeHOL mlstringSizeHOL name + (expSizeHOL value + expSizeHOL body)))
  | .letrec name bindings body =>
      1 + (mlstringSizeHOL name + (exp1SizeHOL bindings + expSizeHOL body))

/-- The `exp1_size` list component of HOL's generated expression size. -/
def exp1SizeHOL : List (AstHOL.VarN × AstHOL.VarN × Exp) → Nat
  | [] => 0
  | pair :: rest => 1 + (exp2SizeHOL pair + exp1SizeHOL rest)

/-- The `exp2_size` pair component of HOL's generated expression size. -/
def exp2SizeHOL : (AstHOL.VarN × AstHOL.VarN × Exp) → Nat
  | (name, rest) => 1 + (mlstringSizeHOL name + exp4SizeHOL rest)

/-- The `exp3_size` branch-list component of HOL's generated expression size. -/
def exp3SizeHOL : List (Pat × Exp) → Nat
  | [] => 0
  | pair :: rest => 1 + (exp5SizeHOL pair + exp3SizeHOL rest)

/-- The `exp4_size` pair component of HOL's generated expression size. -/
def exp4SizeHOL : (AstHOL.VarN × Exp) → Nat
  | (name, body) => 1 + (mlstringSizeHOL name + expSizeHOL body)

/-- The `exp5_size` branch-pair component of HOL's generated expression size. -/
def exp5SizeHOL : (Pat × Exp) → Nat
  | (pat, body) => 1 + (patSizeHOL pat + expSizeHOL body)

/-- The `exp6_size` expression-list component of HOL's generated size. -/
def exp6SizeHOL : List Exp → Nat
  | [] => 0
  | e :: rest => 1 + (expSizeHOL e + exp6SizeHOL rest)
end

end Flapjack.Compiler.Backend.FlatLang
