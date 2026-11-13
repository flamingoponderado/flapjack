module

public import Flapjack.Compiler.Backend.Semantics.FlatSem
public import Flapjack.Compiler.Backend.FlatLang.GeneratedSize

@[expose] public section

namespace Flapjack.Compiler.Backend.FlatSem

mutual
/-- HOL's generated flat-value size. Its complete typed equations, including
the environment, pair, and list auxiliaries, are captured as
`flat_value_size_def_typed` in `flat_elim_value_globals_probe.out`. -/
def valueSizeHOL : Value → Nat
  | .litv lit => 1 + AstHOL.litSizeHOL lit
  | .conv tag vs =>
      1 + (optionSizeHOL (pairSizeHOL id (optionSizeHOL id)) tag + valueListSizeHOL vs)
  | .closure env name body =>
      1 + (environmentSizeHOL env + (mlstringSizeHOL name + FlatLang.expSizeHOL body))
  | .recclosure env bindings name =>
      1 + (environmentSizeHOL env +
        (listSizeHOL (pairSizeHOL mlstringSizeHOL
          (pairSizeHOL mlstringSizeHOL FlatLang.expSizeHOL)) bindings + mlstringSizeHOL name))
  | .loc flag n => 1 + (boolSizeHOL flag + n)
  | .vectorv vs => 1 + valueListSizeHOL vs

/-- HOL's generated `v1_size`, the value-environment size. -/
def environmentSizeHOL : Environment Value → Nat
  | ⟨values⟩ => 1 + environmentListSizeHOL values

/-- HOL's generated `v2_size`, the environment-list size. -/
def environmentListSizeHOL : List (AstHOL.VarN × Value) → Nat
  | [] => 0
  | pair :: rest => 1 + (valuePairSizeHOL pair + environmentListSizeHOL rest)

/-- HOL's generated `v3_size`, the environment-entry size. -/
def valuePairSizeHOL : (AstHOL.VarN × Value) → Nat
  | (name, value) => 1 + (mlstringSizeHOL name + valueSizeHOL value)

/-- HOL's generated `v4_size`, the value-list size. -/
def valueListSizeHOL : List Value → Nat
  | [] => 0
  | value :: rest => 1 + (valueSizeHOL value + valueListSizeHOL rest)
end

end Flapjack.Compiler.Backend.FlatSem
