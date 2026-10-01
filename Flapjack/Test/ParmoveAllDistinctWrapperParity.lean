import Flapjack.Compiler.Backend.Parmove.AllDistinct.Parmove

namespace Flapjack.Test.ParmoveAllDistinctWrapperParity
open Compiler.Backend.Parmove

/-! Full-output kernel replay of the original scheduler observations in
`parmove_all_distinct_wrapper_probe.out`. Each valid case also applies the
complete distinctness theorem with its original input premise. -/
private theorem applies (moves : List (Nat × Nat)) (distinct : (moves.map Prod.fst).Nodup) :
    (((parmove moves).map Prod.fst).filter Option.isSome).Nodup :=
  allDistinctParmove moves distinct

example : parmove ([] : List (Nat × Nat)) = [] := by decide +kernel
example : parmove [(0, 0)] = [] := by decide +kernel
example : parmove [(0, 1), (1, 2)] = [(some 0, some 1), (some 1, some 2)] := by
  decide +kernel
example : parmove [(0, 1), (1, 0)] =
    [(none, some 1), (some 1, some 0), (some 0, none)] := by decide +kernel
example : parmove [(0, 1), (1, 2), (2, 0)] =
    [(none, some 1), (some 1, some 2), (some 2, some 0), (some 0, none)] := by
  decide +kernel
example : parmove [(0, 2), (1, 2)] = [(some 0, some 2), (some 1, some 2)] := by
  decide +kernel

example : (((parmove ([] : List (Nat × Nat))).map Prod.fst).filter Option.isSome).Nodup :=
  applies [] (by decide +kernel)
example : (((parmove [(0, 0)]).map Prod.fst).filter Option.isSome).Nodup :=
  applies [(0, 0)] (by decide +kernel)
example : (((parmove [(0, 1), (1, 2)]).map Prod.fst).filter Option.isSome).Nodup :=
  applies [(0, 1), (1, 2)] (by decide +kernel)
example : (((parmove [(0, 1), (1, 0)]).map Prod.fst).filter Option.isSome).Nodup :=
  applies [(0, 1), (1, 0)] (by decide +kernel)
example : (((parmove [(0, 1), (1, 2), (2, 0)]).map Prod.fst).filter Option.isSome).Nodup :=
  applies [(0, 1), (1, 2), (2, 0)] (by decide +kernel)
example : (((parmove [(0, 2), (1, 2)]).map Prod.fst).filter Option.isSome).Nodup :=
  applies [(0, 2), (1, 2)] (by decide +kernel)

example : ¬ ([(0, 1), (0, 2)].map Prod.fst).Nodup ∧
    ¬ (((parmove [(0, 1), (0, 2)]).map Prod.fst).filter Option.isSome).Nodup := by
  decide +kernel

example : (((parmove [(false, true), (true, false)]).map Prod.fst).filter Option.isSome).Nodup :=
  allDistinctParmove _ (by decide +kernel)

end Flapjack.Test.ParmoveAllDistinctWrapperParity
