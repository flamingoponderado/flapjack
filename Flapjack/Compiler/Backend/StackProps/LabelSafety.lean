import Flapjack.Compiler.Backend.StackProps.CodeLabels
import Flapjack.Compiler.Backend.BackendProps

namespace Flapjack.Compiler.Backend.StackProps
open StackLang

/-- Whole-program referenced labels are covered by owned handlers, program
entries zero/one, or arbitrary external entries zero/one. HOL sets remain sets;
no finiteness or uniqueness hypothesis is imposed on the external labels. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stackGoodCodeLabels {width : Nat} [NeZero width]
    (program : List (Nat × HolProg width)) (externalLabels : Set Nat) : Prop :=
  ⋃₀ (getCodeLabels '' {body | body ∈ program.map Prod.snd}) ⊆
    ⋃₀ {labels | labels ∈ program.map (fun (name, body) => stackGetHandlerLabels name body)} ∪
      (fun name => (name, 0)) '' {name | name ∈ program.map Prod.fst} ∪
      (fun name => (name, 0)) '' externalLabels ∪
      (fun name => (name, 1)) '' {name | name ∈ program.map Prod.fst} ∪
      (fun name => (name, 1)) '' externalLabels

/-- Nonzero referenced entries must be owned handlers or program entry one.
This is the full source predicate, with no successful evaluation premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stackGoodHandlerLabels {width : Nat} [NeZero width]
    (program : List (Nat × HolProg width)) : Prop :=
  BackendProps.restrictNonzero
      (⋃₀ (getCodeLabels '' {body | body ∈ program.map Prod.snd})) ⊆
    ⋃₀ {labels | labels ∈ program.map (fun (name, body) => stackGetHandlerLabels name body)} ∪
      (fun name => (name, 1)) '' {name | name ∈ program.map Prod.fst}

end Flapjack.Compiler.Backend.StackProps
