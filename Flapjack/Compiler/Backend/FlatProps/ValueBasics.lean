import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Basic flat values and their recursively contained values. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

/-- Building recursive bindings is an ordered prefix of closures. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "build_rec_env_eq_MAP"]
theorem buildRecEnv_eq_map (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (initial : List (Flapjack.AstHOL.VarN × FlatSem.Value)) :
    FlatSem.buildRecEnv funs env initial =
      funs.map (fun f => (f.1, FlatSem.Value.recclosure env funs f.1)) ++ initial := by
  unfold FlatSem.buildRecEnv
  have foldMap : ∀ xs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp),
      xs.foldr (fun (f, _, _) acc => (f, FlatSem.Value.recclosure env funs f) :: acc) initial =
        xs.map (fun f => (f.1, FlatSem.Value.recclosure env funs f.1)) ++ initial := by
    intro xs
    induction xs with
    | nil => rfl
    | cons first rest ih =>
      rcases first with ⟨name, arg, body⟩
      simp [ih]
  exact foldMap funs

/-- A closure value is either a single or recursive closure. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "isClosure_def"]
def isClosure (value : Value) : Prop :=
  (∃ env name body, value = .closure env name body) ∨
    ∃ env functions name, value = .recclosure env functions name

@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_basic_val_rel_def"]
def simpleBasicValRel : Value → Value → Prop
  | .litv lit, value => value = .litv lit
  | .loc flag index, value => value = .loc flag index
  | .conv stamp _, value => ∃ values, value = .conv stamp values
  | .vectorv _, value => ∃ values, value = .vectorv values
  | .closure _ _ _, _ | .recclosure _ _ _, _ => False

@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "v_container_xs_def"]
def valueContainerXs : Value → List Value
  | .conv _ values | .vectorv values => values
  | _ => []

end Flapjack.Compiler.Backend.FlatProps
