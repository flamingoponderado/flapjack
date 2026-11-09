module

public import Flapjack.HolRef

@[expose] public section

/-! Optional association-list binding from CakeML's misc theory. -/
namespace Flapjack

/-- Bind a name when present; otherwise leave the association list unchanged. -/
@[hol "cakeml/misc/miscScript.sml" "opt_bind_def"]
def optBind {K V : Type} (name : Option K) (value : V) (env : List (K × V)) : List (K × V) :=
  match name with
  | none => env
  | some key => (key, value) :: env

/-- Flapjack simplification infrastructure for the none case of `optBind`. -/
@[simp] theorem optBind_none_apply {K V : Type} (value : V) (env : List (K × V)) :
    optBind none value env = env := rfl

/-- Flapjack simplification infrastructure for the some case of `optBind`. -/
@[simp] theorem optBind_some_apply {K V : Type} (key : K) (value : V) (env : List (K × V)) :
    optBind (some key) value env = (key, value) :: env := rfl

end Flapjack
