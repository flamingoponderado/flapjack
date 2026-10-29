import Flapjack.HolRef

/-! Pure compiler and oracle transformations from the backend properties. -/
namespace Flapjack.Compiler.Backend.BackendProps

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_cc_def"]
def pureCc {Config Input Output Result : Type} (f : Input → Output)
    (compiler : Config → Output → Result) : Config → Input → Result :=
  fun config program => compiler config (f program)

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_def"]
def pureCo {Config Input Output : Type} (f : Input → Output) : Config × Input → Config × Output :=
  fun (config, program) => (config, f program)

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "SND_pure_co"]
theorem snd_pureCo {Config Input Output : Type} (f : Input → Output) (x : Config × Input) :
    (pureCo f x).2 = f x.2 := by cases x <;> rfl

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "FST_pure_co"]
theorem fst_pureCo {Config Input Output : Type} (f : Input → Output) (x : Config × Input) :
    (pureCo f x).1 = x.1 := by cases x <;> rfl

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_comb_pure_co"]
theorem pureCo_comp {Config A B D Index : Type} (f : B → D) (g : A → B)
    (oracle : Index → Config × A) :
    pureCo f ∘ pureCo g ∘ oracle = pureCo (f ∘ g) ∘ oracle := by
  funext i
  cases oracle i <;> rfl

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_I"]
theorem pureCo_id {Config A : Type} : pureCo (id : A → A) = (id : Config × A → Config × A) := by
  funext x
  cases x <;> rfl

@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_cc_I"]
theorem pureCc_id {Config A Result : Type} :
    pureCc (id : A → A) = (id : (Config → A → Result) → (Config → A → Result)) := by
  rfl

end Flapjack.Compiler.Backend.BackendProps
