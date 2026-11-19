module

public import Flapjack.Misc.SetSep

@[expose] public section

/-! Reading a singleton from a separated functional heap. -/
namespace Flapjack.SetSep

/-- A separated singleton in a functional heap determines its value and domain membership. -/
@[hol "HOL/examples/machine-code/hoare-triple/set_sepScript.sml" "read_fun2set"]
theorem readFun2Set {α β : Type} (address : β) (value : α)
    (frame : ((β × α) → Prop) → Prop) (function : β → α) (domain : β → Prop)
    (hypothesis : star (one (address, value)) frame (fun2Set (function, domain))) :
    function address = value ∧ domain address := by
  obtain ⟨head, _, partition, singleton, _⟩ := hypothesis
  have inHead : head (address, value) := by rw [singleton]
  have graph : fun2Set (function, domain) (address, value) := by
    rw [← partition.1]
    exact Or.inl inHead
  exact (fun2SetThm function domain address value).mp graph

end Flapjack.SetSep
