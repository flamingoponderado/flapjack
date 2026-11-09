module

public import Flapjack.Compiler.Backend.ClosOp.Proofs.Reduction

@[expose] public section

/-! Source lifting preserves the reduction relation. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- Non-lifted source forms are simple; Flapjack proof infrastructure. -/
private theorem dontSimple (x : Exp) (h : dontLift x = true) : SimpleExp x := by
  rcases (dontLiftCharacterization x).mp h with ⟨t,i,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,s,rfl⟩ | ⟨t,i,rfl⟩ | ⟨t,w,rfl⟩
  · exact .intConst _ _
  · exact .cons _ _ _ (by simp)
  · exact .constStr _ _
  · exact .constInt _ _
  · exact .constWord64 _ _

/-- A matched constructor preserves its argument reduction; Flapjack proof infrastructure. -/
private theorem consRed (x : Exp) (tag : Nat) (ys zs : List Exp)
    (hc : cons x = some (tag, ys)) (h : RedRel ys zs) : RedRel [x] zs := by
  rw [destOpCons_eq_previous] at hc
  cases x <;> try simp at hc
  case op t op args =>
    cases op <;> try simp at hc
    case blockOp op =>
      cases op <;> try simp at hc
      case cons tag2 =>
        obtain ⟨rfl,rfl⟩ := hc
        exact .op 0 _ _ t _ (.const 0) 0 tag2 0 0 (.implode []) 0 h (by simp)

/-- General projection form of the lifting invariant; Flapjack proof infrastructure. -/
private theorem liftRed (xs : List Exp) (n : Nat) (binds : List Exp) :
    ∃ zs, RedRel xs zs ∧ RedRel ((liftExpsHOL xs n binds).2.2.drop binds.length) zs := by
  fun_induction liftExpsHOL xs n binds <;> simp_all
  case case1 => exact ⟨[], .nil⟩
  case case2 =>
    rename_i x xs n binds hd xs1 n1 binds1 hx ih
    obtain ⟨zs, hxs, hb⟩ := ih
    have hs := simpleExpRedRel [x] (by simpa using dontSimple x hd)
    exact ⟨zs, redRelCons x xs zs ⟨hs,hxs⟩, hb⟩
  case case3 =>
    rename_i x xs n binds tag ys ys1 n1 binds1 xs1 n2 binds2 hd hc hy hx ihy ihx
    obtain ⟨p, hp⟩ := liftExpsAcc ys n binds ys1 n1 binds1 hy
    obtain ⟨q, hq⟩ := liftExpsAcc xs n1 binds1 xs1 n2 binds2 hx
    obtain ⟨zy, hry, hpy⟩ := ihy
    obtain ⟨zx, hrx, hqx⟩ := ihx
    simp only [hp, List.drop_left] at hpy
    simp only [hq, List.drop_left] at hqx
    refine ⟨zy ++ zx, redRelConsZero x zy xs zx ⟨consRed x tag ys zy hc hry,hrx⟩, ?_⟩
    rw [hq, hp]
    simp only [List.append_assoc, List.drop_left]
    exact redRelAppend p zy q zx ⟨hpy,hqx⟩
  case case4 =>
    rename_i x xs n binds xs1 n1 binds1 hd hc hx ih
    obtain ⟨p, hp⟩ := liftExpsAcc xs (n+1) (binds ++ [x]) xs1 n1 binds1 hx
    obtain ⟨zs, hxs, hb⟩ := ih
    rw [hp] at hb ⊢
    have dropB : binds.drop (binds.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simp [List.drop_append, List.append_assoc, dropB] at hb
    simp only [List.append_assoc, List.drop_left]
    exact ⟨x :: zs, redRelConsOne xs zs x hxs, redRelConsOne p zs x hb⟩
/-- Original expressions and newly added bindings have a common residual. -/
@[hol "cakeml/compiler/backend/proofs/clos_opProofScript.sml" "lift_exps_red_rel"]
theorem liftExpsRedRel (xs : List Exp) (n : Nat) (binds ys : List Exp) (k : Nat) (binds2 : List Exp)
    (h : liftExpsHOL xs n binds = (ys,k,binds2)) :
    ∃ zs, RedRel xs zs ∧ RedRel (binds2.drop binds.length) zs := by
  have inv := liftRed xs n binds
  rw [h] at inv
  exact inv

end Flapjack.Compiler.Backend.ClosOp
