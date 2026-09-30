import Flapjack.Pancake.WordConvs

/-! Boolean structural conventions on the exact WordLang syntax.
The general checker exposes HOL's unspecified `ARB : memop` as a parameter.
This extra parameter prevents an exact HOL tag on the general checker.
The specialized predicates below do not depend on that choice. -/

namespace Flapjack

/-- Flapjack's choice-parametric counterpart of `not_created_subprogs_def`.
Unlike the older Prop checker, this uses HOL-shaped Spt cut sets and returns
Bool. Its explicit `arb` argument is not part of the HOL signature. -/
def notCreatedSubprogsWithMemOp {α : Type} (arb : WordMemOp)
    (P : WordLangProgHOL α → Bool) : WordLangProgHOL α → Bool
  | .mustTerminate body => P (.mustTerminate .skip) && notCreatedSubprogsWithMemOp arb P body
  | .seq first second =>
      notCreatedSubprogsWithMemOp arb P first && notCreatedSubprogsWithMemOp arb P second
  | .loop _ body _ => notCreatedSubprogsWithMemOp arb P body
  | .ite _ _ _ first second =>
      notCreatedSubprogsWithMemOp arb P first && notCreatedSubprogsWithMemOp arb P second
  | .call returns destination _ handler =>
      P (.call none destination [] none) &&
        (match returns with
          | none => true
          | some (_, _, body, _, _) => notCreatedSubprogsWithMemOp arb P body) &&
        (match handler with
          | none => true
          | some (_, body, label, _) =>
              P (.call none none [] (some (0, .skip, label, 0))) &&
                notCreatedSubprogsWithMemOp arb P body)
  | .alloc _ _ => P (.alloc 0 (.ln, .ln))
  | .locValue _ label => P (.locValue 0 label)
  | .shareInst _ _ _ => P (.shareInst arb 0 (.var 0))
  | .install _ _ _ _ _ => P (.install 0 0 0 0 (.ln, .ln))
  | _ => true

/-- Flapjack-specific congruence on precisely the normalized nodes examined
by the HOL checker. It also permits changing the arbitrary memory operation.
There is no standalone HOL theorem with this statement. -/
theorem notCreatedSubprogsWithMemOp_congr {α : Type}
    (arb₁ arb₂ : WordMemOp) (P Q : WordLangProgHOL α → Bool)
    (hmt : P (.mustTerminate .skip) = Q (.mustTerminate .skip))
    (hcall : ∀ d, P (.call none d [] none) = Q (.call none d [] none))
    (hhandler : ∀ l, P (.call none none [] (some (0, .skip, l, 0))) =
      Q (.call none none [] (some (0, .skip, l, 0))))
    (halloc : P (.alloc 0 (.ln, .ln)) = Q (.alloc 0 (.ln, .ln)))
    (hloc : ∀ l, P (.locValue 0 l) = Q (.locValue 0 l))
    (hshare : P (.shareInst arb₁ 0 (.var 0)) = Q (.shareInst arb₂ 0 (.var 0)))
    (hinstall : P (.install 0 0 0 0 (.ln, .ln)) =
      Q (.install 0 0 0 0 (.ln, .ln)))
    (program : WordLangProgHOL α) :
    notCreatedSubprogsWithMemOp arb₁ P program =
      notCreatedSubprogsWithMemOp arb₂ Q program := by
  cases program with
  | mustTerminate body =>
      simp only [notCreatedSubprogsWithMemOp, hmt]
      rw [notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall body]
  | seq first second | ite _ _ _ first second =>
      simp only [notCreatedSubprogsWithMemOp]
      rw [notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall first,
        notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall second]
  | loop _ body _ =>
      exact notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall body
  | call returns destination arguments handler =>
      cases returns with
      | none =>
          cases handler with
          | none => simp [notCreatedSubprogsWithMemOp, hcall]
          | some data =>
              rcases data with ⟨value, body, label, location⟩
              simp only [notCreatedSubprogsWithMemOp, hcall, hhandler]
              rw [notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall body]
      | some data =>
          rcases data with ⟨values, cuts, body, label, location⟩
          cases handler with
          | none =>
              simp only [notCreatedSubprogsWithMemOp, hcall]
              rw [notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall body]
          | some data =>
              rcases data with ⟨value, handlerBody, handlerLabel, handlerLocation⟩
              simp only [notCreatedSubprogsWithMemOp, hcall, hhandler]
              rw [notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall body,
                notCreatedSubprogsWithMemOp_congr arb₁ arb₂ P Q hmt hcall hhandler halloc hloc hshare hinstall handlerBody]
  | alloc _ _ => exact halloc
  | locValue _ label => exact hloc label
  | shareInst _ _ _ => exact hshare
  | install _ _ _ _ _ => exact hinstall
  | _ => rfl
termination_by sizeOf program

/-- HOL's `no_alloc` specialization: on the normalized nodes inspected by
the checker, inequality with `Alloc 0 (LN,LN)` is exactly this constructor test.
The correspondence theorem below checks that simplification for every input
and every possible interpretation of `ARB`. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_alloc_subprogs_def"
  (words_as_type_indexed_bitvec)]
def noAllocSubprogsHOL {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  notCreatedSubprogsWithMemOp .load (fun q => match q with
    | .alloc _ _ => false
    | _ => true) program

/-- Boolean HOL-shaped `no_install` specialization; see its correspondence theorem. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_install_subprogs_def"
  (words_as_type_indexed_bitvec)]
def noInstallSubprogsHOL {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  notCreatedSubprogsWithMemOp .load (fun q => match q with
    | .install _ _ _ _ _ => false
    | _ => true) program

/-- Boolean HOL-shaped `no_mt` specialization; see its correspondence theorem. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_mt_subprogs_def"
  (words_as_type_indexed_bitvec)]
def noMtSubprogsHOL {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  notCreatedSubprogsWithMemOp .load (fun q => match q with
    | .mustTerminate _ => false
    | _ => true) program

/-- Boolean HOL-shaped `no_share_inst` specialization; the constructor test
removes dependence on the arbitrary memory operation. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_share_inst_subprogs_def"
  (words_as_type_indexed_bitvec)]
def noShareInstSubprogsHOL {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  notCreatedSubprogsWithMemOp .load (fun q => match q with
    | .shareInst _ _ _ => false
    | _ => true) program

/-- Flapjack-specific implementation certificate: the executable specialization
agrees with HOL's equality predicate for every possible `ARB` representative.
This is a correspondence lemma for the implementation, not a HOL theorem port. -/
theorem noAllocSubprogsHOL_eq_choice {width : Nat} [NeZero width]
    (arb : WordMemOp) (program : WordLangProgHOL (BitVec width)) :
    noAllocSubprogsHOL program = notCreatedSubprogsWithMemOp arb
      (fun q => by classical exact decide (q ≠ .alloc 0 (.ln, .ln))) program := by
  classical
  unfold noAllocSubprogsHOL
  apply notCreatedSubprogsWithMemOp_congr <;> simp

/-- Flapjack-specific implementation certificate: the executable specialization
agrees with HOL's equality predicate for every possible `ARB` representative.
This is a correspondence lemma for the implementation, not a HOL theorem port. -/
theorem noInstallSubprogsHOL_eq_choice {width : Nat} [NeZero width]
    (arb : WordMemOp) (program : WordLangProgHOL (BitVec width)) :
    noInstallSubprogsHOL program = notCreatedSubprogsWithMemOp arb
      (fun q => by classical exact decide (q ≠ .install 0 0 0 0 (.ln, .ln))) program := by
  classical
  unfold noInstallSubprogsHOL
  apply notCreatedSubprogsWithMemOp_congr <;> simp

/-- Flapjack-specific implementation certificate: the executable specialization
agrees with HOL's equality predicate for every possible `ARB` representative.
This is a correspondence lemma for the implementation, not a HOL theorem port. -/
theorem noMtSubprogsHOL_eq_choice {width : Nat} [NeZero width]
    (arb : WordMemOp) (program : WordLangProgHOL (BitVec width)) :
    noMtSubprogsHOL program = notCreatedSubprogsWithMemOp arb
      (fun q => by classical exact decide (q ≠ .mustTerminate .skip)) program := by
  classical
  unfold noMtSubprogsHOL
  apply notCreatedSubprogsWithMemOp_congr <;> simp

/-- Flapjack-specific implementation certificate: the executable specialization
agrees with HOL's equality predicate for every possible `ARB` representative.
This is a correspondence lemma for the implementation, not a HOL theorem port. -/
theorem noShareInstSubprogsHOL_eq_choice {width : Nat} [NeZero width]
    (arb : WordMemOp) (program : WordLangProgHOL (BitVec width)) :
    noShareInstSubprogsHOL program = notCreatedSubprogsWithMemOp arb
      (fun q => by classical exact decide (q ≠ .shareInst arb 0 (.var 0))) program := by
  classical
  unfold noShareInstSubprogsHOL
  apply notCreatedSubprogsWithMemOp_congr <;> simp

end Flapjack
