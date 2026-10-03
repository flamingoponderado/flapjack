import Flapjack.Pancake.WordConvs
import Flapjack.HolArb

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

/-- Canonical HOL `ARB : memop`, sharing `Flapjack.holArb` with every other
HOL ARB occurrence at this carrier. The `.load` below witnesses only
nonemptiness; it does not specify the arbitrary value. This transparent alias
is Flapjack infrastructure, not another independent HOL constant. -/
noncomputable abbrev holArbMemOp : WordMemOp :=
  @Flapjack.holArb WordMemOp ⟨.load⟩

/-- Exact HOL `wordConvs$not_created_subprogs_def` (`wordConvsScript.sml:536-556`),
clause by clause, on the faithful Spt-backed program with HOL `ARB` as the
uninterpreted `holArbMemOp`. HOL's predicate is `bool`-valued (`P : 'a prog ->
bool`), as here. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "not_created_subprogs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def notCreatedSubprogsHOL {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) : WordLangProgHOL (BitVec width) → Bool
  | .mustTerminate body => P (.mustTerminate .skip) && notCreatedSubprogsHOL P body
  | .seq first second => notCreatedSubprogsHOL P first && notCreatedSubprogsHOL P second
  | .loop _ body _ => notCreatedSubprogsHOL P body
  | .ite _ _ _ first second => notCreatedSubprogsHOL P first && notCreatedSubprogsHOL P second
  | .call returns destination _ handler =>
      P (.call none destination [] none) &&
        (match returns with
          | none => true
          | some (_, _, body, _, _) => notCreatedSubprogsHOL P body) &&
        (match handler with
          | none => true
          | some (_, body, label, _) =>
              P (.call none none [] (some (0, .skip, label, 0))) &&
                notCreatedSubprogsHOL P body)
  | .alloc _ _ => P (.alloc 0 (.ln, .ln))
  | .locValue _ label => P (.locValue 0 label)
  | .shareInst _ _ _ => P (.shareInst holArbMemOp 0 (.var 0))
  | .install _ _ _ _ _ => P (.install 0 0 0 0 (.ln, .ln))
  | _ => true

/-- The exact checker is the choice-parametric checker at HOL's `ARB`
(Flapjack infrastructure). -/
theorem notCreatedSubprogsHOL_eq_withMemOp {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ program, notCreatedSubprogsHOL P program = notCreatedSubprogsWithMemOp holArbMemOp P program
  | .mustTerminate body => by
      simp only [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp,
        notCreatedSubprogsHOL_eq_withMemOp P body]
  | .seq first second | .ite _ _ _ first second => by
      simp only [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp,
        notCreatedSubprogsHOL_eq_withMemOp P first, notCreatedSubprogsHOL_eq_withMemOp P second]
  | .loop _ body _ => by
      simp only [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp,
        notCreatedSubprogsHOL_eq_withMemOp P body]
  | .call none _ _ none => by simp [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp]
  | .call none _ _ (some (_, body, _, _)) => by
      simp only [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp,
        notCreatedSubprogsHOL_eq_withMemOp P body]
  | .call (some (_, _, ret, _, _)) _ _ none => by
      simp only [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp,
        notCreatedSubprogsHOL_eq_withMemOp P ret]
  | .call (some (_, _, ret, _, _)) _ _ (some (_, body, _, _)) => by
      simp only [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp,
        notCreatedSubprogsHOL_eq_withMemOp P ret, notCreatedSubprogsHOL_eq_withMemOp P body]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by
      simp [notCreatedSubprogsHOL, notCreatedSubprogsWithMemOp]

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

/-- The tagged `no_*` specialisations are the exact `not_created_subprogs` at HOL's
predicates and HOL's `ARB` (Flapjack infrastructure linking the exact general
checker to the specialisations, whose original-HOL probe rows are replayed in
`Flapjack/Test/WordLangNotCreatedParity.lean`). -/
theorem noAllocSubprogsHOL_eq_notCreated {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    noAllocSubprogsHOL program = notCreatedSubprogsHOL
      (fun q => by classical exact decide (q ≠ .alloc 0 (.ln, .ln))) program := by
  rw [notCreatedSubprogsHOL_eq_withMemOp]; exact noAllocSubprogsHOL_eq_choice holArbMemOp program

theorem noInstallSubprogsHOL_eq_notCreated {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    noInstallSubprogsHOL program = notCreatedSubprogsHOL
      (fun q => by classical exact decide (q ≠ .install 0 0 0 0 (.ln, .ln))) program := by
  rw [notCreatedSubprogsHOL_eq_withMemOp]; exact noInstallSubprogsHOL_eq_choice holArbMemOp program

theorem noMtSubprogsHOL_eq_notCreated {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    noMtSubprogsHOL program = notCreatedSubprogsHOL
      (fun q => by classical exact decide (q ≠ .mustTerminate .skip)) program := by
  rw [notCreatedSubprogsHOL_eq_withMemOp]; exact noMtSubprogsHOL_eq_choice holArbMemOp program

theorem noShareInstSubprogsHOL_eq_notCreated {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    noShareInstSubprogsHOL program = notCreatedSubprogsHOL
      (fun q => by classical exact decide (q ≠ .shareInst holArbMemOp 0 (.var 0))) program := by
  rw [notCreatedSubprogsHOL_eq_withMemOp]
  exact noShareInstSubprogsHOL_eq_choice holArbMemOp program

end Flapjack
