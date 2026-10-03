import Flapjack.Pancake.WordConvs.ProgramMonotonicity

/-! Complete original stack-occurrence predicate implications from wordConvs.
These are mathematical prerequisites of native allocator post conventions. -/

namespace Flapjack

/-- Original conjunction of both cut-set occurrence predicates. The two
literal Spt/list enumerations require no representation qualification. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_name_conj"]
theorem everyNameConj (P : Nat → Bool) (names : WordLangCutsetsHOL) (Q : Nat → Bool) :
    (everyNameHOL P names = true ∧ everyNameHOL Q names = true) ↔
      everyNameHOL (fun x => P x && Q x) names = true := by
  simp only [everyNameHOL, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨pLeft, pRight⟩, ⟨qLeft, qRight⟩⟩
    exact ⟨fun x member => ⟨pLeft x member, qLeft x member⟩,
      fun x member => ⟨pRight x member, qRight x member⟩⟩
  · rintro ⟨left, right⟩
    exact ⟨⟨fun x member => (left x member).1, fun x member => (right x member).1⟩,
      ⟨fun x member => (left x member).2, fun x member => (right x member).2⟩⟩

/-- Original full program occurrence implication to stack occurrences. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "every_var_imp_every_stack_var" (words_as_type_indexed_bitvec)]
theorem everyVarImpEveryStackVar {width : Nat} [NeZero width] (P : Nat → Bool)
    (prog : WordLangProgHOL (BitVec width)) :
    everyVarHOL P prog = true → everyStackVarHOL P prog = true := by
  induction prog using everyStackVarHOL.induct
  case case4 target arguments handler values names body label entry ihBody ihHandler =>
    cases handler with
    | none => simp_all [everyVarHOL, everyStackVarHOL]
    | some handler =>
      rcases handler with ⟨value, body, label, entry⟩
      simp_all [everyVarHOL, everyStackVarHOL]
  all_goals try simp_all [everyVarHOL, everyStackVarHOL]

/-- Original monotonicity for arbitrary stack-occurrence predicates. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "every_stack_var_mono" (words_as_type_indexed_bitvec)]
theorem everyStackVarMono {width : Nat} [NeZero width] (P : Nat → Bool)
    (prog : WordLangProgHOL (BitVec width)) (Q : Nat → Bool) :
    ((∀ x, P x = true → Q x = true) ∧ everyStackVarHOL P prog = true) →
      everyStackVarHOL Q prog = true := by
  rintro ⟨mono, valid⟩
  have nameMono (names : WordLangCutsetsHOL) := fun h => everyNameMono P names Q ⟨mono, h⟩
  revert valid
  induction prog using everyStackVarHOL.induct
  case case4 target arguments handler values names body label entry ihBody ihHandler =>
    cases handler with
    | none => simp_all [everyStackVarHOL]
    | some handler =>
      rcases handler with ⟨value, body, label, entry⟩
      simp_all [everyStackVarHOL]
  all_goals try simp_all [everyStackVarHOL]

/-- Original conjunction equivalence, over every constructor and cut-set field. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml"
  "every_stack_var_conj" (words_as_type_indexed_bitvec)]
theorem everyStackVarConj {width : Nat} [NeZero width] (P : Nat → Bool)
    (prog : WordLangProgHOL (BitVec width)) (Q : Nat → Bool) :
    (everyStackVarHOL P prog = true ∧ everyStackVarHOL Q prog = true) ↔
      everyStackVarHOL (fun x => P x && Q x) prog = true := by
  induction prog using everyStackVarHOL.induct
  case case4 target arguments handler values names body label entry ihBody ihHandler =>
    cases handler with
    | none => simp_all [everyStackVarHOL, ← everyNameConj]; aesop
    | some handler =>
      rcases handler with ⟨value, body, label, entry⟩
      simp_all [everyStackVarHOL, ← everyNameConj]
      aesop
  all_goals try simp_all [everyStackVarHOL, ← everyNameConj]
  all_goals aesop

end Flapjack
