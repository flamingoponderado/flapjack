module

public import Flapjack.Compiler.Backend.ClosToBvl.ExtractName
public import Flapjack.Misc.Option
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Choice-based source entry-location extraction. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang

/-- Original extraction uses HOL's optional choice over nonnegative entry
constants. The selected location is unique when a witness exists. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "extract_name_def"]
noncomputable def extractNameSource : List Exp → Nat × List Exp
  | [] => (0, [])
  | x :: xs =>
    match Flapjack.holOptionSome (fun n : Nat => ∃ t, x = .op t (.intOp (.const (.ofNat n))) []) with
    | none => (0, x :: xs)
    | some n => (n, if xs = [] then [x] else xs)

/-- The original optional choice agrees with the executable pattern match. -/
theorem extractNameSource_eq_extractName (xs : List Exp) :
    extractNameSource xs = extractName xs := by
  classical
  cases xs with
  | nil => rfl
  | cons x xs =>
    by_cases h : ∃ n : Nat, ∃ t, x = .op t (.intOp (.const (.ofNat n))) []
    · obtain ⟨n, t, rfl⟩ := h
      have selected : Flapjack.holOptionSome (fun k : Nat =>
          ∃ u, Exp.op t (.intOp (.const (.ofNat n))) [] = .op u (.intOp (.const (.ofNat k))) []) = some n := by
        apply (Flapjack.holOptionSome_eq_some_iff _ ?_ _).2
        · exact ⟨t, rfl⟩
        · intro a b ha hb
          obtain ⟨u, hu⟩ := ha
          obtain ⟨v, hv⟩ := hb
          simp only [Exp.op.injEq, Op.intOp.injEq, IntOp.const.injEq, Int.ofNat.injEq] at hu hv
          simp_all
      simp only [extractNameSource, selected]
      cases xs <;> simp [extractName]
    · have absent : Flapjack.holOptionSome (fun n : Nat =>
          ∃ t, x = .op t (.intOp (.const (.ofNat n))) []) = none := by
        unfold Flapjack.holOptionSome
        rw [dite_eq_right h]
      simp only [extractNameSource, absent]
      cases x <;> simp_all [extractName]
      case op t op args =>
        split <;> simp_all
        exact (h _ rfl).elim

/-- The source choice reduces to the original pattern match on the first
expression, preserving a singleton entry constant. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "extract_name_pmatch"]
theorem extractNameSource_pmatch (xs : List Exp) :
    extractNameSource xs =
      match xs with
      | [] => (0, xs)
      | x :: rest =>
        match x with
        | .op _ (.intOp (.const i)) [] =>
            if i < 0 then (0, x :: rest)
            else (i.natAbs, if rest = [] then [x] else rest)
        | _ => (0, x :: rest) := by
  rw [extractNameSource_eq_extractName]
  cases xs with
  | nil => rfl
  | cons x rest =>
    cases x <;> simp [extractName]
    case op t operation args =>
      cases operation <;> try simp
      case intOp op =>
        cases op <;> try simp
        case const i =>
          cases i <;> cases args <;> simp <;> try omega
          case ofNat.nil => cases rest <;> simp <;> omega

end Flapjack.Compiler.Backend.ClosToBvl
