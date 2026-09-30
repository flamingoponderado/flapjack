import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.StackLang.Prog

/-!
# StackSem label collection and location checking

Exact positive-width definitions from `stackSemScript.sml`: `get_labels_def`
and `loc_check_def` are getLabelsExact and locCheckExact. Generic ProgM helpers
remain untagged: their arbitrary payload type is not the reviewed HolProg carrier. These helpers are part of the HOL semantics, not Flapjack-only
infrastructure. As in the rest of this port, HOL sets are represented as
predicates (`Nat × Nat → Prop`); the code map uses the reviewed Spt carrier.
-/

namespace Flapjack.StackSem

open Flapjack.Compiler.Backend.StackLang

/-- Untagged generic observation helper corresponding to the label clauses.
Its arbitrary ProgM payload carrier is not a claimed exact HOL port. Collect
return and handler continuation labels as well as labels recursively nested
inside those continuations. -/
def getLabels {α : Type} : ProgM α → (Nat × Nat) → Prop
  | .seq first second => fun label => getLabels first label ∨ getLabels second label
  | .ite _ _ _ thenBranch elseBranch =>
      fun label => getLabels thenBranch label ∨ getLabels elseBranch label
  | .loop body => getLabels body
  | .call returnHandler _ handler =>
      match returnHandler with
      | none => fun _ => False
      | some (body, _link, first, second) =>
          let handlerLabels :=
            match handler with
            | none => fun _ => False
            | some (handlerBody, handlerFirst, handlerSecond) =>
                fun label => label = (handlerFirst, handlerSecond) ∨
                  getLabels handlerBody label
          fun label => label = (first, second) ∨ getLabels body label ∨
            handlerLabels label
  | _ => fun _ => False
termination_by program => sizeOf program
decreasing_by all_goals simp_wf <;> omega

/-- Untagged generic location observation helper; see locCheckExact for the
faithful positive-width carrier signature. A label with
zero second component is also accepted when its first component is a code-map
key; otherwise it must be one of the labels found in a stored program. -/
def locCheck {α : Type}
    (code : Spt (ProgM α)) (labels : Nat × Nat) : Prop :=
  (labels.2 = 0 ∧ sptMem labels.1 code) ∨
    ∃ key program, sptLookup key code = some program ∧ getLabels program labels

/-- Source-shaped label set on the reviewed positive-width HOL program carrier.
Sets are predicates; ignored instruction payloads remain on the exact carrier. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_labels_def"
  (words_as_type_indexed_bitvec)]
def getLabelsExact {width : Nat} [NeZero width] : HolProg width → (Nat × Nat) → Prop
  | .seq first second => fun label => getLabelsExact first label ∨ getLabelsExact second label
  | .ite _ _ _ thenBranch elseBranch =>
      fun label => getLabelsExact thenBranch label ∨ getLabelsExact elseBranch label
  | .loop body => getLabelsExact body
  | .call returnHandler _ handler =>
      match returnHandler with
      | none => fun _ => False
      | some (body, _link, first, second) =>
          let handlerLabels :=
            match handler with
            | none => fun _ => False
            | some (handlerBody, handlerFirst, handlerSecond) =>
                fun label => label = (handlerFirst, handlerSecond) ∨
                  getLabelsExact handlerBody label
          fun label => label = (first, second) ∨ getLabelsExact body label ∨
            handlerLabels label
  | _ => fun _ => False
termination_by program => sizeOf program
decreasing_by all_goals simp_wf <;> omega

/-- Source-shaped location check, retaining the existential successful lookup
of an actual HolProg and membership in its exact label set. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "loc_check_def"
  (words_as_type_indexed_bitvec)]
def locCheckExact {width : Nat} [NeZero width]
    (code : Spt (HolProg width)) (labels : Nat × Nat) : Prop :=
  (labels.2 = 0 ∧ sptMem labels.1 code) ∨
    ∃ key program, sptLookup key code = some program ∧ getLabelsExact program labels

end Flapjack.StackSem

namespace Flapjack.StackSemLabels

open Flapjack.Compiler.Backend.StackLang

/-- Forget the exact instruction payloads for label observation.  The HOL
    label equations inspect only `Seq`, `Ite`, `Loop`, and `Call` structure;
    every other constructor is a leaf for this observation.  This adapter lets
    width-indexed `HolProg` observations be compared with the generic helper.
    The kernel theorem below proves precisely label equality; this erasing
    projection is not a full carrier codec. It is Flapjack-specific infrastructure,
    not a separate HOL declaration. -/
def labelsProgram {width : Nat} [NeZero width] : HolProg width → ProgM (BitVec width)
  | .seq first second => .seq (labelsProgram first) (labelsProgram second)
  | .ite _ _ _ thenBranch elseBranch =>
      .ite .equal 0 (.imm (0 : BitVec width))
        (labelsProgram thenBranch) (labelsProgram elseBranch)
  | .loop body => .loop (labelsProgram body)
  | .call none _ none => .call none (.inl 0) none
  | .call none _ (some (handlerBody, handlerFirst, handlerSecond)) =>
      .call none (.inl 0)
        (some (labelsProgram handlerBody, handlerFirst, handlerSecond))
  | .call (some (body, link, first, second)) _ none =>
      .call (some (labelsProgram body, link, first, second)) (.inl 0) none
  | .call (some (body, link, first, second)) _
      (some (handlerBody, handlerFirst, handlerSecond)) =>
      .call (some (labelsProgram body, link, first, second)) (.inl 0)
        (some (labelsProgram handlerBody, handlerFirst, handlerSecond))
  | _ => .skip
termination_by program => sizeOf program
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack-only observation correspondence. This proves label equality for
the erasing projection, not an equivalence of full program carriers. -/
theorem getLabelsExact_eq_generic {width : Nat} [NeZero width] (p : HolProg width) :
    Flapjack.StackSem.getLabelsExact p =
      Flapjack.StackSem.getLabels (labelsProgram p) := by
  induction p using labelsProgram.induct <;>
    try simp_all [Flapjack.StackSem.getLabelsExact, Flapjack.StackSem.getLabels, labelsProgram]
  case case8 p hseq hif hloop hc1 hc2 hc3 hc4 =>
    cases p <;> simp_all [Flapjack.StackSem.getLabelsExact]
    case ite => exact False.elim (hif _ _ _ _ _ rfl rfl rfl rfl rfl)
    case call returns target handler =>
      cases returns with
      | none =>
          cases handler with
          | none => exact False.elim (hc1 rfl rfl)
          | some hand =>
              obtain ⟨body, first, second⟩ := hand
              exact False.elim (hc2 _ _ _ _ rfl rfl rfl)
      | some ret =>
          obtain ⟨body, link, first, second⟩ := ret
          cases handler with
          | none => exact False.elim (hc3 body link first second rfl rfl)
          | some hand =>
              obtain ⟨handlerBody, handlerFirst, handlerSecond⟩ := hand
              exact False.elim (hc4 body link first second target handlerBody handlerFirst handlerSecond rfl rfl rfl)

/-- Flapjack-only code observation projection: preserves the sparse-tree
shape and maps stored programs through labelsProgram. No full carrier codec
or executed evaluator routing claim is made. -/
def labelsCode {width : Nat} [NeZero width] :
    Spt (HolProg width) → Spt (ProgM (BitVec width))
  | .ln => .ln
  | .ls p => .ls (labelsProgram p)
  | .bn left right => .bn (labelsCode left) (labelsCode right)
  | .bs left p right => .bs (labelsCode left) (labelsProgram p) (labelsCode right)

/-- Flapjack-only lookup preservation for the code observation projection. -/
theorem lookup_labelsCode {width : Nat} [NeZero width]
    (code : Spt (HolProg width)) (key : Nat) :
    sptLookup key (labelsCode code) = (sptLookup key code).map labelsProgram := by
  induction code generalizing key <;> simp_all [labelsCode, sptLookup]
  all_goals split <;> try simp_all
  all_goals split <;> try simp_all

/-- Flapjack-only domain preservation for the code observation projection. -/
theorem mem_labelsCode {width : Nat} [NeZero width]
    (code : Spt (HolProg width)) (key : Nat) :
    sptMem key (labelsCode code) ↔ sptMem key code := by
  rw [sptMem_iff_lookup, sptMem_iff_lookup, lookup_labelsCode]
  cases sptLookup key code <;> simp

/-- Flapjack-only location observation correspondence. Both sides retain an
actual successful lookup and its program's labels; no target-location premise
or weakened existential is introduced. -/
theorem locCheckExact_iff_generic {width : Nat} [NeZero width]
    (code : Spt (HolProg width)) (label : Nat × Nat) :
    Flapjack.StackSem.locCheckExact code label ↔
      Flapjack.StackSem.locCheck (labelsCode code) label := by
  simp only [Flapjack.StackSem.locCheckExact, Flapjack.StackSem.locCheck, mem_labelsCode]
  constructor
  · rintro (h | ⟨key, program, hl, hp⟩)
    · exact Or.inl h
    · refine Or.inr ⟨key, labelsProgram program, ?_, ?_⟩
      · rw [lookup_labelsCode, hl]; rfl
      · rw [← getLabelsExact_eq_generic]; exact hp
  · rintro (h | ⟨key, program, hl, hp⟩)
    · exact Or.inl h
    · rw [lookup_labelsCode] at hl
      cases hlook : sptLookup key code with
      | none => simp [hlook] at hl
      | some original =>
          simp only [hlook, Option.map_some, Option.some.injEq] at hl
          subst program
          exact Or.inr ⟨key, original, hlook, by rw [getLabelsExact_eq_generic]; exact hp⟩

/-- Width-indexed consumer API now uses the tagged exact definition. Its
relationship to the generic projection is proved above, not assumed. -/
abbrev getLabels {width : Nat} [NeZero width] : HolProg width → (Nat × Nat) → Prop :=
  Flapjack.StackSem.getLabelsExact

end Flapjack.StackSemLabels
