import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Call
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

/-! `flatten_correct` case `Install` (`stack_to_labProofScript.sml:2398-2519`):
installing the oracle's next programs extends the LabSem code with their
sections, preserving `state_rel` (in particular the installation of every
procedure, old and new). -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

section
variable {width : Nat} [NeZero width] {C F : Type}

theorem sptAListLookup_eq_holAlookup {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = holAlookup entries key
  | [] => rfl
  | (k, v) :: rest => by
    simp only [sptAListLookup, holAlookup]
    by_cases h : key = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
      exact sptAListLookup_eq_holAlookup key rest

theorem secLabelOkOfLabels {n : Nat} :
    ∀ (L : List (LabLineHOL width)),
      (∀ p ∈ LabProps.LabelSets.extractLabels L, p.1 = n ∧ p.2 ≠ 0) →
      ∀ line ∈ L, LabProps.secLabelOk n line := by
  intro L h line hl
  cases line with
  | label a b c =>
    have := h (a, b) (label_mem_extractLabels a b c L hl)
    exact ⟨this.1, this.2⟩
  | _ => trivial

theorem holAlookupIsSome_iff {α : Type} (entries : List (Nat × α)) (key : Nat) :
    (holAlookup entries key).isSome ↔ key ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [holAlookup]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases h : k = key
    · subst h; simp [holAlookup]
    · simp only [holAlookup, h, if_false, ih, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm h
        · exact e

/-- The code part of `state_rel` after installing the oracle's next programs:
old procedures stay installed, new ones are installed in the appended
sections, the domains agree and every section's labels stay well formed. -/
theorem installCode {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    {progs : List (Nat × HolProg width)} (hprogs : (s.compileOracle 0).2.1 = progs) :
    (∀ k prog, sptLookup k (sptUnion s.code (sptFromAList progs)) = some prog →
      StackProps.callArgs prog t.ptrReg t.lenReg t.ptr2Reg t.len2Reg t.linkReg ∧
      ∃ pc, codeInstalled pc (appListAppend (flattenHOL true prog k
          (StackAlloc.nextLabHOL prog 2) [] []).1) (t.code ++ progs.map progToSectionHOL) ∧
        locToPc k 0 (t.code ++ progs.map progToSectionHOL) = some pc) ∧
    (∀ x, sptDomain (sptUnion s.code (sptFromAList progs)) x ↔
      x ∈ (t.code ++ progs.map progToSectionHOL).map (·.sectionId)) ∧
    (∀ sec ∈ t.code ++ progs.map progToSectionHOL, LabProps.secLabelsOk sec) := by
  obtain ⟨-, -, -, -, -, -, -, -, hcode, hdom, hsec, -, -, -, -, -, -, -, -, -, -, -, -, -,
    horc, -⟩ := rel
  obtain ⟨hk1, hk2⟩ := horc 0
  rw [hprogs] at hk1 hk2
  have lok : labelsOk (progs.map progToSectionHOL) :=
    progToSectionLabelsOk ⟨fun np h => ⟨fun p hp => (hk1 np h).2.1 p hp, (hk1 np h).2.2⟩, hk2⟩
  obtain ⟨secNew, -, -⟩ := labelsOkImp _ lok
  have lookNew : ∀ k, sptLookup k (sptFromAList progs) = holAlookup progs k := fun k => by
    rw [sptLookup_sptFromAList, sptAListLookup_eq_holAlookup]
  refine ⟨?_, ?_, ?_⟩
  · intro k prog h
    rw [sptLookup_sptUnion] at h
    split at h
    · rename_i v hv
      cases h
      obtain ⟨ca, pc, inst, entry⟩ := hcode k prog hv
      exact ⟨ca, pc, codeInstalledAppend _ _ _ _ inst, locToPcAppend _ _ _ _ _ entry⟩
    · rename_i hnone
      rw [lookNew] at h
      have mem := holAlookup_mem _ _ _ h
      have ca := (hk1 (k, prog) mem).1
      obtain ⟨pc, instN, entryN⟩ := codeInstalledProgToSection progs k prog ⟨lok, h⟩
      have notMem : k ∉ t.code.map (·.sectionId) := by
        intro hm
        have := (hdom k).mpr hm
        simp [sptDomain, hnone] at this
      have labOk : ∀ line ∈ appListAppend (flattenHOL true prog k
          (StackAlloc.nextLabHOL prog 2) [] []).1, LabProps.secLabelOk k line := by
        apply secLabelOkOfLabels
        intro p hp
        have hsecMem : progToSectionHOL (k, prog) ∈ progs.map progToSectionHOL :=
          List.mem_map_of_mem mem
        have := lok.2 _ hsecMem
        rw [progToSection_eq] at this
        apply this.1 p
        rw [LabProps.LabelSets.extractLabels_append]
        exact List.mem_append_left _ hp
      refine ⟨ca, codeLength t.code + pc,
        codeInstalledAppend2 _ _ _ _ k ⟨notMem, hsec, labOk, instN⟩, ?_⟩
      rw [locToPcAppend2 k 0 _ _ pc ⟨notMem, hsec, entryN⟩, Nat.add_comm]
  · intro x
    rw [sptDomain_sptUnion]
    simp only [List.map_append, List.mem_append, mapProgToSectionFst]
    rw [← hdom x]
    simp only [sptDomain, lookNew, holAlookupIsSome_iff]
  · intro sec hs
    rcases List.mem_append.mp hs with h | h
    · exact hsec sec h
    · exact secNew sec h

end

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
