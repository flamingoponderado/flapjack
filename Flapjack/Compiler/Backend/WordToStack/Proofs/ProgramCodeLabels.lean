import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCodeLabels
import Mathlib.Data.Set.Lattice

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific proof support: unfold actual per-row frame sizing and
apply the full comp bound; this packaging has no separately named HOL original. -/
private theorem compileProgLabelBound {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (arguments registers : Nat) (bs : AppList (BitVec width) × Nat) (owner : Nat)
    (good : goodHandlersHOL owner program = true) (noPerf : perf = false) :
    getCodeLabels (compileProgNative conf perf program arguments registers bs).1 ⊆
      insert (raiseStubLocation,0) (insert (storeConstsStubLocation,0)
        ((fun label => (label,0)) '' getCodeLabelsHOL program ∪
          stackGetHandlerLabels owner (compileProgNative conf perf program arguments registers bs).1)) := by
  let variables := max ((maxVarHOL program / 2 + 1) - registers) (arguments - registers)
  let frame := if variables = 0 then 0 else variables + 1
  have bound := wordToStackCompCodeLabels conf perf program bs (registers,frame,variables)
    owner good noPerf
  simpa only [compileProgNative, variables, frame, getCodeLabels,
    stackGetHandlerLabels, Set.empty_union] using bound

/-- Flapjack-specific list-to-set notation for the row induction; no named
HOL declaration is claimed for this elementary membership equation. -/
private theorem memListConsSet {α : Type} (a : α) (xs : List α) :
    {x | x ∈ a :: xs} = insert a {x | x ∈ xs} := by
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff]

/-- Full original whole-program union bound. The original EVERY guard, perf=F,
and complete output equation (including frames and bitmap residual) are retained.
Only the positive HOL word dimension is translated to BitVec width. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileWordToStackCodeLabels {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (bodies : List (Nat × HolProg width))
    (residual : List Nat × (AppList (BitVec width) × Nat))
    (good : rows.all (fun row => goodHandlersHOL row.1 row.2.2) = true)
    (noPerf : perf = false)
    (compiled : compileWordToStackNative conf perf registers rows bs = (bodies,residual)) :
    Set.sUnion (getCodeLabels '' {p | p ∈ bodies.map Prod.snd}) ⊆
      insert (raiseStubLocation,0) (insert (storeConstsStubLocation,0)
        ((fun label => (label,0)) ''
          Set.sUnion {labels | labels ∈ rows.map (fun row => getCodeLabelsHOL row.2.2)} ∪
          Set.sUnion {labels | labels ∈ bodies.map (fun row => stackGetHandlerLabels row.1 row.2)})) := by
  subst perf
  revert good compiled
  induction rows generalizing bs bodies residual with
  | nil =>
    intro good compiled
    simp only [compileWordToStackNative] at compiled
    cases compiled
    simp
  | cons row rows ih =>
    rcases row with ⟨owner,arguments,program⟩
    intro good compiled
    have guards : goodHandlersHOL owner program = true ∧
        rows.all (fun row => goodHandlersHOL row.1 row.2.2) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using good
    rcases hp : compileProgNative conf false program arguments registers bs with
      ⟨body,frame,next⟩
    rcases ht : compileWordToStackNative conf false registers rows next with
      ⟨tailBodies,tailFrames,tailState⟩
    have equation : ((owner,body)::tailBodies,frame::tailFrames,tailState) =
        (bodies,residual) := by
      simpa only [compileWordToStackNative,hp,ht] using compiled
    cases equation
    have tailBound := ih next tailBodies (tailFrames,tailState) guards.2 ht
    have headBound := compileProgLabelBound conf false program arguments registers bs
      owner guards.1 rfl
    simp only [hp] at headBound
    simp only [List.map_cons,memListConsSet,Set.image_insert_eq,Set.sUnion_insert,
      Set.image_union]

    simp only [Set.subset_def,Set.mem_insert_iff,Set.mem_union] at headBound tailBound ⊢
    intro label member
    rcases member with member | member
    · rcases headBound label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases tailBound label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Flapjack.Compiler.Backend.WordToStack.Native
