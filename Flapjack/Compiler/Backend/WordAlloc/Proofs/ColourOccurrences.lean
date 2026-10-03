import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.Compiler.Backend.WordAlloc.TotalColour
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyMaps
import Flapjack.Pancake.WordConvs.ProgramMonotonicity
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.MaxVar

/-! Original occurrence transport under arbitrary colouring in word_allocProof.
Renaming need not be injective, and the Spt inputs need not be well formed. -/

namespace Flapjack.WordAlloc
open Flapjack

/-- Original instruction occurrence transport with arbitrary source and target
predicates and the original pointwise implication premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_inst_apply_colour_inst" (words_as_type_indexed_bitvec)]
theorem everyVarInst_applyColourInst {width : Nat} [NeZero width] (P : Nat → Bool)
    (inst : WordLangInst (BitVec width)) (Q : Nat → Bool) (f : Nat → Nat) :
    everyVarInstHOL P inst = true ∧ (∀ x, P x = true → Q (f x) = true) →
      everyVarInstHOL Q (applyColourInst f inst) = true := by
  rintro ⟨valid, image⟩
  cases inst with
  | skip => simp [everyVarInstHOL, applyColourInst, applyColourInstCore]
  | const r w => simp_all [everyVarInstHOL, applyColourInst, applyColourInstCore]
  | arith a =>
      cases a with
      | binop op r1 r2 ri | shift op r1 r2 ri =>
          cases ri <;> simp_all [everyVarInstHOL, everyVarImmHOL, applyColourInst,
            applyColourInstCore, applyColourImmCore]
      | div r1 r2 r3 | longMul r1 r2 r3 r4 | longDiv r1 r2 r3 r4 r5
      | addCarry r1 r2 r3 r4 | addOverflow r1 r2 r3 r4 | subOverflow r1 r2 r3 r4 =>
          simp_all [everyVarInstHOL, applyColourInst, applyColourInstCore]
  | mem op r addr =>
      cases op <;> cases addr <;>
        simp_all [everyVarInstHOL, applyColourInst, applyColourInstCore]
  | fp op =>
      cases op <;> simp_all [everyVarInstHOL, applyColourInst, applyColourInstCore]
      all_goals by_cases dimension : width = 64 <;> simp_all

/-- Original full expression occurrence transport, including recursive operator
argument lists and both Shift operands. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_exp_apply_colour_exp" (words_as_type_indexed_bitvec)]
theorem everyVarExp_applyColourExp {width : Nat} [NeZero width] (P : Nat → Bool)
    (exp : WordLangExpHOL (BitVec width)) (Q : Nat → Bool) (f : Nat → Nat) :
    everyVarExpHOL P exp = true ∧ (∀ x, P x = true → Q (f x) = true) →
      everyVarExpHOL Q (applyColourExp f exp) = true := by
  rintro ⟨valid, image⟩
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      everyVarExpHOL P e = true → everyVarExpHOL Q (applyColourExpCore f e) = true)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      everyVarExpsHOL P es = true →
        everyVarExpsHOL Q (es.map (applyColourExpCore f)) = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ exp valid
  · intro value; simp [everyVarExpHOL, applyColourExpCore]
  · intro name; simpa [everyVarExpHOL, applyColourExpCore] using image name
  · intro store; simp [everyVarExpHOL, applyColourExpCore]
  · intro address ih; simpa [everyVarExpHOL, applyColourExpCore] using ih
  · intro operator arguments ih; simpa [everyVarExpHOL, applyColourExpCore] using ih
  · intro operator left right ihLeft ihRight h
    simp only [applyColourExpCore, everyVarExpHOL, Bool.and_eq_true] at h ⊢
    exact ⟨ihLeft h.1, ihRight h.2⟩
  · simp [everyVarExpsHOL]
  · intro head tail ihHead ihTail h
    simp only [everyVarExpsHOL, List.map_cons, Bool.and_eq_true] at h ⊢
    exact ⟨ihHead h.1, ihTail h.2⟩

/-- Original key-enumeration transport on arbitrary Unit Spt trees. It requires
neither injectivity of f nor a canonical-tree assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_apply_nummap_key_helper"]
theorem everyApplyNummapKeyHelper (f : Nat → Nat) (names : Spt Unit)
    (P Q : Nat → Bool) :
    ((sptToAList names).map Prod.fst).all P = true ∧
      (∀ x, P x = true → Q (f x) = true) →
    ((sptToAList (sptFromAList ((sptToAList names).map
      (fun (x, _y) => (f x, ()))))).map Prod.fst).all Q = true := by
  rintro ⟨valid, image⟩
  change ((sptToAList (applyNummapKey f names)).map Prod.fst).all Q = true
  simp only [List.all_eq_true] at valid ⊢
  intro key member
  have domain := (sptMemMapFstToAList (applyNummapKey f names) key).mp member
  rw [applyNummapKeyDomain] at domain
  obtain ⟨source, sourceMember, rfl⟩ := domain
  exact image source (valid source ((sptMemMapFstToAList names source).mpr sourceMember))

/-- Flapjack pairing of the original key helper for the two source cut sets. -/
private theorem everyName_applyColour (P Q : Nat → Bool) (f : Nat → Nat)
    (names : WordLangCutsetsHOL) (valid : everyNameHOL P names = true)
    (image : ∀ x, P x = true → Q (f x) = true) :
    everyNameHOL Q (applyNummapsKey f names) = true := by
  simp only [everyNameHOL, Bool.and_eq_true] at valid ⊢
  exact ⟨everyApplyNummapKeyHelper f names.1 P Q ⟨valid.1, image⟩,
    everyApplyNummapKeyHelper f names.2 P Q ⟨valid.2, image⟩⟩

/-- Original full program occurrence transport, including all source fields and
return-dependent handlers. Arbitrary renaming may collapse names. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_apply_colour" (words_as_type_indexed_bitvec)]
theorem everyVar_applyColour {width : Nat} [NeZero width] (P : Nat → Bool)
    (prog : WordLangProgHOL (BitVec width)) (Q : Nat → Bool) (f : Nat → Nat) :
    everyVarHOL P prog = true ∧ (∀ x, P x = true → Q (f x) = true) →
      everyVarHOL Q (applyColour f prog) = true := by
  rintro ⟨valid, image⟩
  have listImage (values : List Nat) : values.all P = true → (values.map f).all Q = true := by
    simp only [List.all_eq_true, List.mem_map]
    rintro h _ ⟨x, member, rfl⟩
    exact image x (h x member)
  have nameImage (names : WordLangCutsetsHOL) := fun h => everyName_applyColour P Q f names h image
  have keyImage (names : Spt Unit) := fun h => everyApplyNummapKeyHelper f names P Q ⟨h, image⟩
  have instImage (i : WordLangInst (BitVec width)) := fun h => everyVarInst_applyColourInst P i Q f ⟨h, image⟩
  have expImage (e : WordLangExpHOL (BitVec width)) := fun h => everyVarExp_applyColourExp P e Q f ⟨h, image⟩
  have immImage (ri : WordRegImm (BitVec width)) :
      everyVarImmHOL P ri = true → everyVarImmHOL Q (applyColourImm f ri) = true := by
    cases ri <;> simp_all [everyVarImmHOL, applyColourImm]
  revert valid
  induction prog using everyVarHOL.induct
  case case2 priority moves =>
    have lengths : (moves.map (f ∘ Prod.fst)).length = (moves.map (f ∘ Prod.snd)).length := by simp
    simp only [applyColour, everyVarHOL, List.map_fst_zip (Nat.le_of_eq lengths),
      List.map_snd_zip (Nat.le_of_eq lengths.symm), Bool.and_eq_true]
    intro h
    exact ⟨by simpa only [List.map_map] using listImage (moves.map Prod.fst) h.1,
      by simpa only [List.map_map] using listImage (moves.map Prod.snd) h.2⟩
  case case13 returns target arguments handler ih =>
    cases returns with
    | none =>
      cases handler with
      | none => simpa [everyVarHOL, applyColour] using listImage arguments
      | some handler =>
        rcases handler with ⟨value, body, label, entry⟩
        simpa [everyVarHOL, applyColour] using listImage arguments
    | some returns =>
      rcases returns with ⟨values, names, body, label, entry⟩
      cases handler with
      | none =>
        simp_all [everyVarHOL, applyColour]
      | some handler =>
        rcases handler with ⟨value, body, label, entry⟩
        simp_all [everyVarHOL, applyColour]
  case case25 t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases t <;> simp_all [everyVarHOL, applyColour]
    all_goals exfalso
    all_goals rename_i impossible
    all_goals first
      | exact impossible _ _ _ _ rfl rfl rfl rfl
      | exact impossible _ _ _ _ _ rfl rfl rfl rfl rfl
  all_goals try simp_all [everyVarHOL, applyColour]
  all_goals aesop

/-- Original stack-field occurrence transport under arbitrary colouring. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_stack_var_apply_colour" (words_as_type_indexed_bitvec)]
theorem everyStackVar_applyColour {width : Nat} [NeZero width] (P : Nat → Bool)
    (prog : WordLangProgHOL (BitVec width)) (Q : Nat → Bool) (f : Nat → Nat) :
    everyStackVarHOL P prog = true ∧ (∀ x, P x = true → Q (f x) = true) →
      everyStackVarHOL Q (applyColour f prog) = true := by
  rintro ⟨valid, image⟩
  have nameImage (names : WordLangCutsetsHOL) := fun h => everyName_applyColour P Q f names h image
  revert valid
  induction prog using everyStackVarHOL.induct
  case case3 target arguments handler =>
    cases handler with
    | none => simp [everyStackVarHOL, applyColour]
    | some handler =>
      rcases handler with ⟨value, body, label, entry⟩
      simp [everyStackVarHOL, applyColour]
  case case4 target arguments handler values names body label entry ihBody ihHandler =>
    cases handler with
    | none => simp_all [everyStackVarHOL, applyColour]
    | some handler =>
      rcases handler with ⟨value, body, label, entry⟩
      simp_all [everyStackVarHOL, applyColour]
  case case10 t _ _ _ _ _ _ _ _ =>
    cases t <;> simp_all [everyStackVarHOL, applyColour]
    all_goals exfalso
    all_goals rename_i impossible
    all_goals first
      | exact impossible _ _ _ _ rfl rfl rfl rfl
      | exact impossible _ _ _ _ _ rfl rfl rfl rfl rfl
  all_goals try simp_all [everyStackVarHOL, applyColour]

/-- Original unconditional occurrence predicate with the constantly true
predicate, derived from the original full maximum bound as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_T" (words_as_type_indexed_bitvec)]
theorem everyVarTrue {width : Nat} [NeZero width] (prog : WordLangProgHOL (BitVec width)) :
    everyVarHOL (fun _ => true) prog = true := by
  exact everyVarMono (fun x => decide (x ≤ maxVarHOL prog)) prog (fun _ => true)
    ⟨fun _ _ => rfl, Flapjack.Compiler.Backend.WordAlloc.maxVarMax prog⟩

/-- Original unconditional physical-register occurrence result for total colouring.
No oracle acceptance or allocator success is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_is_phy_var_total_colour" (words_as_type_indexed_bitvec)]
theorem everyVar_isPhyVar_totalColour {width : Nat} [NeZero width]
    (col : Spt Nat) (prog : WordLangProgHOL (BitVec width)) :
    everyVarHOL isPhyVar (applyColour (totalColour col) prog) = true := by
  apply everyVar_applyColour (fun _ => true) prog isPhyVar (totalColour col)
  refine ⟨everyVarTrue prog, ?_⟩
  intro x _
  rw [totalColourAlt]
  simp [Function.comp_apply, isPhyVar]

end Flapjack.WordAlloc
