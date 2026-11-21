module

public import Flapjack.Compiler.Backend.WordElim.Proofs.StateRel
public import Flapjack.Compiler.Backend.WordElim.Proofs.Vars
public import Flapjack.Compiler.Backend.WordElim.Proofs.ConstWrites
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts

@[expose] public section

/-!
# `word_removal_lemma`: replacing the code of a leaf statement

Flapjack infrastructure for `word_removal_lemma`
(`word_elimProofScript.sml:931-1601`).  The removed state differs from the
original only in its code table (`wordStateRel_eq_withCode`).  Every statement
without a sub-program that is neither `LocValue` nor `Install` does not read the
code table, so its run on the removed state is its run on the original state with
the code replaced.  HOL obtains this per case by `fs[word_state_rel_def]`.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact

section Frame
variable {width : Nat} [NeZero width] {C F : Type}

/-- Statements without a sub-program that read neither the code table's domain
    nor the compiler state. Flapjack infrastructure. -/
def removalLeaf {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _
  | .install _ _ _ _ _ | .locValue _ _ => false
  | _ => true

/-- Replacing the code is a shared-memory frame. Flapjack infrastructure. -/
theorem withCode_shMemFrame (c : Spt (Nat × WordLangProgHOL (BitVec width))) :
    ShMemFrame (fun x : WordSemStateFiniteExact width C F => { x with code := c }) where
  locals _ := rfl
  shMdomain _ := rfl
  ffi _ := rfl
  setVar _ _ _ := rfl
  setFfi _ _ := rfl
  flushState b _ := by cases b <;> rfl

set_option linter.unusedSimpArgs false in
/-- A leaf statement run on the state with replaced code. Flapjack
    infrastructure. -/
theorem evaluate_withCode_leaf (c : Spt (Nat × WordLangProgHOL (BitVec width)))
    (s : WordSemStateFiniteExact width C F) (p : WordLangProgHOL (BitVec width))
    (hp : removalLeaf p = true) :
    evaluate p { s with code := c } =
      ((evaluate p s).1, { (evaluate p s).2 with code := c }) := by
  have hI := withCode_instFrame (C := C) (F := F) c
  have hA := withCode_allocFrame (C := C) (F := F) c
  have hS := withCode_shMemFrame (C := C) (F := F) c
  have gv : ∀ x (t : WordSemStateFiniteExact width C F), getVar x { t with code := c } = getVar x t :=
    fun _ _ => rfl
  have gvs : ∀ xs (t : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.getVars xs { t with code := c } =
        WordSemStateFiniteExact.getVars xs t :=
    fun xs t => (getVars_congr { t with code := c } t rfl xs).symm
  have wE : ∀ e (t : WordSemStateFiniteExact width C F),
      wordExp { t with code := c } e = wordExp t e :=
    fun e t => (wordExp_congr { t with code := c } t rfl rfl rfl rfl e).symm
  have hi := fun i (t : WordSemStateFiniteExact width C F) => (inst_frame hI i t).symm
  have ha := fun w n (t : WordSemStateFiniteExact width C F) => (alloc_frame hA w n t).symm
  have hsh := fun op v ad (t : WordSemStateFiniteExact width C F) =>
    (shareInst_frame (rw := width) hS op v ad t).symm
  have gst : ∀ x (t : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.getStore x { t with code := c } =
        WordSemStateFiniteExact.getStore x t := fun _ _ => rfl
  have hj := fun (t : WordSemStateFiniteExact width C F) => jumpExc_withCode t c
  cases p <;> simp only [removalLeaf, Bool.false_eq_true] at hp <;>
    rw [evaluate, evaluate] <;>
    (try simp only [gv, gvs, gst, wE, hi, ha, hsh, hI.memStore, hj]) <;>
    (repeat' split) <;>
    first
      | rfl
      | simp_all [flushState, setVar, setVars, setStore, unsetVar,
          decClock, getFpVar, Option.map_eq_none_iff, Option.map_eq_some_iff]

end Frame

end Flapjack.Compiler.Backend.WordElim
