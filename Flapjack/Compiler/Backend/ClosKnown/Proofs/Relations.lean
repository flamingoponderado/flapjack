module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxTotal
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.FreeVars

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Relations used in the known-function semantic simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations
open ClosSem ClosProps

/-- Two expressions are related when a safe known-function traversal of the
first produces the second within the requested approximation tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "exp_rel_def"]
def expRel (c : Config) (aenv : List ValApprox) (g' : Spt ValApprox)
    (e1 e2 : ClosLang.Exp) : Prop :=
  ∃ g0 g approx k, sptSubspt g g' ∧
    (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0 ∧
    knownListTotal { c with inlineFactor := k } [e1] aenv g0 = ([(e2, approx)], g)

/-- Changing the current inline factor leaves the existential expression
relation unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "exp_rel_upd_inline_factor"]
theorem expRelUpdateInlineFactor (c : Config) (k : Nat) :
    expRel { c with inlineFactor := k } = expRel c := by
  funext aenv g e1 e2
  simp [expRel]

/-- Decreasing the current inline factor leaves the expression relation
unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "exp_rel_dec_inline_factor"]
theorem expRelDecInlineFactor (c : Config) (aenv : List ValApprox) (g : Spt ValApprox)
    (e1 e2 : ClosLang.Exp) : expRel (decInlineFactor c) aenv g e1 e2 ↔ expRel c aenv g e1 e2 := by
  simp [decInlineFactor, expRelUpdateInlineFactor]

/-- Function bodies are related when their arities agree and their expressions
are related in the corresponding approximation environment. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "f_rel_def"]
def fRel (c : Config) (aenv : List ValApprox) (g : Spt ValApprox)
    (f1 f2 : Nat × ClosLang.Exp) : Prop :=
  f1.1 = f2.1 ∧ expRel c (List.replicate f1.1 .other ++ aenv) g f1.2 f2.2

/-- Function-body relation is independent of the current inline factor. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "f_rel_upd_inline_factor"]
theorem fRelUpdateInlineFactor (c : Config) (k : Nat) :
    fRel { c with inlineFactor := k } = fRel c := by
  funext aenv g f1 f2
  simp [fRel, expRelUpdateInlineFactor]

/-- Expression relation is monotone under extension of its approximation
tree. This is Flapjack proof infrastructure. -/
theorem expRelSubspt (c : Config) (aenv : List ValApprox) (g g' : Spt ValApprox)
    (e1 e2 : ClosLang.Exp) (rel : expRel c aenv g e1 e2) (sub : sptSubspt g g') :
    expRel c aenv g' e1 e2 := by
  obtain ⟨g0, intermediate, approx, k, inner, safeEnv, safeGlobals, run⟩ := rel
  refine ⟨g0, intermediate, approx, k, ?_, safeEnv, safeGlobals, run⟩
  intro n member
  obtain ⟨inG, eq1⟩ := inner n member
  obtain ⟨inG', eq2⟩ := sub n inG
  exact ⟨inG', eq2.trans eq1⟩

/-- The target application annotation is unchanged or valid for the runtime
closure and argument count. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "loptrel_def"]
def loptRel (fv : ClosSem.Value) (numargs : Nat) (lopt1 lopt2 : Option Nat) : Prop :=
  lopt2 = lopt1 ∨ lopt1 = none ∧
    match fv, lopt2 with
    | .closure (some loc1) args _ n _, some loc2 => loc1 = loc2 ∧ n = numargs ∧ args = []
    | .recclosure (some loc1) args _ fns i, some loc2 =>
      i < fns.length ∧ loc2 = loc1 + 2 * i ∧
        numargs = (@Flapjack.holEl (Nat × ClosLang.Exp) ⟨(0, .var .none 0)⟩ i fns).1 ∧ args = []
    | _, _ => False

/-- The current approximation tree is the compiler-oracle state at index zero. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "next_g_def"
  (fmap_as_finite_support := [refs, code])]
def nextG {C F : Type} (s : State (Spt ValApprox × C) F) : Spt ValApprox :=
  (s.compileOracle 0).1.1

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

end Flapjack.Compiler.Backend.ClosKnown.Relations
