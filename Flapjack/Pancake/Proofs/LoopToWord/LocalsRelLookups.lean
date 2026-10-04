import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.HolRef

/-!
# Exact lookup consequences of the Loop-to-Word locals relation

Ports `locals_rel_get_var` and `locals_rel_get_vars` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:252-269`.  The theorem
statements retain HOL's conjunctive premises, quantified argument/result lists,
and exact `loopSem`/`wordSem` evaluators. The `get_var` case takes the source
locals map directly, while the `get_vars` case retains both full states. The
finite-map relation qualifiers record canonical carriers named in each theorem
signature; they do not change the theorem statements.
-/

namespace Flapjack.LoopToWord

/-- Local canonical roundtrip witness for the LoopSem state's `globals`
finite-map qualifier on the lookup ports in this module. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
      (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
      LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Local canonical roundtrip witness for the WordSem state's `fpRegs` and
`store` finite-map qualifiers on the lookup ports in this module. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Exact HOL `locals_rel_get_var` (`loop_to_wordProofScript.sml:252-257`).
The source locals argument is the exact Spt map (HOL `num_map`); the target is
the full WordSem state, as in HOL's `t.locals` input/result. The premise
conjunction and result are those of HOL verbatim, using exact Spt `lookup`,
`find_var`, and state-carried `wordSem$get_var` ports. The target state's
finite-map translation and word-width translation are spelled out by the tag. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem localsRelHOLGetVar {width : Nat} [NeZero width] {C F : Type}
    (context : Spt Nat) (sourceLocals : Spt (WordLocW width))
    (target : WordSemStateFiniteExact width C F) (name : Nat)
    (value : WordLocW width)
    (hpremises : localsRelHOL context sourceLocals target.locals ∧
      sptLookup name sourceLocals = some value) :
    WordSemStateFiniteExact.getVar (width := width)
      (findVarHOL context name) target = some value := by
  obtain ⟨_, _, hsim⟩ := hpremises.1
  obtain ⟨register, hcontext, htarget⟩ := hsim name value hpremises.2
  have hfind : findVarHOL context name = register := by
    simp [findVarHOL, hcontext]
  rw [hfind]
  simpa [WordSemStateFiniteExact.getVar] using htarget

/-- Exact HOL `locals_rel_get_vars` (`loop_to_wordProofScript.sml:259-269`).
This retains HOL's universal quantification over `argvars` and `argvals`, its
conjunctive relation/evaluation premise, its mapped argument list, and the
length conclusion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem localsRelHOLGetVars {width : Nat} [NeZero width] {C F : Type}
    (context : Spt Nat) (source : LoopSemStateFiniteExact width F)
    (target : WordSemStateFiniteExact width C F) :
    ∀ argvars argvals,
      (localsRelHOL context source.locals target.locals ∧
        LoopSemStateFiniteExact.getVars argvars source = some argvals) →
      WordSemStateFiniteExact.getVars (argvars.map (findVarHOL context)) target =
        some argvals ∧ argvals.length = argvars.length := by
  intro argvars
  induction argvars with
  | nil =>
      intro argvals hpremises
      rcases hpremises with ⟨_, hsource⟩
      simp [LoopSemStateFiniteExact.getVars] at hsource
      subst argvals
      simp [WordSemStateFiniteExact.getVars]
  | cons name names ih =>
      intro argvals hpremises
      rcases hpremises with ⟨hrel, hsource⟩
      cases hfirst : sptLookup name source.locals with
      | none =>
          simp [LoopSemStateFiniteExact.getVars, hfirst] at hsource
      | some value =>
          cases htail : LoopSemStateFiniteExact.getVars names source with
          | none =>
              simp [LoopSemStateFiniteExact.getVars, hfirst, htail] at hsource
          | some values =>
              simp [LoopSemStateFiniteExact.getVars, hfirst, htail] at hsource
              subst argvals
              have hhead := localsRelHOLGetVar context source.locals target name value
                ⟨hrel, hfirst⟩
              have hrest := ih values ⟨hrel, htail⟩
              constructor
              · change (match WordSemStateFiniteExact.getVar
                    (findVarHOL context name) target with
                  | none => none
                  | some head =>
                    match WordSemStateFiniteExact.getVars
                        (names.map (findVarHOL context)) target with
                    | none => none
                    | some tail => some (head :: tail)) =
                  some (value :: values)
                rw [hhead, hrest.1]
              · simp [hrest.2]

end Flapjack.LoopToWord
