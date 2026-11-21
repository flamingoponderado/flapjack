module

public import Flapjack.Pancake.Proofs.PanSimp
public import Mathlib.Data.List.Basic

@[expose] public section

/-! `pan_simpProofScript.sml:1064`: `pan_simp` rewrites only function bodies and
keeps every parameter list, so per-function parameter distinctness is preserved.

HOL states `EVERY (λ(name,params,body). ALL_DISTINCT params)` over `functions`
on both sides, i.e. Lean's `List.Forall` over the same tuple-pattern lambda with
`ALL_DISTINCT` as `List.Nodup`.  `List.Forall` is provided by
`Mathlib.Data.List.Basic`, so this declaration has its own module rather than
pulling Mathlib's linter defaults into `PanSimp.lean`. -/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact HOL `pan_simpProof$compile_prog_distinct_params`
(`pan_simpProofScript.sml:1064`): `pan_simp` rewrites only function bodies and
keeps every parameter list, so distinctness of each function's parameters is
preserved.  The typed capture `compile_prog_distinct_params_typed`
(`pancake_pan_simp_proof_typed_probe.out`) shows HOL's three-tuple pattern
lambda `λ(name,params,body). ALL_DISTINCT params` on both sides, with the body
paired with its shape; Lean keeps that lambda as
`fun (_name, params, _body) => params.Nodup` under `List.Forall`, and
`functions`/`compile_prog` as the reviewed `functionsHOL`/`panSimpDeclsHOL`. -/
@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "compile_prog_distinct_params"
  (words_as_type_indexed_bitvec)]
theorem compileProgDistinctParamsHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) :
    (Flapjack.Pancake.PanLang.functionsHOL declarations).Forall
        (fun (_name, params, _body) => params.Nodup) →
      (Flapjack.Pancake.PanLang.functionsHOL (panSimpDeclsHOL declarations)).Forall
        (fun (_name, params, _body) => params.Nodup) := by
  rw [functionsHOL_panSimpDeclsHOL_eq]
  induction declarations with
  | nil =>
    intro h
    simp [Flapjack.Pancake.PanLang.functionsHOL] at h ⊢
  | cons declaration declarations ih =>
    intro h
    cases declaration with
    | function entry =>
      simp only [Flapjack.Pancake.PanLang.functionsHOL, List.forall_cons,
        List.map_cons] at h ⊢
      exact ⟨by simpa using h.1, ih h.2⟩
    | decl shape name value =>
      simp only [Flapjack.Pancake.PanLang.functionsHOL] at h ⊢
      exact ih h
    | exnDecl exceptionName shape =>
      simp only [Flapjack.Pancake.PanLang.functionsHOL] at h ⊢
      exact ih h
    | name struct fields =>
      simp only [Flapjack.Pancake.PanLang.functionsHOL] at h ⊢
      exact ih h

end Flapjack
