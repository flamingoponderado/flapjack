import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL

/-! Executed pan_simp declaration pass. The wrapper calls the reviewed
`panSimpDeclsHOL` (HOL `pan_simp$compile_prog_def`) directly through the
production declaration codecs, as the executed PanStructs and pan_globals
stages already do; these production-carrier equalities have no HOL original. -/
namespace Flapjack
open Pancake.PanLang

/-- Execute the reviewed `panSimpDeclsHOL` through the production declaration
codecs. The parser-backed caller supplies the input range invariant used by the
equality below. This wrapper has no separate HOL declaration. -/
def panSimpDeclsRouted {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (_hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (Decl (BitVec width)) :=
  (panSimpDeclsHOL (declarations.map declToHOL)).map declOfHOL

/-- On byte-ranged input the routed pass computes exactly the production
`panSimpDecls` result, so the executed output is unchanged. -/
theorem panSimpDeclsRouted_eq {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    panSimpDeclsRouted declarations hd = panSimpDecls declarations := by
  have hround : (declarations.map declToHOL).map (fun d => declOfHOL d) = declarations := by
    induction declarations with
    | nil => rfl
    | cons d ds ih =>
        simp only [List.map_cons]
        rw [declOfHOL_declToHOL d (hd d (by simp)),
          ih (fun e he => hd e (by simp [he]))]
  unfold panSimpDeclsRouted
  rw [progOfHOL_panSimpDeclsHOL, hround]

end Flapjack
