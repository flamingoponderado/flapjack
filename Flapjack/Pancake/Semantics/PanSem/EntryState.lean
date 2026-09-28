import Flapjack.Pancake.Semantics.PanSem.TotalEvalAgree

/-!
# Production PanSem entry state from evaluated declarations

HOL `semantics_decls_def` (`cakeml/pancake/semantics/panSemScript.sml:861-869`)
runs `evaluate_decls (s with structs := st_ctxt) decls` and then
`semantics s' start`.  HOL `evaluate_decls_def` (`:814-837`) writes only
`globals` (`Decl`), `code` (`Function`) and `eshapes` (`ExnDecl`), leaving every
other field of `s` unchanged.

Production `evaluateDecls` works on `PanSemDeclarationState`, whose `runtime`
holds the expression-evaluation fields and whose `code`/`eshapes` are
`InfoMap`s.  This module defines the canonical production entry state
`panSemEntryStateOfDecls` fed to the total evaluator, and proves the production
frame: `evaluateDecls` changes only `runtime.globals`, `code` and `eshapes`,
matching HOL.  The memory-domain fields `memaddrs`/`sharedMemaddrs` and the
byte order `be` are not carried by the declaration state; they come from the
machine state.  Untagged Flapjack-specific bridge infrastructure
(`flapjack-pxn.18.4.3.77.2.17.1`).
-/

namespace Flapjack

/-- The production PanSem entry state after declaration evaluation: structure
    context, globals, locals, memory, FFI, clock and base/top addresses from the
    evaluated declaration state's runtime, `code` from its function entries (the
    HOL code value `(params, body, return)`), `exceptionShapes` by lookup in its
    exception-shape map, and the memory domains and byte order from `machine`. -/
def panSemEntryStateOfDecls [BEq String] {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (decl : PanSemDeclarationState (RiscV.Word 64) σ) :
    PanSemState (RiscV.Word 64) (FfiState σ) where
  locals := decl.runtime.locals
  globals := decl.runtime.globals
  structs := decl.runtime.structs
  code := decl.code.map fun entry =>
    (entry.1, (entry.2.params, entry.2.body, entry.2.returnShape))
  exceptionShapes := fun exception => lookupInfo exception decl.eshapes
  memory := decl.runtime.memory
  memaddrs := machine.memaddrs
  sharedMemaddrs := machine.sharedMemaddrs
  clock := decl.runtime.clock
  be := machine.be
  ffi := decl.runtime.ffi
  baseAddress := decl.runtime.baseAddress
  topAddress := decl.runtime.topAddress

/-- **Production `evaluate_decls` frame.**  A successful production
    `evaluateDecls` changes only `runtime.globals`, `code` and `eshapes`; the rest
    of the runtime (structure context, locals, memory, FFI, clock, addresses,
    byte width and memory hooks) and the memory access are unchanged, as in HOL
    `evaluate_decls_def`. -/
theorem evaluateDecls_frame [BEq String] {σ : Type} :
    ∀ (declarations : List (Decl (RiscV.Word 64)))
      (state out : PanSemDeclarationState (RiscV.Word 64) σ),
      evaluateDecls state declarations = some out →
      out.runtime = { state.runtime with globals := out.runtime.globals } ∧
        out.memoryAccess = state.memoryAccess := by
  intro declarations
  induction declarations with
  | nil =>
      intro state out h
      simp only [evaluateDecls, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | cons declaration declarations ih =>
      intro state out h
      cases declaration with
      | name _ _ =>
          simp only [evaluateDecls] at h
          exact ih state out h
      | decl shape name expression =>
          simp only [evaluateDecls] at h
          split at h
          · cases h
          · split at h
            · obtain ⟨hr, hm⟩ := ih _ out h
              exact ⟨by rw [hr], hm⟩
            · cases h
      | function fd =>
          simp only [evaluateDecls] at h
          split at h
          · obtain ⟨hr, hm⟩ := ih _ out h
            exact ⟨hr, hm⟩
          · cases h
      | exnDecl exception shape =>
          simp only [evaluateDecls] at h
          split at h
          · cases h
          · split at h
            · obtain ⟨hr, hm⟩ := ih _ out h
              exact ⟨hr, hm⟩
            · cases h

/-- The fields of the entry state that `evaluate_decls` does not write are those
    of the initial declaration state's runtime. -/
theorem panSemEntryStateOfDecls_frame [BEq String] {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (declarations : List (Decl (RiscV.Word 64)))
    (state out : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state declarations = some out) :
    (panSemEntryStateOfDecls machine out).structs = state.runtime.structs ∧
      (panSemEntryStateOfDecls machine out).locals = state.runtime.locals ∧
      (panSemEntryStateOfDecls machine out).memory = state.runtime.memory ∧
      (panSemEntryStateOfDecls machine out).ffi = state.runtime.ffi ∧
      (panSemEntryStateOfDecls machine out).clock = state.runtime.clock ∧
      (panSemEntryStateOfDecls machine out).baseAddress = state.runtime.baseAddress ∧
      (panSemEntryStateOfDecls machine out).topAddress = state.runtime.topAddress := by
  obtain ⟨hr, _⟩ := evaluateDecls_frame declarations state out h
  simp only [panSemEntryStateOfDecls]
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Flapjack
