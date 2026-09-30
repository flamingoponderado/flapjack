import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsDisjoint
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack.PanGlobalsInitGlobalsSimulation
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack-specific address algebra for the initializer cons proof's head
store and recursive free-range obligations (HOL source 2155-2229). This has no
independently named HOL original. Modular word arithmetic permits wrapping;
no numeric bound or evaluation premise is needed for range splitting. -/
theorem initializerAddressesSplit {width : Nat} (base : BitVec width)
    (head tail : Nat) (address : BitVec width) :
    addresses base (head + tail) address ↔
      addresses base head address ∨
        addresses (base + BitVec.ofNat width head *
          Flapjack.Compiler.Backend.StackRemove.bytesInWord width) tail address := by
  induction head generalizing base with
  | zero => simp [addresses]
  | succ head ih =>
      simp only [Nat.succ_add, addresses, ih]
      have hbase :
          base + Flapjack.Compiler.Backend.StackRemove.bytesInWord width +
              BitVec.ofNat width head *
                Flapjack.Compiler.Backend.StackRemove.bytesInWord width =
            base + BitVec.ofNat width (head + 1) *
              Flapjack.Compiler.Backend.StackRemove.bytesInWord width := by
        rw [BitVec.ofNat_add, BitVec.add_mul]
        simp only [BitVec.one_mul]
        ac_rfl
      rw [hbase]
      exact or_assoc.symm

/-- Prefix containment used to justify the first initializer's stores. -/
theorem initializerAddressesPrefix {width : Nat} (base : BitVec width)
    (head tail : Nat) (address : BitVec width)
    (h : addresses base head address) :
    addresses base (head + tail) address :=
  (initializerAddressesSplit base head tail address).mpr (Or.inl h)

/-- Suffix containment transports domain and disjointness premises to the
recursive initializer. This is infrastructure, not an extra simulation premise. -/
theorem initializerAddressesSuffix {width : Nat} (base : BitVec width)
    (head tail : Nat) (address : BitVec width)
    (h : addresses (base + BitVec.ofNat width head *
      Flapjack.Compiler.Backend.StackRemove.bytesInWord width) tail address) :
    addresses base (head + tail) address :=
  (initializerAddressesSplit base head tail address).mpr (Or.inr h)

/-- Canonical state roundtrips for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Flapjack assembly predicate for the complete original initializer lemma.
This is not a separately named HOL declaration: it packages all original
premises and conclusions so the recursive cases share one fixed target. -/
def initGlobalsGoal {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (decls : List (DeclHOL width))
    (ctxt : PanGlobalsContextExact width) : Prop :=
  ∀ (s' : PanSemStateFiniteExact width σ) (decls' : List (ProgHOL width))
    (funs exns : List (DeclHOL width)) (ctxt' : PanGlobalsContextExact width)
    (t : PanSemStateFiniteExact width σ) (freeAddrs : BitVec width → Prop),
    @evaluateDeclsHOLFinite width σ _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) decls = some s' ∧
    (∀ d ∈ decls, isDeclHOL d = true) ∧
    compileDecsExactHOL ctxt decls = (decls', funs, exns, ctxt') ∧
    panGlobalsStateRelHOLExact false ctxt s t ∧
    freeAddrs = addresses
      (t.topAddr - panBytesInWord width * BitVec.ofNat width
        ((decShapesHOL decls).map sizeOfShapeHOL).sum - ctxt.globalsSize)
      ((decShapesHOL decls).map sizeOfShapeHOL).sum ∧
    (∀ a, s.memaddrs a → ¬ freeAddrs a) ∧
    (∀ a, freeAddrs a → t.memaddrs a) ∧
    panGlobalsByteAlignedHOL ctxt.globalsSize ∧
    s.code = HolFiniteMapExact.empty ∧
    (∀ v sh addr, (s.globals.lookup v).isSome = true ∧
      ctxt.globals.lookup v = some (sh, addr) →
      ∀ a, addresses (t.topAddr - addr) (sizeOfShapeHOL sh) a → ¬ freeAddrs a) ∧
    (panBytesInWord width).toNat * ((decShapesHOL decls).map sizeOfShapeHOL).sum <
      2 ^ width →
    ∃ t', evaluateHOLFiniteState t (nestedSeqHOL decls') = (none, t') ∧
      panGlobalsStateRelHOLExact false ctxt' s' t' ∧
      t'.clock = t.clock ∧ t'.ffi = t.ffi ∧ t'.locals = t.locals ∧
      panGlobalsByteAlignedHOL ctxt'.globalsSize

/-- Original empty declaration case of the initializer lemma. All original
premises are retained in initGlobalsGoal; recursive allocation is still open. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_init_globals_lemma"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem initGlobalsNil {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (ctxt : PanGlobalsContextExact width) :
    initGlobalsGoal s [] ctxt := by
  classical
  intro s' decls' funs exns ctxt' t freeAddrs
    ⟨heval, _, hcompile, hrel, _, _, _, halign, _, _, _⟩
  simp only [evaluateDeclsHOLFinite, Option.some.injEq] at heval
  subst s'
  simp only [compileDecsExactHOL, Prod.mk.injEq] at hcompile
  rcases hcompile with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨t, ?_, hrel, rfl, rfl, rfl, halign⟩
  simp [nestedSeqHOL]

end Flapjack.PanGlobalsInitGlobalsSimulation
