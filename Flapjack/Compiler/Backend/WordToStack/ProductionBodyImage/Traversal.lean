import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.Instructions
import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.MoveHelpers
import Flapjack.Compiler.Backend.WordToStack.NativeCompile

/-! Native `compNative` body output in the actual production decoder image.
Flapjack codec infrastructure (no HOL original): the production StackLang
decoder rejects only instruction payloads without a production counterpart, so
the whole body lies in its image when every emitted instruction does. The
source-side domain is the one actual callers already hold: the native input
decodes through `wordLangProgFromHOL` and the decoded program satisfies the
runtime `allocatorMemorySupported` guard. No output codec, desired body or
target run is assumed. -/
namespace Flapjack.ProductionBodyImage
open Compiler.Backend
open Compiler.Backend.WordToStack.Native Compiler.Backend.StackLang
open Compiler.Encoders.Asm RiscV

/-- Decode a concrete StackLang leaf or instruction-only fragment. -/
macro "output_image_leaf" : tactic => `(tactic|
  simp [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction,
    HolInst.toWordLangInst, HolArith.toWordLangArith, HolRegImm.toWordRegImm,
    HolAddr.toWordLangAddr, wordLangInstFromHOL, wordLangArithFromHOL, listSeq] <;>
  (repeat' split) <;> simp)

theorem iteImage {width : Nat} [NeZero width] (operator : HolCmp) (register : Nat)
    (right : HolRegImm width) (first second : HolProg width)
    (left : OutputImage first) (rightImage : OutputImage second) :
    OutputImage (.ite operator register right first second) := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := rightImage
  refine ⟨.ite operator register (HolRegImm.toWordRegImm right) a b, ?_⟩
  simp only [holProgToProduction, holProgToProgW, Prog.map, progToProduction] at ha hb ⊢
  rw [ha, hb]
  rfl

theorem loopImage {width : Nat} [NeZero width] (body : HolProg width)
    (image : OutputImage body) : OutputImage (.loop body) := by
  obtain ⟨a, ha⟩ := image
  refine ⟨.loop a, ?_⟩
  simp only [holProgToProduction, holProgToProgW, Prog.map, progToProduction] at ha ⊢
  rw [ha]
  rfl

/-- A call whose optional return and handler continuations decode. -/
theorem callImage {width : Nat} [NeZero width]
    (returns : Option (HolProg width × Nat × Nat × Nat)) (target : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (returnsImage : ∀ body link l1 l2, returns = some (body, link, l1, l2) → OutputImage body)
    (handlerImage : ∀ body l1 l2, handler = some (body, l1, l2) → OutputImage body) :
    OutputImage (.call returns target handler) := by
  rcases returns with _ | ⟨body, link, l1, l2⟩ <;>
    rcases handler with _ | ⟨hbody, h1, h2⟩
  · output_image_leaf
  · obtain ⟨b, hb⟩ := handlerImage hbody h1 h2 rfl
    simp only [holProgToProduction, holProgToProgW] at hb
    simp [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction, hb]
  · obtain ⟨a, ha⟩ := returnsImage body link l1 l2 rfl
    simp only [holProgToProduction, holProgToProgW] at ha
    simp [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction, ha]
  · obtain ⟨a, ha⟩ := returnsImage body link l1 l2 rfl
    obtain ⟨b, hb⟩ := handlerImage hbody h1 h2 rfl
    simp only [holProgToProduction, holProgToProgW] at ha hb
    simp [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction, ha, hb]

theorem seqStackFreeImage {width : Nat} [NeZero width] (n : Nat) (body : HolProg width)
    (image : OutputImage body) : OutputImage (seqStackFreeNative n body) := by
  unfold seqStackFreeNative
  split
  · exact image
  · exact sequenceImage _ _ (by output_image_leaf) image

theorem copyRetAuxImage {width : Nat} [NeZero width] (k f n : Nat) :
    OutputImage (copyRetAuxNative (width := width) k f n) := by
  induction n with
  | zero => unfold copyRetAuxNative; output_image_leaf
  | succ n ih =>
    unfold copyRetAuxNative
    simp only [listSeq]
    exact sequenceImage _ _ (stackLoadImage _ _) (sequenceImage _ _ (stackStoreImage _ _) ih)

theorem copyRetImage {width : Nat} [NeZero width] {β γ : Type} (perf isHandle : Bool)
    (kf : Nat × Nat × γ) (values : List β) (body : HolProg width)
    (image : OutputImage body) : OutputImage (copyRetNative perf isHandle kf values body) := by
  unfold copyRetNative
  dsimp only
  split
  · exact image
  · exact sequenceImage _ _ (copyRetAuxImage _ _ _) (seqStackFreeImage _ _ image)

theorem stackMoveImage {width : Nat} [NeZero width] (n start offset register : Nat)
    (body : HolProg width) (image : OutputImage body) :
    OutputImage (stackMoveNative n start offset register body) := by
  induction n generalizing start with
  | zero => exact image
  | succ n ih =>
    unfold stackMoveNative
    exact sequenceImage _ _ (ih _)
      (sequenceImage _ _ (stackLoadImage _ _) (stackStoreImage _ _))

theorem stackArgsImage {width : Nat} [NeZero width] {α β : Type} (dest : Sum α β)
    (argCount : Nat) (kf : Nat × Nat × Nat) :
    OutputImage (stackArgsNative (width := width) dest argCount kf) :=
  stackMoveImage _ _ _ _ _ (by output_image_leaf)

theorem stackHandlerArgsImage {width : Nat} [NeZero width] {α β : Type} (perf : Bool)
    (dest : Sum α β) (argCount : Nat) (kf : Nat × Nat × Nat) :
    OutputImage (stackHandlerArgsNative (width := width) perf dest argCount kf) :=
  stackArgsImage _ _ _

theorem callDestImage {width : Nat} [NeZero width] (pos : Option Nat) (args : List Nat)
    (kf : Nat × Nat × Nat) : OutputImage (callDestNative (width := width) pos args kf).1 := by
  unfold callDestNative
  cases pos with
  | some p => output_image_leaf
  | none =>
    simp only []
    split
    · output_image_leaf
    · exact stackLoadsImage _ _ (by output_image_leaf)

theorem liveImage {width : Nat} [NeZero width] (live : Spt Unit × Spt Unit)
    (bitmaps : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    OutputImage (wLiveNative live bitmaps kf).1 := by
  unfold wLiveNative
  split
  · output_image_leaf
  · exact sequenceImage _ _ (constantImage _ _) (stackStoreImage _ _)

theorem pushHandlerImage {width : Nat} [NeZero width] {β γ : Type} (perf : Bool)
    (l1 l2 : Nat) (kf : Nat × β × γ) :
    OutputImage (pushHandlerNative (width := width) perf l1 l2 kf) := by
  unfold pushHandlerNative
  cases perf <;> output_image_leaf

theorem popHandlerImage {width : Nat} [NeZero width] {β γ : Type} (perf : Bool)
    (kf : Nat × β × γ) (body : HolProg width) (image : OutputImage body) :
    OutputImage (popHandlerNative perf kf body) := by
  unfold popHandlerNative
  exact sequenceImage _ _ (stackLoadImage _ _)
    (sequenceImage _ _ (by output_image_leaf)
      (sequenceImage _ _ (by output_image_leaf) image))

theorem perfCallPrefixImage {width : Nat} [NeZero width] (l1 l2 k : Nat) :
    OutputImage (perfCallPrefixNative (width := width) l1 l2 k) := by
  unfold perfCallPrefixNative
  output_image_leaf

theorem perfCallSuffixImage {width : Nat} [NeZero width] :
    OutputImage (perfCallSuffixNative (width := width)) := by
  unfold perfCallSuffixNative
  output_image_leaf

theorem shareInstImage {width : Nat} [NeZero width] (op : HolMemop) (v : Nat)
    (address : HolAddr width) (kf : Nat × Nat × Nat) :
    OutputImage (wShareInstNative op v address kf) := by
  rcases address with ⟨ad, offset⟩
  cases op <;> unfold wShareInstNative <;> apply stackLoadsImage
  all_goals first
    | apply registerWriteImage
      intro register
      output_image_leaf
    | output_image_leaf

theorem perfPrefixIfImage {width : Nat} [NeZero width] (perf : Bool) (l1 l2 k : Nat) :
    OutputImage (if perf = true then perfCallPrefixNative (width := width) l1 l2 k
      else .skip) := by
  split
  · exact perfCallPrefixImage _ _ _
  · output_image_leaf

theorem perfSuffixIfImage {width : Nat} [NeZero width] (perf : Bool) :
    OutputImage (if perf = true then perfCallSuffixNative (width := width) else .skip) := by
  split
  · exact perfCallSuffixImage
  · output_image_leaf

/-- Full recursive native body image. The source domain is the actual caller's:
the native program decodes to `production` and that program satisfies the
runtime memory guard. `moveImage` is the move-helper image supplied by the
dedicated move leaf; it quantifies over all move lists and frames and assumes
no compiler output. -/
theorem compNativeImage {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool)
    (moveImage : ∀ (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat),
      OutputImage (wMoveNative (width := width) moves kf)) :
    (native : WordLangProgHOL (BitVec width)) → (production : WordProg (BitVec width)) →
    wordLangProgFromHOL native = some production →
    allocatorMemorySupported production = true →
    ∀ (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat),
      OutputImage (compNative conf perf native bs kf).1
  | .skip, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .move _ moves, _, _, _, bs, kf => by unfold compNative; exact moveImage moves kf
  | .inst instruction, production, decoded, supported, bs, kf => by
      unfold compNative
      simp only [wordLangProgFromHOL, Option.map_eq_some_iff] at decoded
      obtain ⟨inst, hinst, rfl⟩ := decoded
      exact instructionCompilerImage instruction inst hinst supported kf
  | .assign _ _, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .store _ _, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .get n name, _, _, _, bs, kf => by
      unfold compNative
      dsimp only
      exact registerWriteImage _ _ _ (fun _ => by output_image_leaf)
  | .set name exp, _, _, _, bs, kf => by
      unfold compNative
      cases name <;> cases exp <;> dsimp only <;>
        first
        | output_image_leaf
        | exact stackLoadsImage _ _ (by output_image_leaf)
  | .mustTerminate body, production, decoded, supported, bs, kf => by
      unfold compNative
      simp only [wordLangProgFromHOL, Option.map_eq_some_iff] at decoded
      obtain ⟨inner, hinner, rfl⟩ := decoded
      exact compNativeImage conf perf moveImage body inner hinner
        (by simpa [allocatorMemorySupported] using supported) bs kf
  | .seq first second, production, decoded, supported, bs, kf => by
      simp only [wordLangProgFromHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at decoded
      obtain ⟨a, ha, b, hb, rfl⟩ := decoded
      simp only [allocatorMemorySupported, Bool.and_eq_true] at supported
      unfold compNative
      rcases h1 : compNative conf perf first bs kf with ⟨q1, bs1⟩
      have i1 := compNativeImage conf perf moveImage first a ha supported.1 bs kf
      have i2 := compNativeImage conf perf moveImage second b hb supported.2 bs1 kf
      rw [h1] at i1
      exact sequenceImage _ _ i1 i2
  | .ite cmp r ri first second, production, decoded, supported, bs, kf => by
      simp only [wordLangProgFromHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at decoded
      obtain ⟨a, ha, b, hb, rfl⟩ := decoded
      simp only [allocatorMemorySupported, Bool.and_eq_true] at supported
      unfold compNative
      rcases h1 : compNative conf perf first bs kf with ⟨q1, bs1⟩
      have i1 := compNativeImage conf perf moveImage first a ha supported.1 bs kf
      have i2 := compNativeImage conf perf moveImage second b hb supported.2 bs1 kf
      rw [h1] at i1
      dsimp only
      cases ri with
      | reg n => exact stackLoadsImage _ _ (iteImage _ _ _ _ _ i1 i2)
      | imm i =>
        dsimp only
        split
        · exact stackLoadsImage _ _ (iteImage _ _ _ _ _ i1 i2)
        · exact sequenceImage _ _ (constantImage _ _)
            (stackLoadsImage _ _ (iteImage _ _ _ _ _ i1 i2))
  | .loop liveIn body liveOut, production, decoded, supported, bs, kf => by
      simp only [wordLangProgFromHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at decoded
      obtain ⟨inner, hinner, rfl⟩ := decoded
      unfold compNative
      rcases h : compNative conf perf body bs kf with ⟨q, bs1⟩
      have i := compNativeImage conf perf moveImage body inner hinner
        (by simpa [allocatorMemorySupported] using supported) bs kf
      rw [h] at i
      exact loopImage _ i
  | .call none dest args handler, _, _, _, bs, kf => by
      unfold compNative
      exact sequenceImage _ _ (callDestImage _ _ _)
        (seqStackFreeImage _ _ (by output_image_leaf))
  | .call (some (vs, live, retCode, l1, l2)) dest args none, production, decoded, supported,
      bs, kf => by
      unfold compNative
      simp only [wordLangProgFromHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at decoded
      obtain ⟨retProd, hret, _, rfl, hprod⟩ := decoded
      obtain ⟨_, rfl, rfl⟩ := hprod
      have sret : allocatorMemorySupported retProd = true := by
        simpa [allocatorMemorySupported] using supported
      rcases hd : callDestNative dest args kf with ⟨q0, target⟩
      have i0 := callDestImage (width := width) dest args kf
      rw [hd] at i0
      have i1 := liveImage live bs kf
      have i2 := compNativeImage conf perf moveImage retCode retProd hret sret
        (wLiveNative live bs kf).2 kf
      dsimp only
      refine sequenceImage _ _ i0 (sequenceImage _ _ i1
        (sequenceImage _ _ (stackArgsImage _ _ _)
          (sequenceImage _ _ (perfPrefixIfImage _ _ _ _)
            (callImage _ _ _ ?_ ?_))))
      · intro body link a b h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact sequenceImage _ _ (perfSuffixIfImage _) (copyRetImage _ _ _ _ _ i2)
      · intro body a b h
        cases h
  | .call (some (vs, live, retCode, l1, l2)) dest args (some (exn, handleCode, h1, h2)),
      production, decoded, supported, bs, kf => by
      unfold compNative
      simp only [wordLangProgFromHOL, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at decoded
      obtain ⟨retProd, hret, _, rfl, hprod⟩ := decoded
      obtain ⟨handleProd, hhandle, _, rfl, rfl⟩ := hprod
      simp only [allocatorMemorySupported, Bool.and_eq_true] at supported
      rcases hd : callDestNative dest args kf with ⟨q0, target⟩
      have i0 := callDestImage (width := width) dest args kf
      rw [hd] at i0
      have i1 := liveImage live bs kf
      have i2 := compNativeImage conf perf moveImage retCode retProd hret supported.1
        (wLiveNative live bs kf).2 kf
      have i4 := compNativeImage conf perf moveImage handleCode handleProd hhandle
        supported.2 (compNative conf perf retCode (wLiveNative live bs kf).2 kf).2 kf
      dsimp only
      refine sequenceImage _ _ i0 (sequenceImage _ _ i1
        (sequenceImage _ _ (pushHandlerImage _ _ _ _)
          (sequenceImage _ _ (stackHandlerArgsImage _ _ _ _)
            (sequenceImage _ _ (perfPrefixIfImage _ _ _ _)
              (callImage _ _ _ ?_ ?_)))))
      · intro body link a b h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact sequenceImage _ _ (perfSuffixIfImage _)
          (copyRetImage _ _ _ _ _ (popHandlerImage _ _ _ i2))
      · intro body a b h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact i4
  | .alloc _ live, _, _, _, bs, kf => by
      unfold compNative
      exact sequenceImage _ _ (liveImage _ _ _) (by output_image_leaf)
  | .storeConsts _ _ _ _ ws, _, _, _, bs, kf => by
      unfold compNative
      exact sequenceImage _ _ (constantImage _ _) (by output_image_leaf)
  | .raise _, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .return v vs, _, _, _, bs, kf => by
      unfold compNative
      exact stackLoadsImage _ _ (seqStackFreeImage _ _ (by output_image_leaf))
  | .break _, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .continue _, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .tick, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .opCurrHeap _ _ _, _, _, _, bs, kf => by
      unfold compNative
      exact stackLoadsImage _ _ (registerWriteImage _ _ _ (fun _ => by output_image_leaf))
  | .locValue _ _, _, _, _, bs, kf => by
      unfold compNative
      dsimp only
      exact registerWriteImage _ _ _ (fun _ => by output_image_leaf)
  | .install _ _ _ _ _, _, _, _, bs, kf => by
      unfold compNative
      exact stackLoadsImage _ _ (by output_image_leaf)
  | .codeBufferWrite _ _, _, _, _, bs, kf => by
      unfold compNative
      exact stackLoadsImage _ _ (by output_image_leaf)
  | .dataBufferWrite _ _, _, _, _, bs, kf => by
      unfold compNative
      exact stackLoadsImage _ _ (by output_image_leaf)
  | .ffi _ _ _ _ _ _, _, _, _, bs, kf => by unfold compNative; output_image_leaf
  | .shareInst op v exp, _, _, _, bs, kf => by
      unfold compNative
      split
      · output_image_leaf
      · exact shareInstImage _ _ _ _
termination_by native => sizeOf native

/-- The derived decoder result recovers the entire native body, including every
nested return/handler continuation. -/
theorem compNativeRoundtrip {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool)
    (moveImage : ∀ (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat),
      OutputImage (wMoveNative (width := width) moves kf))
    (native : WordLangProgHOL (BitVec width)) (production : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL native = some production)
    (supported : allocatorMemorySupported production = true)
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    ∃ body, holProgToProduction (compNative conf perf native bs kf).1 = some body ∧
      productionToHolProg body = some (compNative conf perf native bs kf).1 := by
  obtain ⟨body, image⟩ :=
    compNativeImage conf perf moveImage native production decoded supported bs kf
  exact ⟨body, image, productionToHolProg_of_holProgToProduction _ body image⟩

/-- Complete native body image on the actual source domain, with the move
helper discharged by `moveCompilerImage`: no callback or output premise. -/
theorem compNativeOutputImage {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (native : WordLangProgHOL (BitVec width))
    (production : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL native = some production)
    (supported : allocatorMemorySupported production = true)
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    OutputImage (compNative conf perf native bs kf).1 :=
  compNativeImage conf perf moveCompilerImage native production decoded supported bs kf

/-- Complete native body roundtrip on the actual source domain, with no callback. -/
theorem compNativeOutputRoundtrip {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (native : WordLangProgHOL (BitVec width))
    (production : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL native = some production)
    (supported : allocatorMemorySupported production = true)
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    ∃ body, holProgToProduction (compNative conf perf native bs kf).1 = some body ∧
      productionToHolProg body = some (compNative conf perf native bs kf).1 :=
  compNativeRoundtrip conf perf moveCompilerImage native production decoded supported bs kf

end Flapjack.ProductionBodyImage
