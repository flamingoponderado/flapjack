import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanLang.Decl

/-!
Byte-range preservation facts for the executable `pan_simp` transform.
These are Flapjack-specific representation invariants, not HOL correctness
theorems: the rewrites reassociate sequences and move existing names and
expressions without changing their character data.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

theorem smartSeq_byteRanged {width : Nat} (pre program : Prog (BitVec width))
    (hpre : ProgByteRanged pre) (hprogram : ProgByteRanged program) :
    ProgByteRanged (smartSeq pre program) := by
  fun_cases smartSeq pre program with
  | case1 => exact hprogram
  | case2 => exact ⟨hpre, hprogram⟩

theorem seqCallRet_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (seqCallRet program) := by
  unfold seqCallRet
  split
  · split
    · exact ⟨h.1.1, h.1.2.1, trivial⟩
    · exact h
  · exact h

theorem seqAssoc_byteRanged {width : Nat} (pre program : Prog (BitVec width))
    (hpre : ProgByteRanged pre) (hprogram : ProgByteRanged program) :
    ProgByteRanged (seqAssoc pre program) := by
  fun_induction ProgByteRanged program generalizing pre with
  | case13 info _ _ _ =>
      rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨eid, handlerVar, handler⟩⟩ <;>
        grind only [seqAssoc, smartSeq_byteRanged, ProgByteRanged]
  | _ => grind only [seqAssoc, smartSeq_byteRanged, ProgByteRanged]

theorem retToTail_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (retToTail program) := by
  fun_induction ProgByteRanged program with
  | case13 info _ _ _ =>
      rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨eid, handlerVar, handler⟩⟩ <;>
        grind only [retToTail, seqCallRet_byteRanged, ProgByteRanged]
  | _ => grind only [retToTail, seqCallRet_byteRanged, ProgByteRanged]

theorem panSimpProg_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (panSimpProg program) := by
  unfold panSimpProg
  exact retToTail_byteRanged _ (seqAssoc_byteRanged .skip program trivial h)

theorem panSimpDecl_byteRanged {width : Nat} (declaration : Decl (BitVec width))
    (h : DeclByteRanged declaration) : DeclByteRanged (panSimpDecl declaration) := by
  cases declaration with
  | function d =>
      simp only [panSimpDecl]
      simp only [DeclByteRanged, FunDeclByteRanged] at h ⊢
      exact ⟨h.1, h.2.1, panSimpProg_byteRanged d.body h.2.2.1, h.2.2.2⟩
  | _ => simpa [panSimpDecl] using h

theorem panSimpDecls_byteRanged {width : Nat} (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panSimpDecls declarations, DeclByteRanged d := by
  intro d hd
  rw [panSimpDecls_eq_map] at hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  exact panSimpDecl_byteRanged e (h e he)

end Flapjack
