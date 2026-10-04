import Flapjack.RiscV.L3.Support
namespace Flapjack.RiscV.L3
/-- HOL `riscv$privilege` (`privilege_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "privilege_def"]
noncomputable def privilege (p : (BitVec 2)) : Privilege :=
  (((fun (v : (BitVec 2)) => (if ((v == (BitVec.ofNat 2 0))) then Privilege.User else ((if ((v == (BitVec.ofNat 2 1))) then Privilege.Supervisor else ((if ((v == (BitVec.ofNat 2 2))) then Privilege.Hypervisor else ((if ((v == (BitVec.ofNat 2 3))) then Privilege.Machine else (Flapjack.holArb Privilege)))))))))) p)

/-- HOL `riscv$MEM` (`MEM_def`), mechanically rendered from the elaborated HOL definition. -/
def MEM (a : (BitVec 61)) : (riscv_state → (BitVec 64)) :=
  (fun (state : riscv_state) => (let b : (BitVec 64) := ((BitVec.setWidth 64 a) <<< 3); (BitVec.setWidth 64 (((state.MEM8 ((b + (BitVec.ofNat 64 7))))) ++ ((BitVec.setWidth 56 (((state.MEM8 ((b + (BitVec.ofNat 64 6))))) ++ ((BitVec.setWidth 48 (((state.MEM8 ((b + (BitVec.ofNat 64 5))))) ++ ((BitVec.setWidth 40 (((state.MEM8 ((b + (BitVec.ofNat 64 4))))) ++ ((BitVec.setWidth 32 (((state.MEM8 ((b + (BitVec.ofNat 64 3))))) ++ ((BitVec.setWidth 24 (((state.MEM8 ((b + (BitVec.ofNat 64 2))))) ++ ((BitVec.setWidth 16 (((state.MEM8 ((b + (BitVec.ofNat 64 1))))) ++ (state.MEM8 b)))))))))))))))))))))))

/-- HOL `riscv$write'MEM` (`write'MEM_def`), mechanically rendered from the elaborated HOL definition. -/
def «write'MEM» (arg0 : ((BitVec 64) × (BitVec 61))) : (riscv_state → riscv_state) :=
  match arg0 with
  | (val, a) =>
  (fun (state : riscv_state) => (let b : (BitVec 64) := ((BitVec.setWidth 64 a) <<< 3); (let s : riscv_state := (let r := state; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 7))) (holWordExtract 8 63 56 val) state.MEM8)))) r.MEM8 }); (let s_1 : riscv_state := (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 6))) (holWordExtract 8 55 48 val) s.MEM8)))) r.MEM8 }); (let s : riscv_state := (let r := s_1; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 5))) (holWordExtract 8 47 40 val) s_1.MEM8)))) r.MEM8 }); (let s_1 : riscv_state := (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 4))) (holWordExtract 8 39 32 val) s.MEM8)))) r.MEM8 }); (let s : riscv_state := (let r := s_1; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 3))) (holWordExtract 8 31 24 val) s_1.MEM8)))) r.MEM8 }); (let s_1 : riscv_state := (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 2))) (holWordExtract 8 23 16 val) s.MEM8)))) r.MEM8 }); (let s : riscv_state := (let r := s_1; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate ((b + (BitVec.ofNat 64 1))) (holWordExtract 8 15 8 val) s_1.MEM8)))) r.MEM8 }); (let r := s; { r with MEM8 := ((fun (_eta1 : ((BitVec 64) → (BitVec 8))) => ((holUpdate b (holWordExtract 8 7 0 val) s.MEM8)))) r.MEM8 }))))))))))


end Flapjack.RiscV.L3
