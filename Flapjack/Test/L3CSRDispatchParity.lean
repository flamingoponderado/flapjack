import Flapjack.RiscV.L3.Defs.CSRDispatch

set_option maxRecDepth 10000
namespace Flapjack.Test.L3CSRDispatchParity
open Flapjack.RiscV.L3

/-- Each literal known-CSR read preserves the entire arbitrary machine state.
These are Flapjack regression guards, not separate HOL theorem ports. -/
example (s : riscv_state) : (CSRMap 1 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3072 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3073 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3074 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3200 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3201 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3202 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 256 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 257 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 260 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 289 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3329 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3457 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 320 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 321 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3394 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3395 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 324 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 384 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 385 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2304 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2305 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2306 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2432 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2433 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2434 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 512 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 513 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 514 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 545 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3585 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3713 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 576 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 577 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 578 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 579 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2561 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2689 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3840 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3841 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 3856 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 768 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 769 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 770 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 772 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 801 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1793 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1857 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 832 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 833 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 834 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 835 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 836 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 896 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 897 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 898 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 899 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 900 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 901 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2817 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 2945 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1920 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1921 s).2 = s := by rfl
example (s : riscv_state) : (CSRMap 1923 s).2 = s := by rfl

-- Complete arbitrary-state equations for all literal direct-field writes.
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,257) s =
  {s with c_SCSR := holUpdate s.procID {s.c_SCSR s.procID with stvec := v} s.c_SCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,320) s =
  {s with c_SCSR := holUpdate s.procID {s.c_SCSR s.procID with sscratch := v} s.c_SCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,384) s =
  {s with c_SCSR := holUpdate s.procID {s.c_SCSR s.procID with sptbr := v} s.c_SCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,385) s =
  {s with c_SCSR := holUpdate s.procID {s.c_SCSR s.procID with sasid := v} s.c_SCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,769) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mtvec := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,832) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mscratch := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,835) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mbadaddr := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,896) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mbase := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,897) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mbound := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,898) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mibase := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,899) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mibound := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,900) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mdbase := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,901) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mdbound := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,1920) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mtohost := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,1921) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mfromhost := v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (257,v) {s with procID := 7} =
  {{s with procID := 7, c_SCSR := holUpdate 7 {s.c_SCSR 7 with stvec := v} s.c_SCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 257, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 257} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (320,v) {s with procID := 7} =
  {{s with procID := 7, c_SCSR := holUpdate 7 {s.c_SCSR 7 with sscratch := v} s.c_SCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 320, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 320} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (384,v) {s with procID := 7} =
  {{s with procID := 7, c_SCSR := holUpdate 7 {s.c_SCSR 7 with sptbr := v} s.c_SCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 384, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 384} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (385,v) {s with procID := 7} =
  {{s with procID := 7, c_SCSR := holUpdate 7 {s.c_SCSR 7 with sasid := v} s.c_SCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 385, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 385} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (769,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mtvec := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 769, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 769} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (832,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mscratch := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 832, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 832} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (835,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mbadaddr := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 835, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 835} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (896,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mbase := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 896, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 896} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (897,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mbound := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 897, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 897} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (898,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mibase := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 898, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 898} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (899,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mibound := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 899, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 899} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (900,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mdbase := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 900, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 900} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (901,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mdbound := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 901, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 901} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (1920,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mtohost := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 1920, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 1920} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : writeCSR (1921,v) {s with procID := 7} =
  {{s with procID := 7, c_MCSR := holUpdate 7 {s.c_MCSR 7 with mfromhost := v} s.c_MCSR} with c_update := holUpdate 7 {s.c_update 7 with addr := some 1921, data2 := some v} (holUpdate 7 {s.c_update 7 with addr := some 1921} s.c_update)} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,321) s =
  {s with c_SCSR := holUpdate s.procID {s.c_SCSR s.procID with sepc := v &&& BitVec.signExtend 64 (4 : BitVec 3)} s.c_SCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,833) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mepc := v &&& BitVec.signExtend 64 (4 : BitVec 3)} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,770) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mtdeleg := «rec'mtdeleg» v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,772) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mie := «rec'mie» v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,834) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mcause := «rec'mcause» v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,836) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mip := «rec'mip» v} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,289) s =
  (let t := {s with c_SCSR := holUpdate s.procID {s.c_SCSR s.procID with stimecmp := v} s.c_SCSR}; {t with c_MCSR := holUpdate t.procID {t.c_MCSR t.procID with mip := { (t.c_MCSR t.procID).mip with STIP := false}} t.c_MCSR}) := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,801) s =
  (let t := {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mtimecmp := v} s.c_MCSR}; {t with c_MCSR := holUpdate t.procID {t.c_MCSR t.procID with mip := { (t.c_MCSR t.procID).mip with MTIP := false}} t.c_MCSR}) := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,256) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mstatus := lower_sstatus_mstatus («rec'sstatus» v, (s.c_MCSR s.procID).mstatus)} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,260) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mie := lower_sie_mie («rec'sie» v, (s.c_MCSR s.procID).mie)} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,324) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mip := lower_sip_mip («rec'sip» v, (s.c_MCSR s.procID).mip)} s.c_MCSR} := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,768) s =
  {s with c_MCSR := holUpdate s.procID {s.c_MCSR s.procID with mstatus := update_mstatus ((s.c_MCSR s.procID).mstatus, «rec'mstatus» v)} s.c_MCSR} := by rfl
example (s : riscv_state) (core : BitVec 64) : sendIPI core s =
 (let id := BitVec.setWidth 8 core;
  if decide (id.toNat < s.totalCore) then
   {s with c_MCSR := holUpdate id {s.c_MCSR id with mip := {(s.c_MCSR id).mip with MSIP := true}} s.c_MCSR}
  else s) := by rfl
example (s : riscv_state) (core : BitVec 64) : «write'CSRMap» (core,1923) s = sendIPI core s := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,1) s =
 (let t := {s with c_UCSR := holUpdate s.procID {s.c_UCSR s.procID with fpcsr := «write'reg'FPCSR» ((s.c_UCSR s.procID).fpcsr, holBitFieldInsert 4 0 (holWordExtract 5 4 0 v) («reg'FPCSR» (s.c_UCSR s.procID).fpcsr))} s.c_UCSR}; let u := {t with c_MCSR := holUpdate t.procID {t.c_MCSR t.procID with mstatus := {(t.c_MCSR t.procID).mstatus with MFS := ext_status ExtStatus.Dirty}} t.c_MCSR}; {u with c_MCSR := holUpdate u.procID {u.c_MCSR u.procID with mstatus := {(u.c_MCSR u.procID).mstatus with MSD := true}} u.c_MCSR}) := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,2) s =
 (let t := {s with c_UCSR := holUpdate s.procID {s.c_UCSR s.procID with fpcsr := {(s.c_UCSR s.procID).fpcsr with FRM := holWordExtract 3 2 0 v}} s.c_UCSR}; let u := {t with c_MCSR := holUpdate t.procID {t.c_MCSR t.procID with mstatus := {(t.c_MCSR t.procID).mstatus with MFS := ext_status ExtStatus.Dirty}} t.c_MCSR}; {u with c_MCSR := holUpdate u.procID {u.c_MCSR u.procID with mstatus := {(u.c_MCSR u.procID).mstatus with MSD := true}} u.c_MCSR}) := by rfl
example (s : riscv_state) (v : BitVec 64) : «write'CSRMap» (v,3) s =
 (let t := {s with c_UCSR := holUpdate s.procID {s.c_UCSR s.procID with fpcsr := «write'reg'FPCSR» ((s.c_UCSR s.procID).fpcsr, holWordExtract 32 31 0 v)} s.c_UCSR}; let u := {t with c_MCSR := holUpdate t.procID {t.c_MCSR t.procID with mstatus := {(t.c_MCSR t.procID).mstatus with MFS := ext_status ExtStatus.Dirty}} t.c_MCSR}; {u with c_MCSR := holUpdate u.procID {u.c_MCSR u.procID with mstatus := {(u.c_MCSR u.procID).mstatus with MSD := true}} u.c_MCSR}) := by rfl
example (s : riscv_state) : CSRMap 1 s = (BitVec.setWidth 64 (holWordExtract 5 4 0 («reg'FPCSR» (s.c_UCSR s.procID).fpcsr)),s) := by rfl
example (s : riscv_state) : CSRMap 2 s = (BitVec.setWidth 64 (s.c_UCSR s.procID).fpcsr.FRM,s) := by rfl
example (s : riscv_state) : CSRMap 3 s = (BitVec.setWidth 64 (holWordExtract 8 7 0 («reg'FPCSR» (s.c_UCSR s.procID).fpcsr)),s) := by rfl
example (s : riscv_state) : CSRMap 256 s = («reg'sstatus» (lift_mstatus_sstatus (s.c_MCSR s.procID).mstatus),s) := by rfl
example (s : riscv_state) : CSRMap 257 s = ((s.c_SCSR s.procID).stvec,s) := by rfl
example (s : riscv_state) : CSRMap 260 s = («reg'sie» (lift_mie_sie (s.c_MCSR s.procID).mie),s) := by rfl
example (s : riscv_state) : CSRMap 289 s = ((s.c_SCSR s.procID).stimecmp,s) := by rfl
example (s : riscv_state) : CSRMap 320 s = ((s.c_SCSR s.procID).sscratch,s) := by rfl
example (s : riscv_state) : CSRMap 321 s = ((s.c_SCSR s.procID).sepc,s) := by rfl
example (s : riscv_state) : CSRMap 324 s = («reg'sip» (lift_mip_sip (s.c_MCSR s.procID).mip),s) := by rfl
example (s : riscv_state) : CSRMap 384 s = ((s.c_SCSR s.procID).sptbr,s) := by rfl
example (s : riscv_state) : CSRMap 385 s = ((s.c_SCSR s.procID).sasid,s) := by rfl
example (s : riscv_state) : CSRMap 512 s = («reg'mstatus» (s.c_HCSR s.procID).hstatus,s) := by rfl
example (s : riscv_state) : CSRMap 513 s = ((s.c_HCSR s.procID).htvec,s) := by rfl
example (s : riscv_state) : CSRMap 514 s = («reg'mtdeleg» (s.c_HCSR s.procID).htdeleg,s) := by rfl
example (s : riscv_state) : CSRMap 545 s = ((s.c_HCSR s.procID).htimecmp,s) := by rfl
example (s : riscv_state) : CSRMap 576 s = ((s.c_HCSR s.procID).hscratch,s) := by rfl
example (s : riscv_state) : CSRMap 577 s = ((s.c_HCSR s.procID).hepc,s) := by rfl
example (s : riscv_state) : CSRMap 578 s = («reg'mcause» (s.c_HCSR s.procID).hcause,s) := by rfl
example (s : riscv_state) : CSRMap 579 s = ((s.c_HCSR s.procID).hbadaddr,s) := by rfl
example (s : riscv_state) : CSRMap 768 s = («reg'mstatus» (s.c_MCSR s.procID).mstatus,s) := by rfl
example (s : riscv_state) : CSRMap 769 s = ((s.c_MCSR s.procID).mtvec,s) := by rfl
example (s : riscv_state) : CSRMap 770 s = («reg'mtdeleg» (s.c_MCSR s.procID).mtdeleg,s) := by rfl
example (s : riscv_state) : CSRMap 772 s = («reg'mie» (s.c_MCSR s.procID).mie,s) := by rfl
example (s : riscv_state) : CSRMap 801 s = ((s.c_MCSR s.procID).mtimecmp,s) := by rfl
example (s : riscv_state) : CSRMap 832 s = ((s.c_MCSR s.procID).mscratch,s) := by rfl
example (s : riscv_state) : CSRMap 833 s = ((s.c_MCSR s.procID).mepc,s) := by rfl
example (s : riscv_state) : CSRMap 834 s = («reg'mcause» (s.c_MCSR s.procID).mcause,s) := by rfl
example (s : riscv_state) : CSRMap 835 s = ((s.c_MCSR s.procID).mbadaddr,s) := by rfl
example (s : riscv_state) : CSRMap 836 s = («reg'mip» (s.c_MCSR s.procID).mip,s) := by rfl
example (s : riscv_state) : CSRMap 896 s = ((s.c_MCSR s.procID).mbase,s) := by rfl
example (s : riscv_state) : CSRMap 897 s = ((s.c_MCSR s.procID).mbound,s) := by rfl
example (s : riscv_state) : CSRMap 898 s = ((s.c_MCSR s.procID).mibase,s) := by rfl
example (s : riscv_state) : CSRMap 899 s = ((s.c_MCSR s.procID).mibound,s) := by rfl
example (s : riscv_state) : CSRMap 900 s = ((s.c_MCSR s.procID).mdbase,s) := by rfl
example (s : riscv_state) : CSRMap 901 s = ((s.c_MCSR s.procID).mdbound,s) := by rfl
example (s : riscv_state) : CSRMap 1920 s = ((s.c_MCSR s.procID).mtohost,s) := by rfl
example (s : riscv_state) : CSRMap 1921 s = ((s.c_MCSR s.procID).mfromhost,s) := by rfl
example (s : riscv_state) : CSRMap 1923 s = (0,s) := by rfl
example (s : riscv_state) : CSRMap 3394 s = («reg'mcause» (s.c_SCSR s.procID).scause,s) := by rfl
example (s : riscv_state) : CSRMap 3395 s = ((s.c_SCSR s.procID).sbadaddr,s) := by rfl
example (s : riscv_state) : CSRMap 3840 s = («reg'mcpuid» (s.c_MCSR s.procID).mcpuid,s) := by rfl
example (s : riscv_state) : CSRMap 3841 s = («reg'mimpid» (s.c_MCSR s.procID).mimpid,s) := by rfl
example (s : riscv_state) : CSRMap 3856 s = ((s.c_MCSR s.procID).mhartid,s) := by rfl

open Flapjack.Basis.Pure.MlString
example (s : riscv_state) : ((CSRMap 0 {s with exception := exception.NoException}).2).exception = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,48] : List HolChar) := by
  change exception.UNDEFINED (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32] : List HolChar) ++ holWordToHexString (0 : BitVec 12)) = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,48] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) : (CSRMap 0 {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}).2 = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) (v : BitVec 64) : ((«write'CSRMap» (v,0) {s with exception := exception.NoException})).exception = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,48] : List HolChar) := by
  change exception.INTERNAL_ERROR (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32] : List HolChar) ++ holWordToHexString (0 : BitVec 12)) = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,48] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) (v : BitVec 64) : («write'CSRMap» (v,0) {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}) = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) : (CSRMap 0 s).1 = Flapjack.holArb (BitVec 64) := by rfl
example (s : riscv_state) : ((CSRMap 773 {s with exception := exception.NoException}).2).exception = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,51,48,53] : List HolChar) := by
  change exception.UNDEFINED (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32] : List HolChar) ++ holWordToHexString (773 : BitVec 12)) = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,51,48,53] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) : (CSRMap 773 {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}).2 = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) (v : BitVec 64) : ((«write'CSRMap» (v,773) {s with exception := exception.NoException})).exception = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,51,48,53] : List HolChar) := by
  change exception.INTERNAL_ERROR (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32] : List HolChar) ++ holWordToHexString (773 : BitVec 12)) = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,51,48,53] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) (v : BitVec 64) : («write'CSRMap» (v,773) {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}) = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) : (CSRMap 773 s).1 = Flapjack.holArb (BitVec 64) := by rfl
example (s : riscv_state) : ((CSRMap 1922 {s with exception := exception.NoException}).2).exception = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,55,56,50] : List HolChar) := by
  change exception.UNDEFINED (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32] : List HolChar) ++ holWordToHexString (1922 : BitVec 12)) = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,55,56,50] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) : (CSRMap 1922 {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}).2 = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) (v : BitVec 64) : ((«write'CSRMap» (v,1922) {s with exception := exception.NoException})).exception = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,55,56,50] : List HolChar) := by
  change exception.INTERNAL_ERROR (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32] : List HolChar) ++ holWordToHexString (1922 : BitVec 12)) = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,55,56,50] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) (v : BitVec 64) : («write'CSRMap» (v,1922) {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}) = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) : (CSRMap 1922 s).1 = Flapjack.holArb (BitVec 64) := by rfl
example (s : riscv_state) : ((CSRMap 4095 {s with exception := exception.NoException}).2).exception = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,70,70,70] : List HolChar) := by
  change exception.UNDEFINED (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32] : List HolChar) ++ holWordToHexString (4095 : BitVec 12)) = exception.UNDEFINED ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,114,101,97,100,32,97,116,32,70,70,70] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) : (CSRMap 4095 {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}).2 = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) (v : BitVec 64) : ((«write'CSRMap» (v,4095) {s with exception := exception.NoException})).exception = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,70,70,70] : List HolChar) := by
  change exception.INTERNAL_ERROR (([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32] : List HolChar) ++ holWordToHexString (4095 : BitVec 12)) = exception.INTERNAL_ERROR ([117,110,101,120,112,101,99,116,101,100,32,67,83,82,32,119,114,105,116,101,32,116,111,32,70,70,70] : List HolChar)
  congr 1
  simp [Flapjack.holWordToHexString, Flapjack.holW2s, Flapjack.holN2s, Flapjack.holN2l, Flapjack.holHex]
example (s : riscv_state) (v : BitVec 64) : («write'CSRMap» (v,4095) {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)}) = {s with exception := exception.INTERNAL_ERROR ([112,114,105,111,114] : List HolChar)} := by rfl
example (s : riscv_state) : (CSRMap 4095 s).1 = Flapjack.holArb (BitVec 64) := by rfl
example (s : riscv_state) : sendIPI 0 {s with totalCore := 0} = {s with totalCore := 0} := by rfl
example (s : riscv_state) : sendIPI 0 {s with totalCore := 1} = {s with totalCore := 1, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 0 {s with totalCore := 2} = {s with totalCore := 2, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 0 {s with totalCore := 255} = {s with totalCore := 255, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 0 {s with totalCore := 256} = {s with totalCore := 256, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 1 {s with totalCore := 0} = {s with totalCore := 0} := by rfl
example (s : riscv_state) : sendIPI 1 {s with totalCore := 1} = {s with totalCore := 1} := by rfl
example (s : riscv_state) : sendIPI 1 {s with totalCore := 2} = {s with totalCore := 2, c_MCSR := holUpdate 1 {s.c_MCSR 1 with mip := {(s.c_MCSR 1).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 1 {s with totalCore := 255} = {s with totalCore := 255, c_MCSR := holUpdate 1 {s.c_MCSR 1 with mip := {(s.c_MCSR 1).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 1 {s with totalCore := 256} = {s with totalCore := 256, c_MCSR := holUpdate 1 {s.c_MCSR 1 with mip := {(s.c_MCSR 1).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 255 {s with totalCore := 0} = {s with totalCore := 0} := by rfl
example (s : riscv_state) : sendIPI 255 {s with totalCore := 1} = {s with totalCore := 1} := by rfl
example (s : riscv_state) : sendIPI 255 {s with totalCore := 2} = {s with totalCore := 2} := by rfl
example (s : riscv_state) : sendIPI 255 {s with totalCore := 255} = {s with totalCore := 255} := by rfl
example (s : riscv_state) : sendIPI 255 {s with totalCore := 256} = {s with totalCore := 256, c_MCSR := holUpdate 255 {s.c_MCSR 255 with mip := {(s.c_MCSR 255).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 256 {s with totalCore := 0} = {s with totalCore := 0} := by rfl
example (s : riscv_state) : sendIPI 256 {s with totalCore := 1} = {s with totalCore := 1, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 256 {s with totalCore := 2} = {s with totalCore := 2, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 256 {s with totalCore := 255} = {s with totalCore := 255, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 256 {s with totalCore := 256} = {s with totalCore := 256, c_MCSR := holUpdate 0 {s.c_MCSR 0 with mip := {(s.c_MCSR 0).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 257 {s with totalCore := 0} = {s with totalCore := 0} := by rfl
example (s : riscv_state) : sendIPI 257 {s with totalCore := 1} = {s with totalCore := 1} := by rfl
example (s : riscv_state) : sendIPI 257 {s with totalCore := 2} = {s with totalCore := 2, c_MCSR := holUpdate 1 {s.c_MCSR 1 with mip := {(s.c_MCSR 1).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 257 {s with totalCore := 255} = {s with totalCore := 255, c_MCSR := holUpdate 1 {s.c_MCSR 1 with mip := {(s.c_MCSR 1).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 257 {s with totalCore := 256} = {s with totalCore := 256, c_MCSR := holUpdate 1 {s.c_MCSR 1 with mip := {(s.c_MCSR 1).mip with MSIP := true}} s.c_MCSR} := by rfl
example (s : riscv_state) : sendIPI 18446744073709551615 {s with totalCore := 0} = {s with totalCore := 0} := by rfl
example (s : riscv_state) : sendIPI 18446744073709551615 {s with totalCore := 1} = {s with totalCore := 1} := by rfl
example (s : riscv_state) : sendIPI 18446744073709551615 {s with totalCore := 2} = {s with totalCore := 2} := by rfl
example (s : riscv_state) : sendIPI 18446744073709551615 {s with totalCore := 255} = {s with totalCore := 255} := by rfl
example (s : riscv_state) : sendIPI 18446744073709551615 {s with totalCore := 256} = {s with totalCore := 256, c_MCSR := holUpdate 255 {s.c_MCSR 255 with mip := {(s.c_MCSR 255).mip with MSIP := true}} s.c_MCSR} := by rfl
end Flapjack.Test.L3CSRDispatchParity
