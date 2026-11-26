/-
  文件：Pnp/Machine/SimObsRun.lean
  File: Pnp/Machine/SimObsRun.lean

  主题：驱动状态的「被模拟状态读数」`driveM` 与它的粘性——一旦读数等于接受态编号，
        之后的任何一步都仍是接受态编号。
  Topic: the simulated-state reading `driveM` of a driver state and its stickiness —
  once it equals the accept state's number, it stays so after any step.

  用途：耗尽轮中「模拟层是否已接受」只用读数判断，不必追踪具体相位；
  粘性把「沿途任一时刻接受」归约到「终点接受」，从而用终点格局（相位 14、
  读数 `m'`）一句话排除全部误接受。
  Use: acceptance along the exhaustion round is decided by the reading alone; stickiness
  reduces "accepts at some point" to "accepts at the end", excluded by the end state.

  本文件给出：
    - `driveM` 及嵌入形态的读数引理 `driveM_embS` / `driveM_embN`；
    - 模拟层一步的粘性 `simDrive_step_driveM_sim`；
    - 导航层一步的读数不变 `simDrive_step_driveM_nav`；
    - 运行级粘性 `simDrive_run_driveM_sticky`。
  This file provides the reading, its one-step stickiness in both layers, and the
  run-level sticky lemma.
-/

import Pnp.Machine.SimExhaust
import Pnp.Machine.SimDecide
import Pnp.Machine.SimVerdict
import Pnp.Machine.SimRoundM

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- 驱动状态的被模拟状态读数：模拟层直接读，导航层读内层（减 `stateCount`）。
    The simulated-state reading of a driver state. -/
def driveM (q b : Nat) (st : Fin (stateCountD q b)) : Nat :=
  if st.val < stateCount q b then unpackM (2 ^ b) 9 15 st.val
  else unpackM (2 ^ b) 9 15 (st.val - stateCount q b)

/-- 模拟层嵌入形态的读数。 -/
theorem driveM_embS (q b : Nat) (inner : Fin (stateCount q b)) :
    driveM q b (embS inner) = unpackM (2 ^ b) 9 15 inner.val := by
  rw [driveM, if_pos (by simpa only [embS, Fin.val_mk] using inner.isLt)]
  simp only [embS, Fin.val_mk]

/-- 导航层嵌入形态的读数。 -/
theorem driveM_embN (q b : Nat) (inner : Fin (stateCount q b)) :
    driveM q b (embN inner) = unpackM (2 ^ b) 9 15 inner.val := by
  rw [driveM, ite_eq_right (by simp only [embN, Fin.val_mk]; omega), embN, Fin.val_mk,
    Nat.add_sub_cancel_left]

/-- 规范形查表在编码状态上失败：读数为接受态时 `pick` 必为空。 -/
theorem pick_haltNorm_none_codeState (q b : Nat) (M : NTM q) (m c z ph : Nat)
    (a : Sym) (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (hph : ph < 15)
    (hacc : m = M.accept.val) :
    pick ((M.haltNorm).step (⟨m, hm⟩ : Fin q) a) c = none := by
  subst hacc
  exact pick_haltNorm_none M { state := ⟨M.accept.val, hm⟩, pre := [], cur := a, post := [] } c
    (Or.inl rfl)

/-- **导航层一步不改变读数**：导航层的所有转移都保留内层被模拟状态。
    A navigation-layer step keeps the reading unchanged. -/
theorem simDrive_step_driveM_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCountD q b)) (a : Sym) (h1 : ¬ st.val < stateCount q b)
    (h2 : st.val < 2 * stateCount q b) :
    driveM q b ((simDrive q b tab s0).step st a).1
      = unpackM (2 ^ b) 9 15 (st.val - stateCount q b) := by
  have h2' : ¬ st.val = 2 * stateCount q b := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2']
  repeat' split
  all_goals first
    | (simp only [driveM_embN, driveM_embS, codeState_unpackM]; done)
    | rw [driveM, ite_eq_right (by omega : ¬ st.val < stateCount q b)]
  all_goals simp_all

/-- **模拟层一步：接受态读数保持**。规范形下接受态查表必失败，读写步不改 `m`。
    A simulation-layer step keeps the reading once it is the accept state. -/
theorem simStep_step_unpackM_accept (q b : Nat) (M : NTM q)
    (st : Fin (stateCount q b)) (a : Sym)
    (h13 : unpackPh (2 ^ b) 9 15 st.val ≠ 13)
    (h : unpackM (2 ^ b) 9 15 st.val = M.accept.val) :
    unpackM (2 ^ b) 9 15 ((simStep q b (M.haltNorm).step M.start).step st a).1.val
      = M.accept.val := by
  have hph : unpackPh (2 ^ b) 9 15 st.val < 15 := unpackPh_lt (2 ^ b) 9 15 st.val (by decide)
  have hcases : unpackPh (2 ^ b) 9 15 st.val = 0 ∨ unpackPh (2 ^ b) 9 15 st.val = 1 ∨ unpackPh (2 ^ b) 9 15 st.val = 2 ∨ unpackPh (2 ^ b) 9 15 st.val = 3 ∨ unpackPh (2 ^ b) 9 15 st.val = 4 ∨ unpackPh (2 ^ b) 9 15 st.val = 5 ∨ unpackPh (2 ^ b) 9 15 st.val = 6 ∨ unpackPh (2 ^ b) 9 15 st.val = 7 ∨ unpackPh (2 ^ b) 9 15 st.val = 8 ∨ unpackPh (2 ^ b) 9 15 st.val = 9 ∨ unpackPh (2 ^ b) 9 15 st.val = 10 ∨ unpackPh (2 ^ b) 9 15 st.val = 11 ∨ unpackPh (2 ^ b) 9 15 st.val = 12 ∨ unpackPh (2 ^ b) 9 15 st.val = 14 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h14
  · -- 相位 0：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 0 := h0
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 1 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase0 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 1：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 1 := h1
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (symIdx a) 2 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (by have := symIdx_lt a; omega) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase1 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 2：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 2 := h2
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (symIdxOfCode a (symOfIdx (unpackZ (2 ^ b) 9 15 st.val))) 3 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (by have := symIdxOfCode_lt a (symOfIdx (unpackZ (2 ^ b) 9 15 st.val)); omega) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase2 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 3：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 3 := h3
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 4 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase3 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 4：查表。接受态在规范形下查表必失败，故 `m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 4 := h4
    have hlook : lookupRes q b (M.haltNorm).step st = none := by
      have hm' : decM q b st = (⟨M.accept.val, M.accept.isLt⟩ : Fin q) := by
        apply Fin.ext
        simp only [decM]
        exact h
      simp only [lookupRes, hm']
      exact pick_haltNorm_none M
        { state := ⟨M.accept.val, M.accept.isLt⟩, pre := [],
           cur := symOfIdx (decZ b st), post := [] } _ (Or.inl rfl)
    cases hl : lookupRes q b (M.haltNorm).step st with
    | none =>
        have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
            codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
              (unpackZ (2 ^ b) 9 15 st.val) 14 (unpackM_lt q b st.val st.isLt)
              (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
              (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
          have := congrArg Config.state
            (simStep_step_phase4_none q b (M.haltNorm).step M.start st a [] [] hp' hl)
          simpa [DTM.stepConfig, Tape.read, List.headD] using this
        rw [hstate]
        simp only [codeState_unpackM]
        exact h
    | some v =>
        rw [hlook] at hl
        cases hl
  · -- 相位 5：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 5 := h5
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 6 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase5 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 6：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 6 := h6
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 7 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase6 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 7：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 7 := h7
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 8 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase7 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 8：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 8 := h8
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 9 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase8 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 9：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 9 := h9
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 10 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase9 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 10：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 10 := h10
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 11 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase10 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 11：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 11 := h11
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 12 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase11 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 12：读写步，`m` 不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 12 := h12
    have hstate : ((simStep q b (M.haltNorm).step M.start).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
          (unpackZ (2 ^ b) 9 15 st.val) 13 (unpackM_lt q b st.val st.isLt)
          (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
          (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase12 q b (M.haltNorm).step M.start st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    rw [hstate]
    simp only [codeState_unpackM]
    exact h
  · -- 相位 14：死点，状态不变
    have hp' : unpackPh (2 ^ b) 9 15 st.val = 14 := h14
    rw [simStep_step_ph14_state q b (M.haltNorm).step M.start st a hp']
    exact h

/-- **驱动模拟层一步：接受态读数保持**。 -/
theorem simDrive_step_driveM_sim (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (a : Sym) (hlt : st.val < stateCount q b)
    (hm : unpackM (2 ^ b) 9 15 st.val = M.accept.val) :
    driveM q b ((simDrive q b (M.haltNorm).step M.start).step st a).1 = M.accept.val := by
  simp only [simDrive]
  rw [dite_eq_left hlt]
  by_cases h13 : unpackPh (2 ^ b) 9 15 st.val = 13
  · rw [if_pos h13]
    split <;> (simp only [driveM_embN, codeState_unpackM]; exact hm)
  · rw [if_neg h13]
    simp only [driveM_embS]
    exact simStep_step_unpackM_accept q b M ⟨st.val, hlt⟩ a h13 hm

/-- 驱动状态在范围内时不停机（哨兵状态号是 `2 * stateCount`）。 -/
theorem simDrive_halted_false_of_range (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCountD q b)) (t : Tape) (h : st.val < 2 * stateCount q b) :
    (simDrive q b tab s0).halted (Config.mk st t) = false := by
  have hne : st ≠ (⟨2 * stateCount q b, by unfold stateCountD; omega⟩ :
      Fin (stateCountD q b)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  have ha : (simDrive q b tab s0).accept
      = (⟨2 * stateCount q b, by unfold stateCountD; omega⟩ : Fin (stateCountD q b)) := rfl
  have hr : (simDrive q b tab s0).reject
      = (⟨2 * stateCount q b, by unfold stateCountD; omega⟩ : Fin (stateCountD q b)) := rfl
  rw [DTM.halted, ha, hr, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hne⟩

/-- **一步读数**：驱动状态走一步后的读数，模拟层与导航层统一处理。 -/
theorem simDrive_step_driveM (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (a : Sym)
    (hrange : st.val < 2 * stateCount q b)
    (h : driveM q b st = M.accept.val) :
    driveM q b ((simDrive q b (M.haltNorm).step M.start).step st a).1 = M.accept.val := by
  by_cases hlt : st.val < stateCount q b
  · have hm : unpackM (2 ^ b) 9 15 st.val = M.accept.val := by
      rw [driveM, ite_eq_left hlt] at h
      exact h
    exact simDrive_step_driveM_sim q b M st a hlt hm
  · have h' : unpackM (2 ^ b) 9 15 (st.val - stateCount q b) = M.accept.val := by
      rw [driveM, ite_eq_right hlt] at h
      exact h
    rw [simDrive_step_driveM_nav q b (M.haltNorm).step M.start st a hlt hrange]
    exact h'

/-- **读数粘性（运行级）**：起点在范围内且某时刻读数为接受态，则之后一直是接受态。 -/
theorem simDrive_run_driveM_sticky (q b : Nat) (M : NTM q)
    (c₀ : Config (stateCountD q b)) (h0 : c₀.state.val < 2 * stateCount q b) :
    ∀ (k i : Nat),
      driveM q b ((simDrive q b (M.haltNorm).step M.start).run i c₀).state = M.accept.val →
      driveM q b ((simDrive q b (M.haltNorm).step M.start).run (i + k) c₀).state
        = M.accept.val := by
  intro k
  induction k with
  | zero => intro i h; simpa using h
  | succ k ih =>
      intro i h
      have hnh := simDrive_halted_false_of_range q b (M.haltNorm).step M.start
        ((simDrive q b (M.haltNorm).step M.start).run i c₀).state
        ((simDrive q b (M.haltNorm).step M.start).run i c₀).tape
        (simDrive_run_range q b (M.haltNorm).step M.start i c₀ h0)
      have hone : (simDrive q b (M.haltNorm).step M.start).run (i + 1) c₀
          = (simDrive q b (M.haltNorm).step M.start).stepConfig
              ((simDrive q b (M.haltNorm).step M.start).run i c₀) := by
        exact DTM.run_succ_last (simDrive q b (M.haltNorm).step M.start) i c₀ hnh
      have hstep : driveM q b
          ((simDrive q b (M.haltNorm).step M.start).run (i + 1) c₀).state
          = M.accept.val := by
        rw [hone]
        simp only [DTM.stepConfig, Tape.read]
        exact simDrive_step_driveM q b M _ _
          (simDrive_run_range q b (M.haltNorm).step M.start i c₀ h0) h
      rw [show i + (k + 1) = (i + 1) + k from by omega]
      exact ih (i + 1) hstep

/-- 终点读数非接受 ⇒ 全程读数非接受（粘性逆否）。 -/
theorem simDrive_run_driveM_ne_accept (q b : Nat) (M : NTM q)
    (c₀ : Config (stateCountD q b)) (h0 : c₀.state.val < 2 * stateCount q b)
    (N : Nat)
    (hN : driveM q b ((simDrive q b (M.haltNorm).step M.start).run N c₀).state
      ≠ M.accept.val) :
    ∀ i : Nat, i ≤ N →
      driveM q b ((simDrive q b (M.haltNorm).step M.start).run i c₀).state
        ≠ M.accept.val := by
  intro i hi hacc
  have hst := simDrive_run_driveM_sticky q b M c₀ h0 (N - i) i hacc
  rw [show i + (N - i) = N from by omega] at hst
  exact hN hst

/-- **观察机委托直到失败**：驱动全程不停机、读数不是接受态、状态在范围内时，
    观察机与驱动逐步一致；一旦驱动落入相位 14（或接受），观察机在该步落入哨兵。
    The observer follows the driver step by step while the reading is not the accept
    state; if the driver hits phase 14, the observer lands on `obsFail`. -/
theorem simObs_run_delegate_until_fail (q b : Nat) (M : NTM q) :
    ∀ (n : Nat) (c : Config (stateCountD q b)),
      (∀ i : Nat, i ≤ n →
        driveM q b ((simDrive q b (M.haltNorm).step M.start).run i c).state
          ≠ M.accept.val) →
      (∀ i : Nat, i ≤ n →
        ((simDrive q b (M.haltNorm).step M.start).run i c).state.val
          < 2 * stateCount q b) →
      ((simObs q b (M.haltNorm)).run n
          (Config.mk (embO q b c.state) c.tape)
        = Config.mk (embO q b ((simDrive q b (M.haltNorm).step M.start).run n c).state)
            ((simDrive q b (M.haltNorm).step M.start).run n c).tape
      ∨ ((simObs q b (M.haltNorm)).run n
          (Config.mk (embO q b c.state) c.tape)).state = obsFail q b) := by
  intro n
  induction n with
  | zero =>
      intro c _ _
      left
      rfl
  | succ n ih =>
      intro c hacc hrange
      rcases ih c (fun i hi => hacc i (by omega)) (fun i hi => hrange i (by omega)) with
        hdel | hfail
      · -- 前 `n` 步委托：看第 `n` 个状态属于哪一层
        have hrg : ((simDrive q b (M.haltNorm).step M.start).run n c).state.val
            < 2 * stateCount q b := hrange n (by omega)
        have hh : (simDrive q b (M.haltNorm).step M.start).halted
            ((simDrive q b (M.haltNorm).step M.start).run n c) = false :=
          simDrive_halted_false_of_range q b (M.haltNorm).step M.start
            ((simDrive q b (M.haltNorm).step M.start).run n c).state
            ((simDrive q b (M.haltNorm).step M.start).run n c).tape hrg
        have hltD : ((simDrive q b (M.haltNorm).step M.start).run n c).state.val
            < stateCountD q b :=
          ((simDrive q b (M.haltNorm).step M.start).run n c).state.isLt
        have hhn : (simObs q b (M.haltNorm)).halted
            (Config.mk (embO q b ((simDrive q b (M.haltNorm).step M.start).run n c).state)
              ((simDrive q b (M.haltNorm).step M.start).run n c).tape) = false :=
          simObs_halted_inner q b (M.haltNorm) _ hltD _
        have hstepD := DTM.run_succ_last (simDrive q b (M.haltNorm).step M.start) n c hh
        have hstepO := DTM.run_succ_last (simObs q b (M.haltNorm)) n
          (Config.mk (embO q b c.state) c.tape) (by
            rw [hdel]; exact hhn)
        by_cases hlt : ((simDrive q b (M.haltNorm).step M.start).run n c).state.val
            < stateCount q b
        · by_cases h14 : unpackPh (2 ^ b) 9 15
              ((simDrive q b (M.haltNorm).step M.start).run n c).state.val = 14
          · -- 模拟层相位 14：观察机在该步进入失败哨兵
            right
            have hsacc : unpackM (2 ^ b) 9 15
                ((simDrive q b (M.haltNorm).step M.start).run n c).state.val
                ≠ (M.haltNorm).accept.val := by
              have h := hacc n (by omega)
              rwa [driveM, ite_eq_left hlt] at h
            rw [hstepO, hdel]
            simp only [DTM.stepConfig, simObs, embO]
            rw [dif_pos hltD, dif_pos hlt, if_neg hsacc, if_pos h14]
          · -- 模拟层可委托：逐步一致
            left
            have hsacc : unpackM (2 ^ b) 9 15
                ((simDrive q b (M.haltNorm).step M.start).run n c).state.val
                ≠ M.accept.val := by
              have h := hacc n (by omega)
              rwa [driveM, ite_eq_left hlt] at h
            have hd : observeState q b (M.haltNorm)
                ((simDrive q b (M.haltNorm).step M.start).run n c).state :=
              ⟨hrg, fun _ => ⟨hsacc, h14⟩⟩
            rw [hstepO, hdel, hstepD]
            exact simObs_stepConfig_delegate q b (M.haltNorm) _ _ hd
        · -- 导航层：照搬驱动
          left
          have hd : observeState q b (M.haltNorm)
              ((simDrive q b (M.haltNorm).step M.start).run n c).state :=
            ⟨hrg, fun hc => absurd hc hlt⟩
          rw [hstepO, hdel, hstepD]
          exact simObs_stepConfig_delegate q b (M.haltNorm) _ _ hd
      · -- 已在失败哨兵：观察机停机，停在那里
        right
        have hst : (simObs q b (M.haltNorm)).halted
            ((simObs q b (M.haltNorm)).run n
              (Config.mk (embO q b c.state) c.tape)) = true :=
          halted_of_accept_or_reject (simObs q b (M.haltNorm)) _ (Or.inr hfail)
        rw [DTM.run_add (simObs q b (M.haltNorm)) n 1, DTM.run]
        simp only [hst, ite_true]
        exact hfail

end DTM

end Pnp
