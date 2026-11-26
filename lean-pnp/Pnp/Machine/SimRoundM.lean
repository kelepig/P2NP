/-
  文件：Pnp/Machine/SimRoundM.lean
  主题：轮内「被模拟状态 `m`」的分析——一轮之内模拟层携带的 `m` 只可能是
        轮起点区域状态（阶段 ≤ 4）或查表结果状态（阶段 ≥ 5）。

  为什么需要它（docs/decisions/auto-run-log.md #93）：观察机命中接受哨兵时只
  看到模拟层的 `m = accept`；要把这一命中归约到「某个前缀通路终态区域是接受」，
  必须知道轮内的 `m` 不会凭空跳到别的值。

  In-round `m` analysis: inside one round the simulation layer carries either the
  round-start region state (phases ≤ 4) or the lookup result state (phases ≥ 5).
-/

import Pnp.Machine.SimPassPrefix
import Pnp.Machine.SimDecide

set_option maxHeartbeats 1600000

namespace Pnp

namespace DTM

/-- 阶段 ≠ 4（且 ≤ 12）时，模拟一步保持被模拟状态 `m`。
    Outside phase 4 the step preserves the simulated state `m`. -/
theorem simStep_step_unpackM_ph_ne4 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val ≠ 4)
    (h12 : unpackPh (2 ^ b) 9 15 st.val ≤ 12) :
    unpackM (2 ^ b) 9 15 ((simStep q b tab s0).step st a).1.val
      = unpackM (2 ^ b) 9 15 st.val := by
  have hcases : unpackPh (2 ^ b) 9 15 st.val = 0
      ∨ unpackPh (2 ^ b) 9 15 st.val = 1
      ∨ unpackPh (2 ^ b) 9 15 st.val = 2
      ∨ unpackPh (2 ^ b) 9 15 st.val = 3
      ∨ unpackPh (2 ^ b) 9 15 st.val = 5
      ∨ unpackPh (2 ^ b) 9 15 st.val = 6
      ∨ unpackPh (2 ^ b) 9 15 st.val = 7
      ∨ unpackPh (2 ^ b) 9 15 st.val = 8
      ∨ unpackPh (2 ^ b) 9 15 st.val = 9
      ∨ unpackPh (2 ^ b) 9 15 st.val = 10
      ∨ unpackPh (2 ^ b) 9 15 st.val = 11
      ∨ unpackPh (2 ^ b) 9 15 st.val = 12 := by
    rcases Nat.lt_or_ge (unpackPh (2 ^ b) 9 15 st.val) 4 with h | h
    · omega
    · omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h
  · have hs := congrArg Config.state (simStep_step_phase0 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase1 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase2 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase3 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase5 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase6 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase7 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase8 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase9 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase10 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase11 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]
  · have hs := congrArg Config.state (simStep_step_phase12 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackM]

/-- 阶段 4 查表命中时，一步之后 `m` 变为查到的状态。
    A successful lookup at phase 4 turns `m` into the looked-up state. -/
theorem simStep_step_phase4_unpackM (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 4)
    (m' : Fin q) (s' : Sym) (d : Dir)
    (h : lookupRes q b tab st = some (m', s', d)) :
    unpackM (2 ^ b) 9 15 ((simStep q b tab s0).step st a).1.val = m'.val := by
  have hs := congrArg Config.state
    (simStep_step_phase4_some q b tab s0 st a [] [] hP m' s' d h)
  simp only [DTM.stepConfig, Tape.read, List.headD] at hs
  rw [hs, codeState_unpackM]

/-- 阶段 ≠ 4（且 ≤ 12）时，模拟一步把相位推进到 `ph + 1`（不会失败）。
    Outside phase 4 a step advances the phase by exactly one. -/
theorem simStep_step_unpackPh_ph_ne4 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val ≠ 4)
    (h12 : unpackPh (2 ^ b) 9 15 st.val ≤ 12) :
    unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).step st a).1.val
      = unpackPh (2 ^ b) 9 15 st.val + 1 := by
  have hcases : unpackPh (2 ^ b) 9 15 st.val = 0
      ∨ unpackPh (2 ^ b) 9 15 st.val = 1
      ∨ unpackPh (2 ^ b) 9 15 st.val = 2
      ∨ unpackPh (2 ^ b) 9 15 st.val = 3
      ∨ unpackPh (2 ^ b) 9 15 st.val = 5
      ∨ unpackPh (2 ^ b) 9 15 st.val = 6
      ∨ unpackPh (2 ^ b) 9 15 st.val = 7
      ∨ unpackPh (2 ^ b) 9 15 st.val = 8
      ∨ unpackPh (2 ^ b) 9 15 st.val = 9
      ∨ unpackPh (2 ^ b) 9 15 st.val = 10
      ∨ unpackPh (2 ^ b) 9 15 st.val = 11
      ∨ unpackPh (2 ^ b) 9 15 st.val = 12 := by
    rcases Nat.lt_or_ge (unpackPh (2 ^ b) 9 15 st.val) 4 with h | h
    · omega
    · omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h
  · have hs := congrArg Config.state (simStep_step_phase0 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase1 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase2 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase3 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase5 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase6 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase7 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase8 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase9 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase10 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase11 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]
  · have hs := congrArg Config.state (simStep_step_phase12 q b tab s0 st a [] [] h)
    simp only [DTM.stepConfig, Tape.read, List.headD] at hs
    rw [hs, codeState_unpackPh, h]

/-- 前 4 步之内相位恰为步数（不会提前死亡）。
    Within the first four steps the phase equals the step count. -/
theorem simStep_run_ph_lt5 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Config (stateCount q b))
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0) :
    ∀ k, k ≤ 4 →
      unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val = k := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa [DTM.run] using h0
  | succ k ih =>
      intro hk
      have hk4 : k ≤ 4 := by omega
      have hk3 : k ≤ 3 := by omega
      have hph := ih hk4
      have hhalt : (simStep q b tab s0).halted ((simStep q b tab s0).run k c) = false := by
        apply simStep_halted_ph_ne q b tab s0 ((simStep q b tab s0).run k c).state _ _
        omega
      have hne4 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≠ 4 := by
        omega
      have hle12 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≤ 12 := by
        omega
      rw [DTM.run_succ_last (simStep q b tab s0) k c hhalt, stepConfig_state,
        simStep_step_unpackPh_ph_ne4 q b tab s0 _ _ hne4 hle12, hph]

/-- 阶段 14 的一步不改变状态（死点）。
    A step in dead phase 14 keeps the state. -/
theorem simStep_step_ph14_state (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    ((simStep q b tab s0).step st a).1 = st := by
  have hs := congrArg Config.state (simStep_step_phase14 q b tab s0 st a [] [] hP)
  simpa [DTM.stepConfig, Tape.read, List.headD] using hs

/-- **相位精确推进**：从相位 0 出发，第 `k` 步（`k ≤ 13`）之后相位恰为 `k`，
    或已落入死相位 14。
    Exact phase progression: after step `k ≤ 13` the phase is exactly `k` or 14. -/
theorem simStep_run_ph_exact (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Config (stateCount q b))
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0) :
    ∀ k, k ≤ 13 →
      unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val = k
        ∨ unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val = 14 := by
  intro k
  induction k with
  | zero =>
      intro _
      left
      simpa [DTM.run] using h0
  | succ k ih =>
      intro hk
      have hk' : k ≤ 13 := by omega
      have hk12 : k ≤ 12 := by omega
      have hhalt : (simStep q b tab s0).halted ((simStep q b tab s0).run k c) = false := by
        apply simStep_halted_ph_ne q b tab s0 ((simStep q b tab s0).run k c).state _ _
        rcases ih hk' with h | h <;> omega
      rw [DTM.run_succ_last (simStep q b tab s0) k c hhalt]
      rcases ih hk' with h | h
      · have hst := simStep_ph_stepConfig q b tab s0 ((simStep q b tab s0).run k c) (by omega)
        rcases hst with hst | hst
        · left
          rw [hst, h]
        · right
          exact hst
      · right
        exact simStep_ph14_stepConfig q b tab s0 ((simStep q b tab s0).run k c) h

/-- 前 4 步之内（阶段 ≤ 4）被模拟状态保持为起点值。
    Within the first four steps (phases ≤ 4) the simulated state stays at its start value. -/
theorem simStep_run_unpackM_le (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Config (stateCount q b)) (m0 : Nat)
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0)
    (hm0 : unpackM (2 ^ b) 9 15 c.state.val = m0) :
    ∀ k, k ≤ 4 →
      unpackM (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val = m0 := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa [DTM.run] using hm0
  | succ k ih =>
      intro hk
      have hk4 : k ≤ 4 := by omega
      have hk3 : k ≤ 3 := by omega
      have hph := simStep_run_ph_lt5 q b tab s0 c h0 k hk4
      have hhalt : (simStep q b tab s0).halted ((simStep q b tab s0).run k c) = false := by
        apply simStep_halted_ph_ne q b tab s0 ((simStep q b tab s0).run k c).state _ _
        omega
      have hne4 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≠ 4 := by
        omega
      have hle12 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≤ 12 := by
        omega
      rw [DTM.run_succ_last (simStep q b tab s0) k c hhalt, stepConfig_state,
        simStep_step_unpackM_ph_ne4 q b tab s0 _ _ hne4 hle12]
      exact ih hk4

/-- 第 4 步查表命中之后（阶段 ≥ 5）被模拟状态保持为查到的状态。
    After the successful lookup at step 4 (phases ≥ 5) the simulated state stays at
    the looked-up state. -/
theorem simStep_run_unpackM_ge (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Config (stateCount q b))
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0)
    (hp4 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run 4 c).state.val = 4)
    (m' : Fin q) (s' : Sym) (d : Dir)
    (hlook : lookupRes q b tab ((simStep q b tab s0).run 4 c).state = some (m', s', d)) :
    ∀ k, 5 ≤ k → k ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val = m'.val := by
  have hnot : (simStep q b tab s0).halted ((simStep q b tab s0).run 4 c) = false := by
    apply simStep_halted_ph_ne q b tab s0 ((simStep q b tab s0).run 4 c).state _ _
    omega
  intro k
  induction k with
  | zero =>
      intro hk5 _
      omega
  | succ k ih =>
      intro hk5 hk13
      rcases Nat.lt_or_ge k 5 with hklt | hkge
      · have hk4 : k = 4 := by omega
        subst hk4
        rw [DTM.run_succ_last (simStep q b tab s0) 4 c hnot]
        exact simStep_step_phase4_unpackM q b tab s0 _ _ hp4 m' s' d hlook
      · have hk13' : k ≤ 12 := by omega
        have hph := simStep_run_ph_exact q b tab s0 c h0 k (by omega)
        have hhalt : (simStep q b tab s0).halted ((simStep q b tab s0).run k c) = false := by
          apply simStep_halted_ph_ne q b tab s0 ((simStep q b tab s0).run k c).state _ _
          rcases hph with h | h <;> omega
        rw [DTM.run_succ_last (simStep q b tab s0) k c hhalt]
        rcases hph with h | h
        · have hne4 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≠ 4 := by
            omega
          have hle12 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≤ 12 := by
            omega
          rw [stepConfig_state,
            simStep_step_unpackM_ph_ne4 q b tab s0 _ _ hne4 hle12]
          exact ih (by omega) (by omega)
        · rw [stepConfig_state, simStep_step_ph14_state q b tab s0 _ _ h]
          exact ih (by omega) (by omega)

/-- 驱动层：从 `passStart` 出发，前 13 步都停在模拟层且与 `simStep` 的运行逐点一致。
    Drive level: for the first 13 steps the drive stays in the simulation layer and
    follows `simStep` exactly. -/
theorem simDrive_passStart_run13 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z : Nat) (ks : List Nat) :
    ∀ i, i ≤ 13 →
      (simDrive q b tab s0).run i (passStart x m c hm hc Z ks) =
        Config.mk
          (embS ((simStep q b tab s0).run i
            (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
              (x.enc (none :: List.replicate Z (some false) ++ digitArea ks)))).state)
          ((simStep q b tab s0).run i
            (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
              (x.enc (none :: List.replicate Z (some false) ++ digitArea ks)))).tape := by
  intro i hi
  refine simDrive_run_embS q b tab s0 i
    (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
      (x.enc (none :: List.replicate Z (some false) ++ digitArea ks))) ?_
  intro k hk
  exact simStep_run_ph_ne13 q b tab s0 _
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)) k (by omega)

/-- 驱动层与 `simStep` 的 `m` 一致（前 13 步）。
    The drive's `m` agrees with `simStep`'s during the first 13 steps. -/
theorem simDrive_passStart_unpackM (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z : Nat) (ks : List Nat) :
    ∀ i, i ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i (passStart x m c hm hc Z ks)).state.val
        = unpackM (2 ^ b) 9 15 ((simStep q b tab s0).run i
            (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
              (x.enc (none :: List.replicate Z (some false) ++ digitArea ks)))).state.val := by
  intro i hi
  rw [simDrive_passStart_run13 q b tab s0 x m c hm hc Z ks i hi]
  rfl

/-- 轮内前 4 步（阶段 ≤ 4）：驱动层模拟状态保持为轮起点值 `m`。
    In the first four steps the drive's simulated state stays at the round start. -/
theorem simDrive_passStart_unpackM_le (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z : Nat) (ks : List Nat) :
    ∀ i, i ≤ 4 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i (passStart x m c hm hc Z ks)).state.val
        = m := by
  intro i hi
  rw [simDrive_passStart_unpackM q b tab s0 x m c hm hc Z ks i (by omega)]
  exact simStep_run_unpackM_le q b tab s0 _
    m
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
    (codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide)) i hi

/-- 查表命中后（阶段 ≥ 5、步数 ≤ 13）：驱动层模拟状态保持为查到的状态 `m'`。
    After the successful lookup the drive's simulated state stays at the looked-up state. -/
theorem simDrive_passStart_unpackM_ge (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z : Nat) (ks : List Nat)
    (m' : Fin q) (s' : Sym) (d : Dir)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpick : pick (tab x.state x.cur) c = some (m', s', d)) :
    ∀ i, 5 ≤ i → i ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i (passStart x m c hm hc Z ks)).state.val
        = m'.val := by
  -- 起点格局与 `simStep_read_run` 的纸带形状一致
  have hread := simStep_read_run q b tab s0 m c hm hc x.cur x.pre x.post
    (none :: List.replicate Z (some false) ++ digitArea ks)
  rw [tape_eq_enc x (none :: List.replicate Z (some false) ++ digitArea ks)] at hread
  have hp4 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run 4
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (x.enc (none :: List.replicate Z (some false) ++ digitArea ks)))).state.val = 4 :=
    simStep_run_ph_lt5 q b tab s0 _
      (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)) 4 (by decide)
  have hlook : lookupRes q b tab ((simStep q b tab s0).run 4
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (x.enc (none :: List.replicate Z (some false) ++ digitArea ks)))).state
      = some (m', s', d) := by
    rw [hread]
    rw [lookupRes_codeState, symOfIdx_symIdx, ← hx]
    exact hpick
  intro i hi5 hi13
  rw [simDrive_passStart_unpackM q b tab s0 x m c hm hc Z ks i (by omega)]
  exact simStep_run_unpackM_ge q b tab s0 _
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
    hp4 m' s' d hlook i hi5 hi13

/-- 导航层一步（子相位 ≠ 7，且不是「数字区耗尽」那一跳）后仍停在导航层。
    唯一的例外是子相位 1 读到空白：那一跳转入模拟层失败相位 14（见
    `simDrive_step_ph1_blank`），故需显式排除。
    A navigation-layer step stays in the navigation layer unless it is the
    digit-area-exhaustion jump (sub-phase 1 reading blank). -/
theorem simDrive_step_nav_val (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (s : Fin (stateCount q b)) (a : Sym)
    (hph : unpackPh (2 ^ b) 9 15 s.val ≠ 7)
    (hexh : ¬ (unpackPh (2 ^ b) 9 15 s.val = 1 ∧ a = none)) :
    stateCount q b ≤ ((simDrive q b tab s0).step (embN s) a).1.val := by
  have hpos : 0 < stateCount q b := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have h1 : ¬ (stateCount q b + s.val < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + s.val = 2 * stateCount q b) := by omega
  simp only [simDrive, embN, Fin.val_mk, dite_eq_right h1, dite_eq_right h2,
    Nat.add_sub_cancel_left]
  repeat' split
  all_goals first
    | exact absurd ‹unpackPh (2 ^ b) 9 15 s.val = 7› hph
    | (exfalso; exact hexh ⟨‹unpackPh (2 ^ b) 9 15 s.val = 1›, rfl⟩)
    | omega
    | (simp only [embN, Fin.val_mk]; omega)

/-- 导航层一步（子相位 ≠ 7，且不是「数字区耗尽」那一跳）保持「内层被模拟状态」`m`。
    A navigation-layer step (excluding the digit-area-exhaustion jump) preserves
    the inner simulated state. -/
theorem simDrive_step_nav_m (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (s : Fin (stateCount q b)) (a : Sym)
    (hph : unpackPh (2 ^ b) 9 15 s.val ≠ 7)
    (hexh : ¬ (unpackPh (2 ^ b) 9 15 s.val = 1 ∧ a = none)) :
    unpackM (2 ^ b) 9 15
        (((simDrive q b tab s0).step (embN s) a).1.val - stateCount q b)
      = unpackM (2 ^ b) 9 15 s.val := by
  have hpos : 0 < stateCount q b := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have h1 : ¬ (stateCount q b + s.val < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + s.val = 2 * stateCount q b) := by omega
  simp only [simDrive, embN, Fin.val_mk, dite_eq_right h1, dite_eq_right h2,
    Nat.add_sub_cancel_left]
  repeat' split
  all_goals first
    | exact absurd ‹unpackPh (2 ^ b) 9 15 s.val = 7› hph
    | (exfalso; exact hexh ⟨‹unpackPh (2 ^ b) 9 15 s.val = 1›, rfl⟩)
    | skip
  all_goals simp only [codeState_unpackM, Nat.add_sub_cancel_left]

/-- 导航层子相位 7 且读到标记：回到模拟层，`m` 不变。
    Sub-phase 7 reading the marker returns to the simulation layer, `m` unchanged. -/
theorem simDrive_step_ph7_sim (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (s : Fin (stateCount q b)) (a : Sym)
    (hph : unpackPh (2 ^ b) 9 15 s.val = 7) :
    ((simDrive q b tab s0).step (embN s) a).1.val < stateCount q b ∧
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).step (embN s) a).1.val
        = unpackM (2 ^ b) 9 15 s.val := by
  have hpos : 0 < stateCount q b := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have h1 : ¬ (stateCount q b + s.val < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + s.val = 2 * stateCount q b) := by omega
  simp only [simDrive, embN, Fin.val_mk, dite_eq_right h1, dite_eq_right h2,
    Nat.add_sub_cancel_left]
  repeat' split
  all_goals first
    | exact absurd hph (by omega)
    | skip
  constructor
  · simp only [embS, Fin.val_mk]
    omega
  · simp only [embS, codeState_unpackM]

/-- 导航层状态的数值下界。`embN` states are at least `stateCount`. -/
theorem embN_val_ge (q b : Nat) (s : Fin (stateCount q b)) :
    stateCount q b ≤ (embN s).val := by
  simp only [embN, Fin.val_mk]
  exact Nat.le_add_right (stateCount q b) s.val

/-- `run 0` 归约。 -/
theorem simRun_zero (q : Nat) (M : DTM q) (c : Config q) : M.run 0 c = c := rfl

/-- `run 1` 单步（数码字面量形式，便于 `rw` 句法匹配）。 -/
theorem simRun_one (q : Nat) (M : DTM q) (c : Config q) (h : M.halted c = false) :
    M.run 1 c = M.stepConfig c := DTM.run_succ_of_not_halted M 0 c h

/-- **回扫段全程在导航层**：从导航层回扫起点出发、步数不超过 `|L0|+2` 时，
    运行中的每一步状态都在导航层（`val ≥ stateCount`）。
    Every intermediate state of the rewind segment stays in the navigation layer. -/
theorem simDrive_rewind_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (x : Sym) (L0 : List Sym), x ≠ none → (∀ y ∈ L0, y ≠ none) →
      ∀ (a0 : Sym) (Z' M : List Sym) (i : Nat), i ≤ L0.length + 2 →
        stateCount q b ≤ ((simDrive q b tab s0).run i
          (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (Tape.mk (L0 ++ none :: a0 :: Z') (x :: M)))).state.val
  | x, [], hx, _, a0, Z', M, i, hi => by
      match i with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m c 0 0 hm hc (by decide) (by decide))).val
          exact embN_val_ge q b _
      | 1 =>
          simp only [List.nil_append]
          have hh : (simDrive q b tab s0).halted
              (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
                (Tape.mk (none :: a0 :: Z') (x :: M))) = false :=
            simDrive_halted_embN q b tab s0 _ _
          rw [simRun_one _ _ _ hh]
          rw [simDrive_stepConfig_ph0_nonblank q b tab s0 m c hm hc x hx
            (none :: a0 :: Z') M]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          exact embN_val_ge q b _
      | 2 =>
          simp only [List.nil_append]
          have hh : (simDrive q b tab s0).halted
              (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
                (Tape.mk (none :: a0 :: Z') (x :: M))) = false :=
            simDrive_halted_embN q b tab s0 _ _
          have hh1 : (simDrive q b tab s0).halted
              (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
                (Tape.mk (a0 :: Z') (none :: x :: M))) = false :=
            simDrive_halted_embN q b tab s0 _ _
          show stateCount q b ≤ ((simDrive q b tab s0).run (1 + 1)
            (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
              (Tape.mk (none :: a0 :: Z') (x :: M)))).state.val
          rw [DTM.run_succ_of_not_halted _ 1 _ hh,
            simDrive_stepConfig_ph0_nonblank q b tab s0 m c hm hc x hx
              (none :: a0 :: Z') M]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          rw [simRun_one _ _ _ hh1,
            simDrive_stepConfig_ph0_blank q b tab s0 m c hm hc (a0 :: Z') (x :: M)]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail,
            List.reverse_nil, List.nil_append]
          exact embN_val_ge q b _
  | x, y :: ys, hx, hL0, a0, Z', M, i, hi => by
      have hy : y ≠ none := hL0 y (by simp)
      have hys : ∀ z ∈ ys, z ≠ none := fun z hz => hL0 z (by simp [hz])
      have hlen : (y :: ys).length = ys.length + 1 := rfl
      rw [hlen] at hi
      match i with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m c 0 0 hm hc (by decide) (by decide))).val
          exact embN_val_ge q b _
      | i + 1 =>
          simp only [List.cons_append]
          have hh : (simDrive q b tab s0).halted
              (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
                (Tape.mk (y :: (ys ++ none :: a0 :: Z')) (x :: M))) = false :=
            simDrive_halted_embN q b tab s0 _ _
          rw [DTM.run_succ_of_not_halted _ i _ hh]
          rw [simDrive_stepConfig_ph0_nonblank q b tab s0 m c hm hc x hx
            (y :: (ys ++ none :: a0 :: Z')) M]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          exact simDrive_rewind_nav q b tab s0 m c hm hc y ys hy hys a0 Z' (x :: M) i
            (by omega)

/-- **跳零段全程在导航层**：`simDrive_skip` 运行中每一步都不小于 `stateCount`。
    The whole zero-skip segment stays in the navigation layer. -/
theorem simDrive_skip_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (z : Nat) (a0 : Sym) (W' R0 : List Sym) (i : Nat), i ≤ z + 1 →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
          (Tape.mk (List.replicate z (some false) ++ a0 :: W')
            ((some false) :: R0)))).state.val
  | 0, a0, W', R0, i, hi => by
      match i with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m c 0 1 hm hc (by decide) (by decide))).val
          exact embN_val_ge q b _
      | 1 =>
          rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph1_false q b tab s0 m c hm hc _ _]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          exact embN_val_ge q b _
  | z + 1, a0, W', R0, i, hi => by
      match i with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m c 0 1 hm hc (by decide) (by decide))).val
          exact embN_val_ge q b _
      | i' + 1 =>
          simp only [List.replicate_succ, List.cons_append]
          rw [DTM.run_succ_of_not_halted _ i' _
            (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph1_false q b tab s0 m c hm hc _ _]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail,
            List.cons_append]
          exact simDrive_skip_nav q b tab s0 m c hm hc z a0 W' ((some false) :: R0) i'
            (by omega)

/-- **计数段全程在导航层**：`simDrive_count2` 运行中每一步都不小于 `stateCount`。
    The whole count segment stays in the navigation layer. -/
theorem simDrive_count2_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m K : Nat) (hm : m < q) (hK : K < 2 ^ b) :
    ∀ (i k : Nat) (he : K = i + k + 1) (hi : i < 2 ^ b)
      (x : Sym) (X' R0 : List Sym), x ≠ some true →
      ∀ (j : Nat), j ≤ k + 1 →
        stateCount q b ≤ ((simDrive q b tab s0).run j
          (Config.mk (embN (codeState q b m i 0 2 hm hi (by decide) (by decide)))
            (Tape.mk (List.replicate k (some true) ++ x :: X')
              (some true :: R0)))).state.val
  | i, 0, he, hi, x, X', R0, hx, j, hj => by
      match j with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m i 0 2 hm hi (by decide) (by decide))).val
          exact embN_val_ge q b _
      | 1 =>
          have hi1 : i + 1 < 2 ^ b := by omega
          rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph2_true q b tab s0 m i hm hi hi1
            (List.replicate 0 (some true) ++ x :: X') R0]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
            List.tail, List.replicate_zero, List.nil_append]
          exact embN_val_ge q b _
  | i, k + 1, he, hi, x, X', R0, hx, j, hj => by
      match j with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m i 0 2 hm hi (by decide) (by decide))).val
          exact embN_val_ge q b _
      | j' + 1 =>
          have hi1 : i + 1 < 2 ^ b := by omega
          simp only [List.replicate_succ, List.cons_append]
          rw [DTM.run_succ_of_not_halted _ j' _
            (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph2_true q b tab s0 m i hm hi hi1 _ _]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail,
            List.cons_append]
          exact simDrive_count2_nav q b tab s0 m K hm hK (i + 1) k (by omega)
            hi1 x X' ((some true) :: R0) hx j' (by omega)

/-- **擦除段全程在导航层**：`simDrive_erase` 运行中每一步都不小于 `stateCount`。
    The whole erase segment stays in the navigation layer. -/
theorem simDrive_erase_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (D : List Sym), (∀ x ∈ D, x ≠ none) →
      ∀ (a0 : Sym) (W' R2 : List Sym) (j : Nat), j ≤ D.length + 1 →
        stateCount q b ≤ ((simDrive q b tab s0).run j
          (Config.mk (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
            (Tape.mk (a0 :: W') (D ++ none :: R2)))).state.val
  | [], _, a0, W', R2, j, hj => by
      match j with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m c 0 3 hm hc (by decide) (by decide))).val
          exact embN_val_ge q b _
      | 1 =>
          simp only [List.nil_append]
          rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph3_blank q b tab s0 m c hm hc _ _]
          simp only [Tape.write, Tape.move, Tape.moveRight, Tape.read, List.tail]
          exact embN_val_ge q b _
  | d :: D', hD, a0, W', R2, j, hj => by
      have hd : d ≠ none := hD d (by simp)
      have hD' : ∀ x ∈ D', x ≠ none := fun x hx => hD x (by simp [hx])
      have hlen : (d :: D').length = D'.length + 1 := rfl
      rw [hlen] at hj
      match j with
      | 0 =>
          show stateCount q b ≤
            (embN (codeState q b m c 0 3 hm hc (by decide) (by decide))).val
          exact embN_val_ge q b _
      | j' + 1 =>
          simp only [List.cons_append]
          rw [DTM.run_succ_of_not_halted _ j' _
            (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph3_nonblank q b tab s0 m c hm hc d hd _ _]
          simp only [Tape.write, Tape.move, Tape.moveRight, Tape.read, List.tail]
          exact simDrive_erase_nav q b tab s0 m c hm hc D' hD' (some false) (a0 :: W')
            R2 j' (by omega)

/-- **找标记段的一格三连步**：相位 4→5→6（读 `w`），三步内每一步都在导航层。
    One three-step cell group of the seek segment stays in the navigation layer. -/
theorem simDrive_seek3_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (b0 b1 w : Sym) (tail L : List Sym) (hw : w = some true ∨ w ≠ some true) :
    ∀ (j : Nat), j ≤ 3 →
      stateCount q b ≤ ((simDrive q b tab s0).run j
        (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
          (Tape.mk L (b0 :: b1 :: w :: tail)))).state.val := by
  intro j hj
  match j with
  | 0 => exact embN_val_ge q b _
  | 1 =>
      rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
      rw [simDrive_stepConfig_ph4 q b tab s0 m c hm hc b0 L (b1 :: w :: tail)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      exact embN_val_ge q b _
  | 2 =>
      show stateCount q b ≤ ((simDrive q b tab s0).run (1 + 1)
        (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
          (Tape.mk L (b0 :: b1 :: w :: tail)))).state.val
      rw [DTM.run_succ_of_not_halted _ 1 _ (simDrive_halted_embN q b tab s0 _ _)]
      rw [simDrive_stepConfig_ph4 q b tab s0 m c hm hc b0 L (b1 :: w :: tail)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
      rw [simDrive_stepConfig_ph5 q b tab s0 m c hm hc b1 (b0 :: L) (w :: tail)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      exact embN_val_ge q b _
  | 3 =>
      show stateCount q b ≤ ((simDrive q b tab s0).run (2 + 1)
        (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
          (Tape.mk L (b0 :: b1 :: w :: tail)))).state.val
      rw [DTM.run_succ_of_not_halted _ 2 _ (simDrive_halted_embN q b tab s0 _ _)]
      rw [simDrive_stepConfig_ph4 q b tab s0 m c hm hc b0 L (b1 :: w :: tail)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      show stateCount q b ≤ ((simDrive q b tab s0).run (1 + 1)
        (Config.mk (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)))
          (Tape.mk (b0 :: L) (b1 :: w :: tail)))).state.val
      rw [DTM.run_succ_of_not_halted _ 1 _ (simDrive_halted_embN q b tab s0 _ _)]
      rw [simDrive_stepConfig_ph5 q b tab s0 m c hm hc b1 (b0 :: L) (w :: tail)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
      rcases hw with rfl | hw
      · rw [simDrive_stepConfig_ph6_true q b tab s0 m c hm hc _ _]
        simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
          List.tail]
        exact embN_val_ge q b _
      · rw [simDrive_stepConfig_ph6_other q b tab s0 m c hm hc w hw _ _]
        simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
          List.tail]
        exact embN_val_ge q b _

/-- **找标记段全程在导航层**：`simDrive_seek` 运行中每一步都不小于 `stateCount`。
    The whole seek segment stays in the navigation layer. -/
theorem simDrive_seek_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) →
      ∀ (s : Sym) (rest : List (Sym × Bool)) (L : List Sym) (j : Nat),
        j ≤ 3 * cs.length + 3 →
        stateCount q b ≤ ((simDrive q b tab s0).run j
          (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
            (Tape.mk L (codeCells cs ++ cellCode (s, true) ++ codeCells rest)))).state.val
  | [], _, s, rest, L, j, hj => by
      obtain ⟨b0, b1, hs⟩ : ∃ b0 b1 : Sym, symCode s = [b0, b1] := by
        cases s with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hcell : cellCode (s, true) = b0 :: b1 :: some true :: [] := by
        simp [cellCode, hs]
      simp only [hcell, List.cons_append, List.nil_append, codeCells,
        List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.zero_add] at hj ⊢
      exact simDrive_seek3_nav q b tab s0 m c hm hc b0 b1 (some true)
        (List.flatMap cellCode rest) L (Or.inl rfl) j (by omega)
  | p :: ps, hmark, s, rest, L, j, hj => by
      obtain ⟨b0, b1, hs⟩ : ∃ b0 b1 : Sym, symCode p.1 = [b0, b1] := by
        cases p.1 with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hp : p.2 = false := hmark p (by simp)
      have hcell : cellCode p = b0 :: b1 :: some false :: [] := by
        simp [cellCode, hs, hp]
      have hps : ∀ q ∈ ps, q.2 = false := fun q hq => hmark q (by simp [hq])
      have hcs : codeCells (p :: ps) = cellCode p ++ codeCells ps := by
        simp [codeCells]
      simp only [hcs, hcell, List.cons_append, List.nil_append,
        List.length_cons, Nat.mul_add, Nat.mul_one] at hj ⊢
      match j with
      | 0 => exact embN_val_ge q b _
      | 1 =>
          exact simDrive_seek3_nav q b tab s0 m c hm hc b0 b1 (some false) _ L
            (Or.inr (by decide)) 1 (by omega)
      | 2 =>
          exact simDrive_seek3_nav q b tab s0 m c hm hc b0 b1 (some false) _ L
            (Or.inr (by decide)) 2 (by omega)
      | j' + 3 =>
          show stateCount q b ≤ ((simDrive q b tab s0).run ((j' + 2) + 1)
            (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
              (Tape.mk L (b0 :: b1 :: some false ::
                (codeCells ps ++ cellCode (s, true) ++ codeCells rest))))).state.val
          rw [DTM.run_succ_of_not_halted _ (j' + 2) _
            (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph4 q b tab s0 m c hm hc b0 L
            (b1 :: some false :: (codeCells ps ++ cellCode (s, true) ++ codeCells rest))]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
            List.tail]
          show stateCount q b ≤ ((simDrive q b tab s0).run ((j' + 1) + 1)
            (Config.mk (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)))
              (Tape.mk (b0 :: L) (b1 :: some false ::
                (codeCells ps ++ cellCode (s, true) ++ codeCells rest))))).state.val
          rw [DTM.run_succ_of_not_halted _ (j' + 1) _
            (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph5 q b tab s0 m c hm hc b1 (b0 :: L)
            (some false :: (codeCells ps ++ cellCode (s, true) ++ codeCells rest))]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
            List.tail]
          show stateCount q b ≤ ((simDrive q b tab s0).run ((j' + 0) + 1)
            (Config.mk (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)))
              (Tape.mk (b1 :: b0 :: L) (some false ::
                (codeCells ps ++ cellCode (s, true) ++ codeCells rest))))).state.val
          rw [DTM.run_succ_of_not_halted _ (j' + 0) _
            (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph6_other q b tab s0 m c hm hc (some false)
            (by decide) (b1 :: b0 :: L)
            (codeCells ps ++ cellCode (s, true) ++ codeCells rest)]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
            List.tail]
          rw [Nat.add_zero]
          exact simDrive_seek_nav q b tab s0 m c hm hc ps hps s rest
            (some false :: b1 :: b0 :: L) j' (by omega)

/-- 两段拼接：若前段 `L1` 步与后段 `L2` 步各自全程在导航层，则整段全程在导航层。
    Concatenation of two navigation-layer runs. -/
theorem nav_concat (q : Nat) (M : DTM q) (S : Nat)
    (L1 L2 : Nat) (c : Config q)
    (h1 : ∀ i, i ≤ L1 → S ≤ (M.run i c).state.val)
    (h2 : ∀ i, i ≤ L2 → S ≤ (M.run i (M.run L1 c)).state.val) :
    ∀ i, i ≤ L1 + L2 → S ≤ (M.run i c).state.val := by
  intro i hi
  rcases Nat.lt_or_ge L1 i with hlt | hge
  · have hi' : i = L1 + (i - L1) := by omega
    rw [hi', DTM.run_add]
    exact h2 (i - L1) (by omega)
  · exact h1 i hge

/-- **整轮前段全程在导航层**（原地 / stay）：模拟 14 步之后，回扫 + 跳零 + 计数段
    的每一步都在导航层。
    The pre-erase part of a full round (stay) stays in the navigation layer. -/
theorem simDrive_roundNavNav_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    ∀ i, 14 ≤ i →
      i ≤ (14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)) + (z + k + 3) →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val := by
  intro i hi14 hib
  -- 取 r = i - 14，把整段拆成「14 步模拟」+「导航段」
  have hi : i = 14 + (i - 14) := by omega
  rw [hi, DTM.run_add]
  rw [simDrive_run14_stay q b tab s0 m c hm hc x
    (none :: (some false) :: (List.replicate z (some false)
      ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))
    m' s' hx h]
  have hL : ∀ y ∈ (codeFst s' :: List.reverse (codeCells x.pre)), y ≠ none := by
    intro y hy
    rcases (List.mem_cons.mp hy) with hy | hy
    · exact hy ▸ codeFst_ne_none s'
    · have hy' := List.mem_reverse.mp hy
      exact codeCells_ne_none x.pre y hy'
  -- 第一段：回扫
  rcases Nat.lt_or_ge (i - 14)
      ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2 + 1) with hlt | hge
  · exact simDrive_rewind_nav q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
      (codeSnd s') (codeFst s' :: List.reverse (codeCells x.pre)) (codeSnd_ne_none s')
      hL (some false) (List.replicate z (some false) ++ (some true
        :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      (some true :: codeCells x.post) (i - 14) (by omega)
  · -- 第二段：回扫之后，先补出回扫终点
    have hr : i - 14 = ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
        + (i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)) := by
      omega
    rw [hr, DTM.run_add]
    -- 纸带形态桥接：`a :: (l ++ m)` 与 `(a :: l) ++ m` 定义相等
    rw [show Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
          (by decide) (by decide)))
        (Tape.mk (codeFst s' :: (List.reverse (codeCells x.pre)
            ++ (none :: (some false) :: (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))))
          (codeSnd s' :: some true :: codeCells x.post))
      = Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
          (by decide) (by decide)))
        (Tape.mk ((codeFst s' :: List.reverse (codeCells x.pre))
            ++ (none :: (some false) :: (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))
          (codeSnd s' :: some true :: codeCells x.post)) from rfl]
    rw [simDrive_rewind q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
      (codeSnd s') (codeFst s' :: List.reverse (codeCells x.pre)) (codeSnd_ne_none s')
      hL (some false) (List.replicate z (some false) ++ (some true
        :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      (some true :: codeCells x.post)]
    simp only [List.cons_append]
    -- 跳零 + 一步 + 计数
    rcases Nat.lt_or_ge (i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2))
        (z + 1 + 1) with hlt2 | hge2
    · exact simDrive_skip_nav q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b) z
        (some true) (List.replicate (k + 1) (some true) ++ (xc :: X'))
        (none :: ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
          ++ (codeSnd s' :: some true :: codeCells x.post))) _ (by omega)
    · have hr2 : i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
          = (z + 1) + (i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
            - (z + 1)) := by omega
      rw [hr2, DTM.run_add]
      rw [simDrive_skip q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b) z (some true)
        (List.replicate (k + 1) (some true) ++ (xc :: X'))
        (none :: ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
          ++ (codeSnd s' :: some true :: codeCells x.post)))]
      simp only [List.cons_append]
      -- 此处还剩：1 步相位 1→2 + 计数段
      rcases Nat.lt_or_ge
          (i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) - (z + 1)) 2
          with hlt3 | hge3
      · -- 0 或 1 步：相位 1 一步到相位 2，均在导航层
        rcases Nat.lt_or_ge
            (i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
              - (z + 1)) 1 with hlt0 | hge0
        · have hzero : i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
              - (z + 1) = 0 := by omega
          rw [hzero, simRun_zero]
          exact embN_val_ge q b
            (codeState q b m'.val 0 0 1 m'.isLt (Nat.two_pow_pos b) (by decide) (by decide))
        · have hone : i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
              - (z + 1) = 1 := by omega
          rw [hone]
          rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph1_true q b tab s0 m'.val 0 m'.isLt
            (Nat.two_pow_pos b) (by omega) _ _]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          exact embN_val_ge q b _
      · have hr3 : i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
            - (z + 1) = 1 + (i - 14 - ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
              - (z + 1) - 1) := by omega
        rw [hr3, DTM.run_add]
        rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
        rw [simDrive_stepConfig_ph1_true q b tab s0 m'.val 0 m'.isLt
          (Nat.two_pow_pos b) (by omega) _ _]
        simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
        exact simDrive_count2_nav q b tab s0 m'.val K m'.isLt hK 1 k (by omega)
          (by omega) xc X'
          (some true :: (some false :: (List.replicate z (some false)
            ++ (none :: ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
              ++ codeSnd s' :: some true :: codeCells x.post))))) hxc _
          (by omega)

/-- **擦除块全程在导航层**：子相位 2 → 3 一步 + 擦除段，全程导航层。
    The erase block stays in the navigation layer. -/
theorem simDrive_ph2Erase_nav (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m K : Nat) (hm : m < q) (hK : K < 2 ^ b) :
    ∀ (z k : Nat) (xc : Sym) (X' R2' : List Sym), xc ≠ some true →
      ∀ j, j ≤ 1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1) →
        stateCount q b ≤ ((simDrive q b tab s0).run j
          (Config.mk (embN (codeState q b m K 0 2 hm hK (by decide) (by decide)))
            (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
              ++ (some true :: (List.replicate (z + 1) (some false)
                ++ (none :: R2')))))))).state.val := by
  intro z k xc X' R2' hxc j hj
  rcases Nat.lt_or_ge j 2 with hlt | hge
  · rcases Nat.lt_or_ge j 1 with h0 | h1
    · have hz : j = 0 := by omega
      rw [hz, simRun_zero]
      exact embN_val_ge q b _
    · have hone : j = 1 := by omega
      rw [hone, simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
      rw [simDrive_stepConfig_ph2_other q b tab s0 m K hm hK xc hxc _ _]
      simp only [Tape.write, Tape.move, Tape.moveRight, Tape.read, List.tail]
      exact embN_val_ge q b _
  · have hsplit : j = 1 + (j - 1) := by omega
    rw [hsplit, DTM.run_add]
    rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
    rw [simDrive_stepConfig_ph2_other q b tab s0 m K hm hK xc hxc _ _]
    simp only [Tape.write, Tape.move, Tape.moveRight, Tape.read, List.tail]
    -- 把纸带规范成 `D ++ none :: R2'`（D = 已读块）
    rw [show Config.mk (embN (codeState q b m K 0 3 hm hK (by decide) (by decide)))
          (Tape.mk (xc :: X') (List.replicate (k + 1) (some true)
            ++ (some true :: (List.replicate (z + 1) (some false)
              ++ (none :: R2')))))
        = Config.mk (embN (codeState q b m K 0 3 hm hK (by decide) (by decide)))
          (Tape.mk (xc :: X') ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))) ++ none :: R2'))
        from by
          refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
          simp only [List.cons_append, List.append_assoc]]
    exact simDrive_erase_nav q b tab s0 m K hm hK
      (List.replicate (k + 1) (some true)
        ++ (some true :: List.replicate (z + 1) (some false)))
      (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact replicate_ne_none (k + 1) (some true) (by decide) y hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact (by decide)
          · exact replicate_ne_none (z + 1) (some false) (by decide) y hy)
      xc X' R2' (j - 1) (by omega)

/-- **完整一轮全程在导航层**（原地 / stay）：14 步模拟之后、轮末（最后一步回模拟层）之前，
    每一步状态都在导航层。
    Every state of a full round (stay) after the 14 simulation steps, except the very
    last step back to the simulation layer, is in the navigation layer. -/
theorem simDrive_roundFullNav_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    ∀ i, 14 ≤ i →
      i < ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * x.pre.length + 3 + 1))) →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val := by
  intro i hi14 hib
  -- 分支 1：仍在「14 步 + 回扫 + 跳零 + 计数」段内
  rcases Nat.lt_or_ge i
      (((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)) + (z + k + 3)) + 1)
      with h1 | h1
  · exact simDrive_roundNavNav_stay q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc
      m' s' hx h i hi14 (by omega)
  · -- 分支 2：从计数端点继续（擦除块 + 找标记块）
    have hB1 : i = ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2))
        + (z + k + 3))
        + (i - ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2))
          + (z + k + 3))) := by omega
    rw [hB1, DTM.run_add]
    rw [simDrive_roundNavCount_stay q b tab s0 m c hm hc x z k K hK hK2 xc X'
      hxc m' s' hx h]
    -- 纸带桥接：`(none :: L0.reverse) ++ m` → `none :: (L0.reverse ++ m)`
    rw [show Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK
          (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ ((none :: (codeFst s' :: List.reverse (codeCells x.pre)).reverse)
              ++ (codeSnd s' :: some true :: codeCells x.post)))))))
      = Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
              ++ (codeSnd s' :: some true :: codeCells x.post))))))))
      from by
        refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
        simp only [List.cons_append]]
    rcases Nat.lt_or_ge
        (i - ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)) + (z + k + 3)))
        ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1)) + 1)
        with h2 | h2
    · exact simDrive_ph2Erase_nav q b tab s0 m'.val K m'.isLt hK z k xc X'
        ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
          ++ (codeSnd s' :: some true :: codeCells x.post)) hxc _ (by omega)
    · -- 分支 3：擦除块之后，找标记段
      have hB2 : (i - ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2))
            + (z + k + 3)))
          = (1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
            + ((i - ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2))
                + (z + k + 3)))
              - (1 + ((List.replicate (k + 1) (some true)
                ++ (some true :: List.replicate (z + 1) (some false))).length + 1))) := by
        omega
      rw [hB2, DTM.run_add]
      rw [simDrive_ph2Erase q b tab s0 m'.val K m'.isLt hK z k xc X'
        ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
          ++ (codeSnd s' :: some true :: codeCells x.post)) hxc]
      -- 纸带桥接：擦除终点右串 → 找标记段起点形式
      rw [show Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK
            (by decide) (by decide)))
          (Tape.mk (none :: List.replicate ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length)
              (some false) ++ xc :: X')
            ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
              ++ (codeSnd s' :: some true :: codeCells x.post)))
        = Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK (by decide) (by decide)))
          (Tape.mk (none :: List.replicate ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length)
              (some false) ++ xc :: X')
            (codeCells x.pre ++ cellCode (s', true) ++ codeCells x.post))
        from by
          refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
          simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc,
            List.cons_append, List.nil_append, cellCode, symCode_eq, if_true]]
      exact simDrive_seek_nav q b tab s0 m'.val K m'.isLt hK x.pre hpre s' x.post
        (none :: List.replicate ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length)
            (some false) ++ xc :: X') _ (by omega)


/-- **整轮前段全程在导航层**（右移 / right）：模拟 14 步之后，回扫 + 跳零 + 计数段
    的每一步都在导航层。
    The pre-erase part of a full round (stay) stays in the navigation layer. -/
theorem simDrive_roundNavNav_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post') (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    ∀ i, 14 ≤ i →
      i ≤ (14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)) + (z + k + 3) →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val := by
  intro i hi14 hib
  -- 取 r = i - 14，把整段拆成「14 步模拟」+「导航段」
  have hi : i = 14 + (i - 14) := by omega
  rw [hi, DTM.run_add]
  rw [simDrive_run14_right q b tab s0 m c hm hc x
    (none :: (some false) :: (List.replicate z (some false)
      ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))
    p post' hp hpost m' s' hx h]
  have hL : ∀ y ∈ (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))), y ≠ none := by
    intro y hy
    rcases (List.mem_cons.mp hy) with hy | hy
    · exact hy ▸ codeFst_ne_none p.1
    · have hy' := List.mem_reverse.mp hy
      exact codeCells_ne_none (x.pre ++ [(s', false)]) y hy'
  -- 第一段：回扫
  rcases Nat.lt_or_ge (i - 14)
      ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2 + 1) with hlt | hge
  · exact simDrive_rewind_nav q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
      (codeSnd p.1) (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))) (codeSnd_ne_none p.1)
      hL (some false) (List.replicate z (some false) ++ (some true
        :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      (some true :: codeCells post') (i - 14) (by omega)
  · -- 第二段：回扫之后，先补出回扫终点
    have hr : i - 14 = ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
        + (i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)) := by
      omega
    rw [hr, DTM.run_add]
    -- 纸带形态桥接：`a :: (l ++ m)` 与 `(a :: l) ++ m` 定义相等
    rw [show Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
          (by decide) (by decide)))
        (Tape.mk (codeFst p.1 :: (List.reverse (codeCells (x.pre ++ [(s', false)]))
            ++ (none :: (some false) :: (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))))
          (codeSnd p.1 :: some true :: codeCells post'))
      = Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
          (by decide) (by decide)))
        (Tape.mk ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)])))
            ++ (none :: (some false) :: (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))
          (codeSnd p.1 :: some true :: codeCells post')) from rfl]
    rw [simDrive_rewind q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
      (codeSnd p.1) (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))) (codeSnd_ne_none p.1)
      hL (some false) (List.replicate z (some false) ++ (some true
        :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      (some true :: codeCells post')]
    simp only [List.cons_append]
    -- 跳零 + 一步 + 计数
    rcases Nat.lt_or_ge (i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
        (z + 1 + 1) with hlt2 | hge2
    · exact simDrive_skip_nav q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b) z
        (some true) (List.replicate (k + 1) (some true) ++ (xc :: X'))
        (none :: ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
          ++ (codeSnd p.1 :: some true :: codeCells post'))) _ (by omega)
    · have hr2 : i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
          = (z + 1) + (i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
            - (z + 1)) := by omega
      rw [hr2, DTM.run_add]
      rw [simDrive_skip q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b) z (some true)
        (List.replicate (k + 1) (some true) ++ (xc :: X'))
        (none :: ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
          ++ (codeSnd p.1 :: some true :: codeCells post')))]
      simp only [List.cons_append]
      -- 此处还剩：1 步相位 1→2 + 计数段
      rcases Nat.lt_or_ge
          (i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) - (z + 1)) 2
          with hlt3 | hge3
      · -- 0 或 1 步：相位 1 一步到相位 2，均在导航层
        rcases Nat.lt_or_ge
            (i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
              - (z + 1)) 1 with hlt0 | hge0
        · have hzero : i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
              - (z + 1) = 0 := by omega
          rw [hzero, simRun_zero]
          exact embN_val_ge q b
            (codeState q b m'.val 0 0 1 m'.isLt (Nat.two_pow_pos b) (by decide) (by decide))
        · have hone : i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
              - (z + 1) = 1 := by omega
          rw [hone]
          rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph1_true q b tab s0 m'.val 0 m'.isLt
            (Nat.two_pow_pos b) (by omega) _ _]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          exact embN_val_ge q b _
      · have hr3 : i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
            - (z + 1) = 1 + (i - 14 - ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
              - (z + 1) - 1) := by omega
        rw [hr3, DTM.run_add]
        rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
        rw [simDrive_stepConfig_ph1_true q b tab s0 m'.val 0 m'.isLt
          (Nat.two_pow_pos b) (by omega) _ _]
        simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
        exact simDrive_count2_nav q b tab s0 m'.val K m'.isLt hK 1 k (by omega)
          (by omega) xc X'
          (some true :: (some false :: (List.replicate z (some false)
            ++ (none :: ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
              ++ codeSnd p.1 :: some true :: codeCells post'))))) hxc _
          (by omega)


/-- **完整一轮全程在导航层**（右移 / right）：14 步模拟之后、轮末（最后一步回模拟层）之前，
    每一步状态都在导航层。
    Every state of a full round (stay) after the 14 simulation steps, except the very
    last step back to the simulation layer, is in the navigation layer. -/
theorem simDrive_roundFullNav_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    ∀ i, 14 ≤ i →
      i < ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * (x.pre ++ [(s', false)]).length + 3 + 1))) →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val := by
  intro i hi14 hib
  -- 分支 1：仍在「14 步 + 回扫 + 跳零 + 计数」段内
  rcases Nat.lt_or_ge i
      (((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)) + (z + k + 3)) + 1)
      with h1 | h1
  · exact simDrive_roundNavNav_right q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc
      p post' hp hpost m' s' hx h i hi14 (by omega)
  · -- 分支 2：从计数端点继续（擦除块 + 找标记块）
    have hB1 : i = ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
        + (z + k + 3))
        + (i - ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
          + (z + k + 3))) := by omega
    rw [hB1, DTM.run_add]
    rw [simDrive_roundNavCount_right q b tab s0 m c hm hc x z k K hK hK2 xc X'
      hxc p post' hp hpost m' s' hx h]
    -- 纸带桥接：`(none :: L0.reverse) ++ m` → `none :: (L0.reverse ++ m)`
    rw [show Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK
          (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ ((none :: (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse)
              ++ (codeSnd p.1 :: some true :: codeCells post')))))))
      = Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
              ++ (codeSnd p.1 :: some true :: codeCells post'))))))))
      from by
        refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
        simp only [List.cons_append]]
    rcases Nat.lt_or_ge
        (i - ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)) + (z + k + 3)))
        ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1)) + 1)
        with h2 | h2
    · exact simDrive_ph2Erase_nav q b tab s0 m'.val K m'.isLt hK z k xc X'
        ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
          ++ (codeSnd p.1 :: some true :: codeCells post')) hxc _ (by omega)
    · -- 分支 3：擦除块之后，找标记段
      have hB2 : (i - ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
            + (z + k + 3)))
          = (1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
            + ((i - ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
                + (z + k + 3)))
              - (1 + ((List.replicate (k + 1) (some true)
                ++ (some true :: List.replicate (z + 1) (some false))).length + 1))) := by
        omega
      rw [hB2, DTM.run_add]
      rw [simDrive_ph2Erase q b tab s0 m'.val K m'.isLt hK z k xc X'
        ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
          ++ (codeSnd p.1 :: some true :: codeCells post')) hxc]
      -- 纸带桥接：擦除终点右串 → 找标记段起点形式
      rw [show Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK
            (by decide) (by decide)))
          (Tape.mk (none :: List.replicate ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length)
              (some false) ++ xc :: X')
            ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
              ++ (codeSnd p.1 :: some true :: codeCells post')))
        = Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK (by decide) (by decide)))
          (Tape.mk (none :: List.replicate ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length)
              (some false) ++ xc :: X')
            (codeCells (x.pre ++ [(s', false)]) ++ cellCode (p.1, true) ++ codeCells post'))
        from by
          refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
          simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc,
            List.cons_append, List.nil_append, cellCode, symCode_eq, if_true]]
      have hpreR : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
        intro p0 hp0
        rcases List.mem_append.mp hp0 with hp0' | hp0'
        · exact hpre p0 hp0'
        · rw [List.mem_singleton] at hp0'
          rw [hp0']
      exact simDrive_seek_nav q b tab s0 m'.val K m'.isLt hK (x.pre ++ [(s', false)]) hpreR p.1 post'
        (none :: List.replicate ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length)
            (some false) ++ xc :: X') _ (by omega)


/-- **整轮前段全程在导航层**（左移 / left）：模拟 14 步之后，回扫 + 跳零 + 计数段
    的每一步都在导航层。
    The pre-erase part of a full round (stay) stays in the navigation layer. -/
theorem simDrive_roundNavNav_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprel : x.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    ∀ i, 14 ≤ i →
      i ≤ (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) + (z + k + 3) →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val := by
  intro i hi14 hib
  -- 取 r = i - 14，把整段拆成「14 步模拟」+「导航段」
  have hi : i = 14 + (i - 14) := by omega
  rw [hi, DTM.run_add]
  rw [simDrive_run14_left q b tab s0 m c hm hc x
    (none :: (some false) :: (List.replicate z (some false)
      ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))
    cq pre' hq hprel m' s' hx h]
  have hL : ∀ y ∈ (codeFst cq.1 :: List.reverse (codeCells pre')), y ≠ none := by
    intro y hy
    rcases (List.mem_cons.mp hy) with hy | hy
    · exact hy ▸ codeFst_ne_none cq.1
    · have hy' := List.mem_reverse.mp hy
      exact codeCells_ne_none pre' y hy'
  -- 第一段：回扫
  rcases Nat.lt_or_ge (i - 14)
      ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2 + 1) with hlt | hge
  · exact simDrive_rewind_nav q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
      (codeSnd cq.1) (codeFst cq.1 :: List.reverse (codeCells pre')) (codeSnd_ne_none cq.1)
      hL (some false) (List.replicate z (some false) ++ (some true
        :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      (some true :: codeCells ((s', false) :: x.post)) (i - 14) (by omega)
  · -- 第二段：回扫之后，先补出回扫终点
    have hr : i - 14 = ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
        + (i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) := by
      omega
    rw [hr, DTM.run_add]
    -- 纸带形态桥接：`a :: (l ++ m)` 与 `(a :: l) ++ m` 定义相等
    rw [show Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
          (by decide) (by decide)))
        (Tape.mk (codeFst cq.1 :: (List.reverse (codeCells pre')
            ++ (none :: (some false) :: (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))))
          (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)))
      = Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
          (by decide) (by decide)))
        (Tape.mk ((codeFst cq.1 :: List.reverse (codeCells pre'))
            ++ (none :: (some false) :: (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))
          (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))) from rfl]
    rw [simDrive_rewind q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
      (codeSnd cq.1) (codeFst cq.1 :: List.reverse (codeCells pre')) (codeSnd_ne_none cq.1)
      hL (some false) (List.replicate z (some false) ++ (some true
        :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      (some true :: codeCells ((s', false) :: x.post))]
    simp only [List.cons_append]
    -- 跳零 + 一步 + 计数
    rcases Nat.lt_or_ge (i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2))
        (z + 1 + 1) with hlt2 | hge2
    · exact simDrive_skip_nav q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b) z
        (some true) (List.replicate (k + 1) (some true) ++ (xc :: X'))
        (none :: ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
          ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)))) _ (by omega)
    · have hr2 : i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
          = (z + 1) + (i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
            - (z + 1)) := by omega
      rw [hr2, DTM.run_add]
      rw [simDrive_skip q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b) z (some true)
        (List.replicate (k + 1) (some true) ++ (xc :: X'))
        (none :: ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
          ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))))]
      simp only [List.cons_append]
      -- 此处还剩：1 步相位 1→2 + 计数段
      rcases Nat.lt_or_ge
          (i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) - (z + 1)) 2
          with hlt3 | hge3
      · -- 0 或 1 步：相位 1 一步到相位 2，均在导航层
        rcases Nat.lt_or_ge
            (i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
              - (z + 1)) 1 with hlt0 | hge0
        · have hzero : i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
              - (z + 1) = 0 := by omega
          rw [hzero, simRun_zero]
          exact embN_val_ge q b
            (codeState q b m'.val 0 0 1 m'.isLt (Nat.two_pow_pos b) (by decide) (by decide))
        · have hone : i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
              - (z + 1) = 1 := by omega
          rw [hone]
          rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
          rw [simDrive_stepConfig_ph1_true q b tab s0 m'.val 0 m'.isLt
            (Nat.two_pow_pos b) (by omega) _ _]
          simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
          exact embN_val_ge q b _
      · have hr3 : i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
            - (z + 1) = 1 + (i - 14 - ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
              - (z + 1) - 1) := by omega
        rw [hr3, DTM.run_add]
        rw [simRun_one _ _ _ (simDrive_halted_embN q b tab s0 _ _)]
        rw [simDrive_stepConfig_ph1_true q b tab s0 m'.val 0 m'.isLt
          (Nat.two_pow_pos b) (by omega) _ _]
        simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail]
        exact simDrive_count2_nav q b tab s0 m'.val K m'.isLt hK 1 k (by omega)
          (by omega) xc X'
          (some true :: (some false :: (List.replicate z (some false)
            ++ (none :: ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
              ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)))))) hxc _
          (by omega)


/-- **完整一轮全程在导航层**（左移 / left）：14 步模拟之后、轮末（最后一步回模拟层）之前，
    每一步状态都在导航层。
    Every state of a full round (stay) after the 14 simulation steps, except the very
    last step back to the simulation layer, is in the navigation layer. -/
theorem simDrive_roundFullNav_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprel : x.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    ∀ i, 14 ≤ i →
      i < ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * pre'.length + 3 + 1))) →
      stateCount q b ≤ ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val := by
  intro i hi14 hib
  -- 分支 1：仍在「14 步 + 回扫 + 跳零 + 计数」段内
  rcases Nat.lt_or_ge i
      (((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) + (z + k + 3)) + 1)
      with h1 | h1
  · exact simDrive_roundNavNav_left q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc
      cq pre' hq hprel m' s' hx h i hi14 (by omega)
  · -- 分支 2：从计数端点继续（擦除块 + 找标记块）
    have hB1 : i = ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2))
        + (z + k + 3))
        + (i - ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2))
          + (z + k + 3))) := by omega
    rw [hB1, DTM.run_add]
    rw [simDrive_roundNavCount_left q b tab s0 m c hm hc x z k K hK hK2 xc X'
      hxc cq pre' hq hprel m' s' hx h]
    -- 纸带桥接：`(none :: L0.reverse) ++ m` → `none :: (L0.reverse ++ m)`
    rw [show Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK
          (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ ((none :: (codeFst cq.1 :: List.reverse (codeCells pre')).reverse)
              ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))))))))
      = Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
              ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)))))))))
      from by
        refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
        simp only [List.cons_append]]
    rcases Nat.lt_or_ge
        (i - ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) + (z + k + 3)))
        ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1)) + 1)
        with h2 | h2
    · exact simDrive_ph2Erase_nav q b tab s0 m'.val K m'.isLt hK z k xc X'
        ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
          ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))) hxc _ (by omega)
    · -- 分支 3：擦除块之后，找标记段
      have hB2 : (i - ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2))
            + (z + k + 3)))
          = (1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
            + ((i - ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2))
                + (z + k + 3)))
              - (1 + ((List.replicate (k + 1) (some true)
                ++ (some true :: List.replicate (z + 1) (some false))).length + 1))) := by
        omega
      rw [hB2, DTM.run_add]
      rw [simDrive_ph2Erase q b tab s0 m'.val K m'.isLt hK z k xc X'
        ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
          ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))) hxc]
      -- 纸带桥接：擦除终点右串 → 找标记段起点形式
      rw [show Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK
            (by decide) (by decide)))
          (Tape.mk (none :: List.replicate ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length)
              (some false) ++ xc :: X')
            ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
              ++ (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))))
        = Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK (by decide) (by decide)))
          (Tape.mk (none :: List.replicate ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length)
              (some false) ++ xc :: X')
            (codeCells pre' ++ cellCode (cq.1, true) ++ codeCells ((s', false) :: x.post)))
        from by
          refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
          simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc,
            List.cons_append, List.nil_append, cellCode, symCode_eq, if_true]]
      have hpreL : ∀ p0 ∈ pre', p0.2 = false := by
        intro p0 hp0
        exact hpre p0 (by rw [hprel]; exact List.mem_append_left _ hp0)
      exact simDrive_seek_nav q b tab s0 m'.val K m'.isLt hK pre' hpreL cq.1 ((s', false) :: x.post)
        (none :: List.replicate ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length)
            (some false) ++ xc :: X') _ (by omega)



/-! ## 轮内 m 分析：任意起步纸带的抬升，再落到整轮起点形态 -/

/-- 驱动层：从模拟层起点（**任意**纸带）出发，前 13 步停在模拟层且与 `simStep` 一致。
    Drive level: from a simulation-layer start with an arbitrary tape, the first 13
    steps stay in the simulation layer and follow `simStep` exactly. -/
theorem simDrive_embS_run13 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (T : Tape) :
    ∀ i, i ≤ 13 →
      (simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) T) =
        Config.mk
          (embS ((simStep q b tab s0).run i
            (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide)) T)).state)
          ((simStep q b tab s0).run i
            (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide)) T)).tape := by
  intro i hi
  refine simDrive_run_embS q b tab s0 i
    (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide)) T) ?_
  intro k hk
  exact simStep_run_ph_ne13 q b tab s0 _
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)) k (by omega)

/-- 驱动层与 `simStep` 的 `m` 一致（任意纸带，前 13 步）。
    The drive's `m` agrees with `simStep`'s on an arbitrary tape, first 13 steps. -/
theorem simDrive_embS_unpackM (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (T : Tape) :
    ∀ i, i ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
          (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) T)).state.val
        = unpackM (2 ^ b) 9 15 ((simStep q b tab s0).run i
            (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide)) T)).state.val := by
  intro i hi
  rw [simDrive_embS_run13 q b tab s0 m c hm hc T i hi]
  rfl

/-- 前 4 步（阶段 ≤ 4）：驱动层模拟状态保持为起点值 `m`（任意纸带）。
    In the first four steps the drive's simulated state stays at `m`. -/
theorem simDrive_embS_unpackM_le (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (T : Tape) :
    ∀ i, i ≤ 4 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) T)).state.val
        = m := by
  intro i hi
  rw [simDrive_embS_unpackM q b tab s0 m c hm hc T i (by omega)]
  exact simStep_run_unpackM_le q b tab s0 _
    m
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
    (codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide)) i hi

/-- 查表命中后（阶段 ≥ 5、步数 ≤ 13）：模拟状态保持为查到的状态 `m'`（纸带 `x.enc L`）。
    After the successful lookup the simulated state stays at the looked-up state. -/
theorem simDrive_embS_unpackM_ge (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (L : List Sym)
    (m' : Fin q) (s' : Sym) (d : Dir)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpick : pick (tab x.state x.cur) c = some (m', s', d)) :
    ∀ i, 5 ≤ i → i ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc L))).state.val
        = m'.val := by
  -- 起点格局与 `simStep_read_run` 的纸带形状一致
  have hread := simStep_read_run q b tab s0 m c hm hc x.cur x.pre x.post L
  rw [tape_eq_enc x L] at hread
  have hp4 : unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run 4
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (x.enc L))).state.val = 4 :=
    simStep_run_ph_lt5 q b tab s0 _
      (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)) 4 (by decide)
  have hlook : lookupRes q b tab ((simStep q b tab s0).run 4
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (x.enc L))).state
      = some (m', s', d) := by
    rw [hread]
    rw [lookupRes_codeState, symOfIdx_symIdx, ← hx]
    exact hpick
  intro i hi5 hi13
  rw [simDrive_embS_unpackM q b tab s0 m c hm hc (x.enc L) i (by omega)]
  exact simStep_run_unpackM_ge q b tab s0 _
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
    hp4 m' s' d hlook i hi5 hi13

/-- **整轮 m 分析 · 前 4 步**（原地 / stay）：模拟层状态保持为轮起点值 `m`。
    Round m analysis, first four steps (stay): the simulated state stays at `m`. -/
theorem simDrive_roundM_le_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k : Nat) (xc : Sym) (X' : List Sym) :
    ∀ i, i ≤ 4 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val
        = m := by
  intro i hi
  exact simDrive_embS_unpackM_le q b tab s0 m c hm hc _ i hi

/-- **整轮 m 分析 · 第 5–13 步**（原地 / stay）：模拟层状态为查表所得 `m'`。
    Round m analysis, steps 5 to 13 (stay): the simulated state is the looked-up `m'`. -/
theorem simDrive_roundM_ge_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k : Nat) (xc : Sym) (X' : List Sym)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    ∀ i, 5 ≤ i → i ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val
        = m'.val := by
  intro i hi5 hi13
  exact simDrive_embS_unpackM_ge q b tab s0 x m c hm hc _ m' s' Dir.stay hx h i hi5 hi13

/-- **整轮 m 分析 · 轮末**（原地 / stay）：整轮结束时模拟状态为查表所得 `m'`。
    Round m analysis, endpoint (stay): at the end of the round the state is `m'`. -/
theorem simDrive_roundM_end_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run
      ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * x.pre.length + 3 + 1)))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true)
            ++ (xc :: X')))))))).state.val
      = m'.val := by
  rw [simDrive_roundFull_stay q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc hpre m' s' hx h]
  exact codeState_unpackM q b m'.val (K - 1) 0 0 m'.isLt (by omega) (by decide) (by decide)

/-- **整轮 m 分析**（原地 / stay）：整轮内若某步仍处于模拟层，则它的模拟状态
    只能是轮起点值 `m`（前 4 步）或查表所得 `m'`（第 5–13 步与轮末）。
    Round m analysis (stay): any simulation-layer state inside the round is either the
    round start `m` (first four steps) or the looked-up `m'` (steps 5–13 and endpoint). -/
theorem simDrive_roundM_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay))
    (i : Nat)
    (hi : i ≤ ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * x.pre.length + 3 + 1))))
    (hlt : ((simDrive q b tab s0).run i
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true)
            ++ (xc :: X')))))))).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val = m
      ∨ unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val = m'.val := by
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · exact Or.inl (simDrive_roundM_le_stay q b tab s0 m c hm hc x z k xc X' i (by omega))
  · rcases Nat.lt_or_ge i 14 with h14 | h14
    · exact Or.inr (simDrive_roundM_ge_stay q b tab s0 m c hm hc x z k xc X' m' s'
        hx h i (by omega) (by omega))
    · rcases Nat.lt_or_ge i
          ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
            + ((1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
              + (3 * x.pre.length + 3 + 1))) with hend | hend
      · -- 14 ≤ i < 轮长：状态在导航层，与模拟层假设矛盾
        have hnav := simDrive_roundFullNav_stay q b tab s0 m c hm hc x z k K hK hK2
          xc X' hxc hpre m' s' hx h i h14 hend
        omega
      · have hie : i = ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)
            + (z + k + 3))
            + ((1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
              + (3 * x.pre.length + 3 + 1))) := by omega
        subst hie
        exact Or.inr (simDrive_roundM_end_stay q b tab s0 m c hm hc x z k K hK hK2
          xc X' hxc hpre m' s' hx h)

/-! ## 轮内 m 分析的 `passStart` 形态（供给分支桥接） -/

/-- `passStart` 起步纸带与整轮起点纸带的同一性（`digitArea` 首格衔接）。
    The `passStart` tape coincides with the round start tape after the digit split. -/
theorem passStart_tape_eq {q : Nat} {x : Reg q} (Z : Nat) (k : Nat) (ks : List Nat)
    (xc : Sym) (X' : List Sym) (htail : digitArea ks = xc :: X') :
    x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))
      = x.enc (none :: (some false) :: (List.replicate Z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))) := by
  have hstart : none :: List.replicate Z (some false) ++ digitArea (k :: ks) =
      none :: some false :: (List.replicate Z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))) := by
    simp only [digitArea, List.cons_append]
    rw [htail, replicate_append_cons]
  exact congrArg (fun L => x.enc L) hstart

/-- **`passStart` 形态的整轮 m 分析**（原地 / stay）：`passStart … Z (k :: ks)` 起步的
    整轮内，若某步仍在模拟层，则它的 `m` 是起点 `m`（前 4 步）或查表所得 `m'`。
    `passStart`-shaped round m analysis (stay). -/
theorem simDrive_passStart_roundM_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat)
    (ks : List Nat) (xc : Sym) (X' : List Sym) (htail : digitArea ks = xc :: X')
    (hk : k + 2 < 2 ^ b) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay))
    (i : Nat) (hi : i ≤ roundCostStay x Z k s')
    (hlt : ((simDrive q b tab s0).run i
      (passStart x m c hm hc Z (k :: ks))).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (passStart x m c hm hc Z (k :: ks))).state.val = m
      ∨ unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (passStart x m c hm hc Z (k :: ks))).state.val = m'.val := by
  have hcfg : passStart x m c hm hc Z (k :: ks)
      = Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    exact passStart_tape_eq Z k ks xc X' htail
  rw [hcfg] at hlt ⊢
  exact simDrive_roundM_stay q b tab s0 m c hm hc x Z k (k + 2) hk rfl
    xc X' hxc hpre m' s' hx h i hi hlt

/-- **查表失败时整轮 `m` 冻结**（原地 / stay）：轮起点查表为空时，整轮任何一步的
    模拟层状态都保持起点值 `m`（阶段 4 一步进入死相位 14，此后状态固定）。
    If the lookup at the round start is empty, `m` stays at the round start value
    for the entire round: phase 4 goes to the dead phase 14 and the state freezes. -/
theorem simDrive_passStart_roundM_none (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat) (ks : List Nat)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = none) :
    ∀ i, unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
      (passStart x m c hm hc Z (k :: ks))).state.val = m := by
  simp only [passStart]
  -- 起点纸带（区域编码）与读符号步
  have hread := simStep_read_run q b tab s0 m c hm hc x.cur x.pre x.post
    (none :: List.replicate Z (some false) ++ digitArea (k :: ks))
  rw [tape_eq_enc x (none :: List.replicate Z (some false) ++ digitArea (k :: ks))] at hread
  -- 第 4 步的状态未停机
  have h4h : (simStep q b tab s0).halted ((simStep q b tab s0).run 4
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))))) = false := by
    rw [hread]
    exact simStep_halted_eq_false q b tab s0 m c (symIdx x.cur) 4 hm hc
      (by have := symIdx_lt x.cur; omega) (by decide) (by decide) _
  -- 第 5 步：查表失败进入阶段 14
  have h5state : (simStep q b tab s0).run 5
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))))
      = Config.mk (codeState q b m c (symIdx x.cur) 14 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))
        (Tape.mk (List.reverse (codeCells x.pre ++ symCode x.cur)
            ++ (none :: List.replicate Z (some false) ++ digitArea (k :: ks)))
          (some true :: codeCells x.post)) := by
    rw [show (5 : Nat) = 4 + 1 from rfl, run_succ_last (simStep q b tab s0) 4 _ h4h,
      hread, ← tape_eq_enc x (none :: List.replicate Z (some false) ++ digitArea (k :: ks))]
    exact simStep_lookupStep_none q b tab s0 m c hm hc x.cur (some true)
      (List.reverse (codeCells x.pre ++ symCode x.cur)
        ++ (none :: List.replicate Z (some false) ++ digitArea (k :: ks)))
      (codeCells x.post) (by rw [← hx]; exact h)
  -- 驱动层第 5 步正是该阶段 14 状态
  have h5 : (simDrive q b tab s0).run 5
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))))
      = Config.mk (embS (codeState q b m c (symIdx x.cur) 14 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide)))
        (Tape.mk (List.reverse (codeCells x.pre ++ symCode x.cur)
            ++ (none :: List.replicate Z (some false) ++ digitArea (k :: ks)))
          (some true :: codeCells x.post)) := by
    rw [simDrive_embS_run13 q b tab s0 m c hm hc
      (x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))) 5 (by decide)]
    exact (congrArg (fun cc : Config (stateCount q b) =>
      Config.mk (embS cc.state) cc.tape) h5state).trans rfl
  intro i
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · exact simDrive_embS_unpackM_le q b tab s0 m c hm hc
      (x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))) i (by omega)
  · have hie : i = 5 + (i - 5) := by omega
    rw [hie, DTM.run_add, h5]
    have hf := simDrive_run_phase14_state q b tab s0
      (Config.mk (embS (codeState q b m c (symIdx x.cur) 14 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide)))
        (Tape.mk (List.reverse (codeCells x.pre ++ symCode x.cur)
            ++ (none :: List.replicate Z (some false) ++ digitArea (k :: ks)))
          (some true :: codeCells x.post)))
      (codeState q b m c (symIdx x.cur) 14 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide)) 0 rfl
      (by simp only [embS, Fin.val_mk, codeState_val,
        unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx x.cur) 14 (by decide)])
      (i - 5)
    rw [show (0 : Nat) + (i - 5) = i - 5 from Nat.zero_add _] at hf
    rw [hf]
    exact codeState_unpackM q b m c (symIdx x.cur) 14 hm hc
      (by have := symIdx_lt x.cur; omega) (by decide)

/-! ## 分支桥接预备：`passRun` 对界限证明的无关性 -/

/-- `passRun` 只依赖界限证明的命题内容：不同证明给出相同结果。
    `passRun` is insensitive to the proof term of the bound hypothesis. -/
theorem passRun_proof_irrel (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb1 hb2 : ∀ k' ∈ L, k' + 2 < 2 ^ b),
      passRun q b tab Z c hc x L hb1 = passRun q b tab Z c hc x L hb2 := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x hb1 hb2
      rfl
  | cons k ks _ =>
      intro Z c hc x hb1 hb2
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb1 hpk]
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb1 m' s' hpk]
          | right =>
              cases hpost : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb1 m' s' hpost hpk]
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb1 m' s' p post' hpost hpk]
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb1 m' s' hrev hpk]
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb1 m' s' cq preRev hrev hpk]

/-- `passStart` 对计数器界限证明不敏感。`passStart` is insensitive to the bound proof. -/
theorem passStart_hc_irrel (q b : Nat) (x : Reg q) (m c : Nat) (hm : m < q)
    (hc1 hc2 : c < 2 ^ b) (Z : Nat) (ks : List Nat) :
    passStart x m c hm hc1 Z ks = passStart x m c hm hc2 Z ks := by
  refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, rfl⟩
  apply Fin.ext
  simp only [embS, Fin.val_mk, codeState_val]

/-- **整轮 m 分析 · 第 5–13 步**（原地 / stay）：模拟层状态为查表所得 `m'`。
    Round m analysis, steps 5 to 13 (stay): the simulated state is the looked-up `m'`. -/
theorem simDrive_roundM_ge (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k : Nat) (xc : Sym) (X' : List Sym)
    (m' : Fin q) (s' : Sym) {d : Dir}
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', d)) :
    ∀ i, 5 ≤ i → i ≤ 13 →
      unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val
        = m'.val := by
  intro i hi5 hi13
  exact simDrive_embS_unpackM_ge q b tab s0 x m c hm hc _ m' s' d hx h i hi5 hi13


/-- **整轮 m 分析 · 轮末**（右移 / right）：整轮结束时模拟状态为查表所得 `m'`。
    Round m analysis, endpoint (right): at the end of the round the state is `m'`. -/
theorem simDrive_roundM_end_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run
      ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * (x.pre ++ [(s', false)]).length + 3 + 1)))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true)
            ++ (xc :: X')))))))).state.val
      = m'.val := by
  rw [simDrive_roundFull_right q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc hpre p post' hp hpost m' s' hx h]
  exact codeState_unpackM q b m'.val (K - 1) 0 0 m'.isLt (by omega) (by decide) (by decide)


/-- **整轮 m 分析 · 轮末**（左移 / left）：整轮结束时模拟状态为查表所得 `m'`。
    Round m analysis, endpoint (left): at the end of the round the state is `m'`. -/
theorem simDrive_roundM_end_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprel : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run
      ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * pre'.length + 3 + 1)))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true)
            ++ (xc :: X')))))))).state.val
      = m'.val := by
  rw [simDrive_roundFull_left q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc hpre cq pre' hq hprel m' s' hx h]
  exact codeState_unpackM q b m'.val (K - 1) 0 0 m'.isLt (by omega) (by decide) (by decide)


/-- **整轮 m 分析**（右移 / right）：整轮内若某步仍处于模拟层，则它的模拟状态
    只能是轮起点值 `m`（前 4 步）或查表所得 `m'`（第 5–13 步与轮末）。
    Round m analysis (right): any simulation-layer state inside the round is either the
    round start `m` (first four steps) or the looked-up `m'` (steps 5–13 and endpoint). -/
theorem simDrive_roundM_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right))
    (i : Nat)
    (hi : i ≤ ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * (x.pre ++ [(s', false)]).length + 3 + 1))))
    (hlt : ((simDrive q b tab s0).run i
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true)
            ++ (xc :: X')))))))).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val = m
      ∨ unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val = m'.val := by
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · exact Or.inl (simDrive_roundM_le_stay q b tab s0 m c hm hc x z k xc X' i (by omega))
  · rcases Nat.lt_or_ge i 14 with h14 | h14
    · exact Or.inr (simDrive_roundM_ge q b tab s0 m c hm hc x z k xc X' m' s'
        hx h i (by omega) (by omega))
    · rcases Nat.lt_or_ge i
          ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
            + ((1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
              + (3 * (x.pre ++ [(s', false)]).length + 3 + 1))) with hend | hend
      · -- 14 ≤ i < 轮长：状态在导航层，与模拟层假设矛盾
        have hnav := simDrive_roundFullNav_right q b tab s0 m c hm hc x z k K hK hK2
          xc X' hxc hpre p post' hp hpost m' s' hx h i h14 hend
        omega
      · have hie : i = ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2)
            + (z + k + 3))
            + ((1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
              + (3 * (x.pre ++ [(s', false)]).length + 3 + 1))) := by omega
        subst hie
        exact Or.inr (simDrive_roundM_end_right q b tab s0 m c hm hc x z k K hK hK2
          xc X' hxc hpre p post' hp hpost m' s' hx h)

/-! ## 轮内 m 分析的 `passStart` 形态（供给分支桥接） -/


/-- **整轮 m 分析**（左移 / left）：整轮内若某步仍处于模拟层，则它的模拟状态
    只能是轮起点值 `m`（前 4 步）或查表所得 `m'`（第 5–13 步与轮末）。
    Round m analysis (left): any simulation-layer state inside the round is either the
    round start `m` (first four steps) or the looked-up `m'` (steps 5–13 and endpoint). -/
theorem simDrive_roundM_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprel : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left))
    (i : Nat)
    (hi : i ≤ ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
        + ((1 + ((List.replicate (k + 1) (some true)
          ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
          + (3 * pre'.length + 3 + 1))))
    (hlt : ((simDrive q b tab s0).run i
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true)
            ++ (xc :: X')))))))).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val = m
      ∨ unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val = m'.val := by
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · exact Or.inl (simDrive_roundM_le_stay q b tab s0 m c hm hc x z k xc X' i (by omega))
  · rcases Nat.lt_or_ge i 14 with h14 | h14
    · exact Or.inr (simDrive_roundM_ge q b tab s0 m c hm hc x z k xc X' m' s'
        hx h i (by omega) (by omega))
    · rcases Nat.lt_or_ge i
          ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
            + ((1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
              + (3 * pre'.length + 3 + 1))) with hend | hend
      · -- 14 ≤ i < 轮长：状态在导航层，与模拟层假设矛盾
        have hnav := simDrive_roundFullNav_left q b tab s0 m c hm hc x z k K hK hK2
          xc X' hxc hpre cq pre' hq hprel m' s' hx h i h14 hend
        omega
      · have hie : i = ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)
            + (z + k + 3))
            + ((1 + ((List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
              + (3 * pre'.length + 3 + 1))) := by omega
        subst hie
        exact Or.inr (simDrive_roundM_end_left q b tab s0 m c hm hc x z k K hK hK2
          xc X' hxc hpre cq pre' hq hprel m' s' hx h)

/-! ## 轮内 m 分析的 `passStart` 形态（供给分支桥接） -/


/-- **`passStart` 形态的整轮 m 分析**（右移 / right）：`passStart … Z (k :: ks)` 起步的
    整轮内，若某步仍在模拟层，则它的 `m` 是起点 `m`（前 4 步）或查表所得 `m'`。
    `passStart`-shaped round m analysis (right). -/
theorem simDrive_passStart_roundM_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat)
    (ks : List Nat) (xc : Sym) (X' : List Sym) (htail : digitArea ks = xc :: X')
    (hk : k + 2 < 2 ^ b) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right))
    (i : Nat) (hi : i ≤ roundCostRight x Z k p s')
    (hlt : ((simDrive q b tab s0).run i
      (passStart x m c hm hc Z (k :: ks))).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (passStart x m c hm hc Z (k :: ks))).state.val = m
      ∨ unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (passStart x m c hm hc Z (k :: ks))).state.val = m'.val := by
  have hcfg : passStart x m c hm hc Z (k :: ks)
      = Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    exact passStart_tape_eq Z k ks xc X' htail
  rw [hcfg] at hlt ⊢
  exact simDrive_roundM_right q b tab s0 m c hm hc x Z k (k + 2) hk rfl
    xc X' hxc hpre p post' hp hpost m' s' hx h i hi hlt


/-- **`passStart` 形态的整轮 m 分析**（左移 / left）：`passStart … Z (k :: ks)` 起步的
    整轮内，若某步仍在模拟层，则它的 `m` 是起点 `m`（前 4 步）或查表所得 `m'`。
    `passStart`-shaped round m analysis (left). -/
theorem simDrive_passStart_roundM_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat)
    (ks : List Nat) (xc : Sym) (X' : List Sym) (htail : digitArea ks = xc :: X')
    (hk : k + 2 < 2 ^ b) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprel : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left))
    (i : Nat) (hi : i ≤ roundCostLeft (q := q) Z k pre' cq s')
    (hlt : ((simDrive q b tab s0).run i
      (passStart x m c hm hc Z (k :: ks))).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (passStart x m c hm hc Z (k :: ks))).state.val = m
      ∨ unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
        (passStart x m c hm hc Z (k :: ks))).state.val = m'.val := by
  have hcfg : passStart x m c hm hc Z (k :: ks)
      = Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    exact passStart_tape_eq Z k ks xc X' htail
  rw [hcfg] at hlt ⊢
  exact simDrive_roundM_left q b tab s0 m c hm hc x Z k (k + 2) hk rfl
    xc X' hxc hpre cq pre' hq hprel m' s' hx h i hi hlt


/-- **分支桥接（通路仍在预算内，任意方向）**：若通路在 `r.steps` 以内仍未死亡，且驱动层
    某步的模拟层状态是接受态 `a`，则存在一个前缀通路，其终态区域的模拟状态正是 `a`。
    Branch bridge (within budget, any direction): a live pass plus an accepting
    simulation-layer hit yields an accepting prefix pass. -/
theorem passRun_accept_prefix_alive (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) (a : Fin q) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q),
      x.state = (⟨m, hm⟩ : Fin q) →
      (∀ p0 ∈ x.pre, p0.2 = false) →
      (∀ p0 ∈ x.post, p0.2 = false) →
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) →
      ∀ (r : PassRes q b), passRun q b tab Z c hc x L hb = some r →
        ∀ i, i ≤ r.steps →
          ((simDrive q b tab s0).run i (passStart x m c hm hc Z L)).state.val
            < stateCount q b →
          unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
              (passStart x m c hm hc Z L)).state.val = a.val →
          ∃ (L1 L2 : List Nat), L = L1 ++ L2 ∧
            ∃ (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
              passRun q b tab Z c hc x L1 hb1 = some r1 ∧ r1.reg.state = a := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x m hm hx hpre hpost hb r hpass i hi hlt hacc
      simp only [passRun, Option.some.injEq] at hpass
      subst hpass
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      have hm_eq : m = a.val := by
        have h := hacc
        rw [show ((simDrive q b tab s0).run 0 (passStart x m c hm hc Z [])).state.val
              = (codeState q b m c 0 0 hm hc (by decide) (by decide)).val from rfl,
            codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide)] at h
        exact h
      refine ⟨[], [], rfl, hb, ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
      rw [hx]
      exact Fin.ext hm_eq
  | cons k ks ih =>
      intro Z c hc x m hm hx hpre hpost hb r hpass i hi hlt hacc
      obtain ⟨xc, X', htail⟩ := digitArea_split ks
      have hxc := digitArea_head_ne_true ks xc X' htail
      have hkb : k + 2 < 2 ^ b := hb k (by rw [List.mem_cons]; exact Or.inl rfl)
      have hcK : k + 1 < 2 ^ b := by omega
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } ks
                  (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  subst hpass
                  rcases Nat.lt_or_ge i (roundCostStay x Z k s') with hltC | hgeC
                  · -- 轮内：前缀为空或单数字，`m` 只能是起点 `m` 或查表所得 `m'`
                    have hmv := simDrive_passStart_roundM_stay q b tab s0 x m c hm hc Z k
                      ks xc X' htail hkb hxc hpre  m' s' hx hpk i (by omega) hlt
                    rcases hmv with hmv | hmv
                    · refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
                        ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
                      have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
                      rw [hx]
                      exact Fin.ext hm_eq
                    · have hm'_eq : m' = a := by
                        apply Fin.ext
                        rw [hmv] at hacc
                        exact hacc
                      refine ⟨[k], ks, rfl, ?_, ⟨roundCostStay x Z k s', Z + k + 3, k + 1, hcK, { state := m', pre := x.pre, cur := s', post := x.post }⟩, ?_, ?_⟩
                      · intro k' hk'
                        rw [List.mem_singleton] at hk'
                        subst hk'
                        exact hkb
                      · rw [passRun_stay_unfold q b tab Z c hc x k [] _ m' s' hpk]
                        simp only [passRun, Option.map_some]
                        rfl
                      · rw [hm'_eq]
                  · -- 轮之后：剥掉一轮再归纳
                    have hC : (simDrive q b tab s0).run i
                        (passStart x m c hm hc Z (k :: ks))
                        = (simDrive q b tab s0).run (i - roundCostStay x Z k s')
                            (passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks) := by
                      rw [show i = roundCostStay x Z k s' + (i - roundCostStay x Z k s') from by omega, DTM.run_add]
                      rw [show (simDrive q b tab s0).run (roundCostStay x Z k s')
                          (passStart x m c hm hc Z (k :: ks))
                          = passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks from by
                        rw [simDrive_roundCanon_stay q b tab s0 m c hm hc x Z k (k + 2)
                          hkb rfl xc X' hxc hpre  m' s' hx hpk ks htail]
                        exact passStart_hc_irrel q b { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK hcK (Z + k + 3) ks]
                      rw [show roundCostStay x Z k s' + (i - roundCostStay x Z k s') - roundCostStay x Z k s' = i - roundCostStay x Z k s' from by omega]
                    have hlt' : ((simDrive q b tab s0).run (i - roundCostStay x Z k s')
                        (passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                        < stateCount q b := by
                      rw [← hC]; exact hlt
                    have hacc' : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run (i - roundCostStay x Z k s')
                        (passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                        = a.val := by
                      rw [← hC]; exact hacc
                    have hi' : i - roundCostStay x Z k s' ≤ r0.steps := by
                      have hi_ : i ≤ roundCostStay x Z k s' + r0.steps := by simpa using hi
                      omega
                    obtain ⟨L1', L2', hL', hb1', r1', hpass1', hreg1'⟩ :=
                      ih (Z + k + 3) (k + 1) hcK { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt rfl hpre hpost hb' r0 hrec
                        (i - roundCostStay x Z k s') hi' hlt' hacc'
                    have hb1k : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
                      intro k' hk'
                      rw [List.mem_cons] at hk'
                      rcases hk' with rfl | hk'
                      · exact hkb
                      · exact hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk'))
                    have hmap : passRun q b tab Z c hc x (k :: L1') hb1k
                        = (passRun q b tab (Z + k + 3) (k + 1)
                            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                            { state := m', pre := x.pre, cur := s', post := x.post } L1'
                            (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk')))).map
                            (fun r1 => ⟨roundCostStay x Z k s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩) := by
                      rw [passRun_stay_unfold q b tab Z c hc x k L1' hb1k m' s' hpk]
                    refine ⟨k :: L1', L2', ?_, hb1k,
                      ⟨roundCostStay x Z k s' + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg1'⟩
                    · rw [hL', List.cons_append]
                    · rw [hmap, hpass1']
                      simp only [Option.map_some]

          | right =>
                  cases hpost0 : x.post with
                  | nil =>
                          rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hpost0 hpk] at hpass
                          cases hpass
                  | cons p post' =>
                      have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                      have hpreR : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_append.mp hp0 with hp0' | hp0'
                        · exact hpre p0 hp0'
                        · rw [List.mem_singleton] at hp0'
                          subst hp0'
                          rfl
                      have hpostR : ∀ p0 ∈ post', p0.2 = false :=
                        fun p0 hp0 => hpost p0 (by rw [hpost0]; exact List.mem_cons_of_mem _ hp0)

                      rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk] at hpass
                      cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                      | none => rw [hrec] at hpass; cases hpass
                      | some r0 =>
                          rw [hrec] at hpass
                          simp only [Option.map_some, Option.some.injEq] at hpass
                          subst hpass
                          rcases Nat.lt_or_ge i (roundCostRight x Z k p s') with hltC | hgeC
                          · -- 轮内：前缀为空或单数字，`m` 只能是起点 `m` 或查表所得 `m'`
                            have hmv := simDrive_passStart_roundM_right q b tab s0 x m c hm hc Z k
                              ks xc X' htail hkb hxc hpre p post' hp hpost0 m' s' hx hpk i (by omega) hlt
                            rcases hmv with hmv | hmv
                            · refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
                                ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
                              have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
                              rw [hx]
                              exact Fin.ext hm_eq
                            · have hm'_eq : m' = a := by
                                apply Fin.ext
                                rw [hmv] at hacc
                                exact hacc
                              refine ⟨[k], ks, rfl, ?_, ⟨roundCostRight x Z k p s', Z + k + 3, k + 1, hcK, { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }⟩, ?_, ?_⟩
                              · intro k' hk'
                                rw [List.mem_singleton] at hk'
                                subst hk'
                                exact hkb
                              · rw [passRun_right_unfold q b tab Z c hc x k [] _ m' s' p post' hpost0 hpk]
                                simp only [passRun, Option.map_some]
                                rfl
                              · rw [hm'_eq]
                          · -- 轮之后：剥掉一轮再归纳
                            have hC : (simDrive q b tab s0).run i
                                (passStart x m c hm hc Z (k :: ks))
                                = (simDrive q b tab s0).run (i - roundCostRight x Z k p s')
                                    (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks) := by
                              rw [show i = roundCostRight x Z k p s' + (i - roundCostRight x Z k p s') from by omega, DTM.run_add]
                              rw [show (simDrive q b tab s0).run (roundCostRight x Z k p s')
                                  (passStart x m c hm hc Z (k :: ks))
                                  = passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks from by
                                rw [simDrive_roundCanon_right q b tab s0 m c hm hc x Z k (k + 2)
                                  hkb rfl xc X' hxc hpre p post' hp hpost0 m' s' hx hpk ks htail]
                                exact passStart_hc_irrel q b { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK hcK (Z + k + 3) ks]
                              rw [show roundCostRight x Z k p s' + (i - roundCostRight x Z k p s') - roundCostRight x Z k p s' = i - roundCostRight x Z k p s' from by omega]
                            have hlt' : ((simDrive q b tab s0).run (i - roundCostRight x Z k p s')
                                (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                < stateCount q b := by
                              rw [← hC]; exact hlt
                            have hacc' : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run (i - roundCostRight x Z k p s')
                                (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                = a.val := by
                              rw [← hC]; exact hacc
                            have hi' : i - roundCostRight x Z k p s' ≤ r0.steps := by
                              have hi_ : i ≤ roundCostRight x Z k p s' + r0.steps := by simpa using hi
                              omega
                            obtain ⟨L1', L2', hL', hb1', r1', hpass1', hreg1'⟩ :=
                              ih (Z + k + 3) (k + 1) hcK { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val m'.isLt rfl hpreR hpostR hb' r0 hrec
                                (i - roundCostRight x Z k p s') hi' hlt' hacc'
                            have hb1k : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
                              intro k' hk'
                              rw [List.mem_cons] at hk'
                              rcases hk' with rfl | hk'
                              · exact hkb
                              · exact hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk'))
                            have hmap : passRun q b tab Z c hc x (k :: L1') hb1k
                                = (passRun q b tab (Z + k + 3) (k + 1)
                                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } L1'
                                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk')))).map
                                    (fun r1 => ⟨roundCostRight x Z k p s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩) := by
                              rw [passRun_right_unfold q b tab Z c hc x k L1' hb1k m' s' p post' hpost0 hpk]
                            refine ⟨k :: L1', L2', ?_, hb1k,
                              ⟨roundCostRight x Z k p s' + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg1'⟩
                            · rw [hL', List.cons_append]
                            · rw [hmap, hpass1']
                              simp only [Option.map_some]

          | left =>
                  cases hrev : x.pre.reverse with
                  | nil =>
                          rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hrev hpk] at hpass
                          cases hpass
                  | cons cq preRev =>
                      have hpre2 : x.pre = preRev.reverse ++ [cq] := by
                        rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                      have hq : cq.2 = false :=
                        hpre cq (by rw [hpre2]; exact List.mem_append_right _ (by simp))
                      have hpreL : ∀ p0 ∈ preRev.reverse, p0.2 = false := by
                        intro p0 hp0
                        exact hpre p0 (by rw [hpre2]; exact List.mem_append_left _ hp0)
                      have hpostL : ∀ p0 ∈ (s', false) :: x.post, p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_cons.mp hp0 with rfl | hp0'
                        · rfl
                        · exact hpost p0 hp0'

                      rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk] at hpass
                      cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } ks
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                      | none => rw [hrec] at hpass; cases hpass
                      | some r0 =>
                          rw [hrec] at hpass
                          simp only [Option.map_some, Option.some.injEq] at hpass
                          subst hpass
                          rcases Nat.lt_or_ge i (roundCostLeft (q := q) Z k preRev.reverse cq s') with hltC | hgeC
                          · -- 轮内：前缀为空或单数字，`m` 只能是起点 `m` 或查表所得 `m'`
                            have hmv := simDrive_passStart_roundM_left q b tab s0 x m c hm hc Z k
                              ks xc X' htail hkb hxc hpre cq preRev.reverse hq hpre2 m' s' hx hpk i (by omega) hlt
                            rcases hmv with hmv | hmv
                            · refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
                                ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
                              have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
                              rw [hx]
                              exact Fin.ext hm_eq
                            · have hm'_eq : m' = a := by
                                apply Fin.ext
                                rw [hmv] at hacc
                                exact hacc
                              refine ⟨[k], ks, rfl, ?_, ⟨roundCostLeft (q := q) Z k preRev.reverse cq s', Z + k + 3, k + 1, hcK, { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }⟩, ?_, ?_⟩
                              · intro k' hk'
                                rw [List.mem_singleton] at hk'
                                subst hk'
                                exact hkb
                              · rw [passRun_left_unfold q b tab Z c hc x k [] _ m' s' cq preRev hrev hpk]
                                simp only [passRun, Option.map_some]
                                rfl
                              · rw [hm'_eq]
                          · -- 轮之后：剥掉一轮再归纳
                            have hC : (simDrive q b tab s0).run i
                                (passStart x m c hm hc Z (k :: ks))
                                = (simDrive q b tab s0).run (i - roundCostLeft (q := q) Z k preRev.reverse cq s')
                                    (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks) := by
                              rw [show i = roundCostLeft (q := q) Z k preRev.reverse cq s' + (i - roundCostLeft (q := q) Z k preRev.reverse cq s') from by omega, DTM.run_add]
                              rw [show (simDrive q b tab s0).run (roundCostLeft (q := q) Z k preRev.reverse cq s')
                                  (passStart x m c hm hc Z (k :: ks))
                                  = passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks from by
                                rw [simDrive_roundCanon_left q b tab s0 m c hm hc x Z k (k + 2)
                                  hkb rfl xc X' hxc hpre cq preRev.reverse hq hpre2 m' s' hx hpk ks htail]
                                exact passStart_hc_irrel q b { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK hcK (Z + k + 3) ks]
                              rw [show roundCostLeft (q := q) Z k preRev.reverse cq s' + (i - roundCostLeft (q := q) Z k preRev.reverse cq s') - roundCostLeft (q := q) Z k preRev.reverse cq s' = i - roundCostLeft (q := q) Z k preRev.reverse cq s' from by omega]
                            have hlt' : ((simDrive q b tab s0).run (i - roundCostLeft (q := q) Z k preRev.reverse cq s')
                                (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                < stateCount q b := by
                              rw [← hC]; exact hlt
                            have hacc' : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run (i - roundCostLeft (q := q) Z k preRev.reverse cq s')
                                (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                = a.val := by
                              rw [← hC]; exact hacc
                            have hi' : i - roundCostLeft (q := q) Z k preRev.reverse cq s' ≤ r0.steps := by
                              have hi_ : i ≤ roundCostLeft (q := q) Z k preRev.reverse cq s' + r0.steps := by simpa using hi
                              omega
                            obtain ⟨L1', L2', hL', hb1', r1', hpass1', hreg1'⟩ :=
                              ih (Z + k + 3) (k + 1) hcK { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val m'.isLt rfl hpreL hpostL hb' r0 hrec
                                (i - roundCostLeft (q := q) Z k preRev.reverse cq s') hi' hlt' hacc'
                            have hb1k : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
                              intro k' hk'
                              rw [List.mem_cons] at hk'
                              rcases hk' with rfl | hk'
                              · exact hkb
                              · exact hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk'))
                            have hmap : passRun q b tab Z c hc x (k :: L1') hb1k
                                = (passRun q b tab (Z + k + 3) (k + 1)
                                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                                    { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } L1'
                                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk')))).map
                                    (fun r1 => ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩) := by
                              rw [passRun_left_unfold q b tab Z c hc x k L1' hb1k m' s' cq preRev hrev hpk]
                            refine ⟨k :: L1', L2', ?_, hb1k,
                              ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg1'⟩
                            · rw [hL', List.cons_append]
                            · rw [hmap, hpass1']
                              simp only [Option.map_some]



/-- **分支桥接（通路已死亡，任意方向）**：若通路在某轮查表失败（`passRun = none`），则驱动层
    任何一步的模拟层接受态命中，都同样对应某个前缀通路的接受终态。`hpadpost`/`hpadpre`
    要求区域两侧各留出至少轮数格的空白（供给越界排除，见 auto-run-log #107）。
    Branch bridge (dead pass, any direction), with a blank-padding side condition. -/
theorem passRun_accept_prefix_dead (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) (a : Fin q) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q),
      x.state = (⟨m, hm⟩ : Fin q) →
      (∀ p0 ∈ x.pre, p0.2 = false) →
      (∀ p0 ∈ x.post, p0.2 = false) →
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) →
      (hpadpost : L.length ≤ x.post.length) →
      (hpadpre : L.length ≤ x.pre.length) →
      passRun q b tab Z c hc x L hb = none →
      ∀ i,
        ((simDrive q b tab s0).run i (passStart x m c hm hc Z L)).state.val
          < stateCount q b →
        unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
            (passStart x m c hm hc Z L)).state.val = a.val →
        ∃ (L1 L2 : List Nat), L = L1 ++ L2 ∧
          ∃ (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
            passRun q b tab Z c hc x L1 hb1 = some r1 ∧ r1.reg.state = a := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x m hm hx hpre hpost hb hpadpost hpadpre hpass i hlt hacc
      simp only [passRun] at hpass
      cases hpass
  | cons k ks ih =>
      intro Z c hc x m hm hx hpre hpost hb hpadpost hpadpre hpass i hlt hacc
      obtain ⟨xc, X', htail⟩ := digitArea_split ks
      have hxc := digitArea_head_ne_true ks xc X' htail
      have hkb : k + 2 < 2 ^ b := hb k (by rw [List.mem_cons]; exact Or.inl rfl)
      have hcK : k + 1 < 2 ^ b :=
        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          have hmv := simDrive_passStart_roundM_none q b tab s0 x m c hm hc Z k ks hx hpk i
          refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
            ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
          have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
          rw [hx]
          exact Fin.ext hm_eq
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } ks
                  (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
              | some r0 => rw [hrec] at hpass; cases hpass
              | none =>
                  rcases Nat.lt_or_ge i (roundCostStay x Z k s') with hltC | hgeC
                  · -- 轮内：前缀为空或单数字
                    have hmv := simDrive_passStart_roundM_stay q b tab s0 x m c hm hc Z k
                      ks xc X' htail hkb hxc hpre  m' s' hx hpk i (by omega) hlt
                    rcases hmv with hmv | hmv
                    · refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
                        ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
                      have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
                      rw [hx]
                      exact Fin.ext hm_eq
                    · have hm'_eq : m' = a := by
                        apply Fin.ext
                        rw [hmv] at hacc
                        exact hacc
                      refine ⟨[k], ks, rfl, ?_, ⟨roundCostStay x Z k s', Z + k + 3, k + 1, hcK, { state := m', pre := x.pre, cur := s', post := x.post }⟩, ?_, ?_⟩
                      · intro k' hk'
                        rw [List.mem_singleton] at hk'
                        subst hk'
                        exact hkb
                      · rw [passRun_stay_unfold q b tab Z c hc x k [] _ m' s' hpk]
                        simp only [passRun, Option.map_some]
                        rfl
                      · rw [hm'_eq]
                  · -- 轮之后：剥掉一轮再归纳
                    have hC : (simDrive q b tab s0).run i
                        (passStart x m c hm hc Z (k :: ks))
                        = (simDrive q b tab s0).run (i - roundCostStay x Z k s')
                            (passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks) := by
                      rw [show i = roundCostStay x Z k s' + (i - roundCostStay x Z k s') from by omega, DTM.run_add]
                      rw [show (simDrive q b tab s0).run (roundCostStay x Z k s')
                          (passStart x m c hm hc Z (k :: ks))
                          = passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks from by
                        rw [simDrive_roundCanon_stay q b tab s0 m c hm hc x Z k (k + 2)
                          hkb rfl xc X' hxc hpre  m' s' hx hpk ks htail]
                        exact passStart_hc_irrel q b { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK hcK (Z + k + 3) ks]
                      rw [show roundCostStay x Z k s' + (i - roundCostStay x Z k s') - roundCostStay x Z k s' = i - roundCostStay x Z k s' from by omega]
                    have hlt' : ((simDrive q b tab s0).run (i - roundCostStay x Z k s')
                        (passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                        < stateCount q b := by
                      rw [← hC]; exact hlt
                    have hacc' : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run (i - roundCostStay x Z k s')
                        (passStart { state := m', pre := x.pre, cur := s', post := x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                        = a.val := by
                      rw [← hC]; exact hacc
                    have hpadpost' : ks.length ≤ x.post.length := by
                      simp only [List.length_cons] at hpadpost
                      omega
                    have hpadpre' : ks.length ≤ x.pre.length := by
                      simp only [List.length_cons] at hpadpre
                      omega
                    obtain ⟨L1', L2', hL', hb1', r1', hpass1', hreg1'⟩ :=
                      ih (Z + k + 3) (k + 1) hcK { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt rfl hpre hpost hb' hpadpost' hpadpre' hrec
                        (i - roundCostStay x Z k s') hlt' hacc'
                    have hb1k : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
                      intro k' hk'
                      rw [List.mem_cons] at hk'
                      rcases hk' with rfl | hk'
                      · exact hkb
                      · exact hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk'))
                    have hmap : passRun q b tab Z c hc x (k :: L1') hb1k
                        = (passRun q b tab (Z + k + 3) (k + 1)
                            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                            { state := m', pre := x.pre, cur := s', post := x.post } L1'
                            (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk')))).map
                            (fun r1 => ⟨roundCostStay x Z k s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩) := by
                      rw [passRun_stay_unfold q b tab Z c hc x k L1' hb1k m' s' hpk]
                    refine ⟨k :: L1', L2', ?_, hb1k,
                      ⟨roundCostStay x Z k s' + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg1'⟩
                    · rw [hL', List.cons_append]
                    · rw [hmap, hpass1']
                      simp only [Option.map_some]

          | right =>
                  cases hpost0 : x.post with
                  | nil =>
                          exfalso
                          have hlen : x.post.length = 0 := by rw [hpost0]; rfl
                          simp only [List.length_cons] at hpadpost
                          omega
                  | cons p post' =>
                      have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                      have hpreR : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_append.mp hp0 with hp0' | hp0'
                        · exact hpre p0 hp0'
                        · rw [List.mem_singleton] at hp0'
                          subst hp0'
                          rfl
                      have hpostR : ∀ p0 ∈ post', p0.2 = false :=
                        fun p0 hp0 => hpost p0 (by rw [hpost0]; exact List.mem_cons_of_mem _ hp0)

                      rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk] at hpass
                      cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                      | some r0 => rw [hrec] at hpass; cases hpass
                      | none =>
                          rcases Nat.lt_or_ge i (roundCostRight x Z k p s') with hltC | hgeC
                          · -- 轮内：前缀为空或单数字
                            have hmv := simDrive_passStart_roundM_right q b tab s0 x m c hm hc Z k
                              ks xc X' htail hkb hxc hpre p post' hp hpost0 m' s' hx hpk i (by omega) hlt
                            rcases hmv with hmv | hmv
                            · refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
                                ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
                              have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
                              rw [hx]
                              exact Fin.ext hm_eq
                            · have hm'_eq : m' = a := by
                                apply Fin.ext
                                rw [hmv] at hacc
                                exact hacc
                              refine ⟨[k], ks, rfl, ?_, ⟨roundCostRight x Z k p s', Z + k + 3, k + 1, hcK, { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }⟩, ?_, ?_⟩
                              · intro k' hk'
                                rw [List.mem_singleton] at hk'
                                subst hk'
                                exact hkb
                              · rw [passRun_right_unfold q b tab Z c hc x k [] _ m' s' p post' hpost0 hpk]
                                simp only [passRun, Option.map_some]
                                rfl
                              · rw [hm'_eq]
                          · -- 轮之后：剥掉一轮再归纳
                            have hC : (simDrive q b tab s0).run i
                                (passStart x m c hm hc Z (k :: ks))
                                = (simDrive q b tab s0).run (i - roundCostRight x Z k p s')
                                    (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks) := by
                              rw [show i = roundCostRight x Z k p s' + (i - roundCostRight x Z k p s') from by omega, DTM.run_add]
                              rw [show (simDrive q b tab s0).run (roundCostRight x Z k p s')
                                  (passStart x m c hm hc Z (k :: ks))
                                  = passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks from by
                                rw [simDrive_roundCanon_right q b tab s0 m c hm hc x Z k (k + 2)
                                  hkb rfl xc X' hxc hpre p post' hp hpost0 m' s' hx hpk ks htail]
                                exact passStart_hc_irrel q b { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK hcK (Z + k + 3) ks]
                              rw [show roundCostRight x Z k p s' + (i - roundCostRight x Z k p s') - roundCostRight x Z k p s' = i - roundCostRight x Z k p s' from by omega]
                            have hlt' : ((simDrive q b tab s0).run (i - roundCostRight x Z k p s')
                                (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                < stateCount q b := by
                              rw [← hC]; exact hlt
                            have hacc' : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run (i - roundCostRight x Z k p s')
                                (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                = a.val := by
                              rw [← hC]; exact hacc
                            have hpadpost' : ks.length ≤ post'.length := by
                              simp only [List.length_cons] at hpadpost
                              rw [hpost0] at hpadpost
                              simp only [List.length_cons] at hpadpost
                              omega
                            have hpadpre' : ks.length ≤ (x.pre ++ [(s', false)]).length := by
                              simp only [List.length_cons] at hpadpre
                              rw [List.length_append]
                              simp only [List.length_cons]
                              omega
                            obtain ⟨L1', L2', hL', hb1', r1', hpass1', hreg1'⟩ :=
                              ih (Z + k + 3) (k + 1) hcK { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } m'.val m'.isLt rfl hpreR hpostR hb' hpadpost' hpadpre' hrec
                                (i - roundCostRight x Z k p s') hlt' hacc'
                            have hb1k : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
                              intro k' hk'
                              rw [List.mem_cons] at hk'
                              rcases hk' with rfl | hk'
                              · exact hkb
                              · exact hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk'))
                            have hmap : passRun q b tab Z c hc x (k :: L1') hb1k
                                = (passRun q b tab (Z + k + 3) (k + 1)
                                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } L1'
                                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk')))).map
                                    (fun r1 => ⟨roundCostRight x Z k p s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩) := by
                              rw [passRun_right_unfold q b tab Z c hc x k L1' hb1k m' s' p post' hpost0 hpk]
                            refine ⟨k :: L1', L2', ?_, hb1k,
                              ⟨roundCostRight x Z k p s' + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg1'⟩
                            · rw [hL', List.cons_append]
                            · rw [hmap, hpass1']
                              simp only [Option.map_some]

          | left =>
                  cases hrev : x.pre.reverse with
                  | nil =>
                          exfalso
                          have hlen : x.pre.length = 0 := by
                            have h := congrArg List.length hrev
                            simp only [List.length_reverse, List.length_nil] at h
                            omega
                          simp only [List.length_cons] at hpadpre
                          omega
                  | cons cq preRev =>
                      have hpre2 : x.pre = preRev.reverse ++ [cq] := by
                        rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                      have hq : cq.2 = false :=
                        hpre cq (by rw [hpre2]; exact List.mem_append_right _ (by simp))
                      have hpreL : ∀ p0 ∈ preRev.reverse, p0.2 = false := by
                        intro p0 hp0
                        exact hpre p0 (by rw [hpre2]; exact List.mem_append_left _ hp0)
                      have hpostL : ∀ p0 ∈ (s', false) :: x.post, p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_cons.mp hp0 with rfl | hp0'
                        · rfl
                        · exact hpost p0 hp0'

                      rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk] at hpass
                      cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } ks
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                      | some r0 => rw [hrec] at hpass; cases hpass
                      | none =>
                          rcases Nat.lt_or_ge i (roundCostLeft (q := q) Z k preRev.reverse cq s') with hltC | hgeC
                          · -- 轮内：前缀为空或单数字
                            have hmv := simDrive_passStart_roundM_left q b tab s0 x m c hm hc Z k
                              ks xc X' htail hkb hxc hpre cq preRev.reverse hq hpre2 m' s' hx hpk i (by omega) hlt
                            rcases hmv with hmv | hmv
                            · refine ⟨[], k :: ks, rfl, (fun k' hk' => by simp at hk'),
                                ⟨0, Z, c, hc, x⟩, rfl, ?_⟩
                              have hm_eq : m = a.val := by rw [hmv] at hacc; exact hacc
                              rw [hx]
                              exact Fin.ext hm_eq
                            · have hm'_eq : m' = a := by
                                apply Fin.ext
                                rw [hmv] at hacc
                                exact hacc
                              refine ⟨[k], ks, rfl, ?_, ⟨roundCostLeft (q := q) Z k preRev.reverse cq s', Z + k + 3, k + 1, hcK, { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }⟩, ?_, ?_⟩
                              · intro k' hk'
                                rw [List.mem_singleton] at hk'
                                subst hk'
                                exact hkb
                              · rw [passRun_left_unfold q b tab Z c hc x k [] _ m' s' cq preRev hrev hpk]
                                simp only [passRun, Option.map_some]
                                rfl
                              · rw [hm'_eq]
                          · -- 轮之后：剥掉一轮再归纳
                            have hC : (simDrive q b tab s0).run i
                                (passStart x m c hm hc Z (k :: ks))
                                = (simDrive q b tab s0).run (i - roundCostLeft (q := q) Z k preRev.reverse cq s')
                                    (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks) := by
                              rw [show i = roundCostLeft (q := q) Z k preRev.reverse cq s' + (i - roundCostLeft (q := q) Z k preRev.reverse cq s') from by omega, DTM.run_add]
                              rw [show (simDrive q b tab s0).run (roundCostLeft (q := q) Z k preRev.reverse cq s')
                                  (passStart x m c hm hc Z (k :: ks))
                                  = passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks from by
                                rw [simDrive_roundCanon_left q b tab s0 m c hm hc x Z k (k + 2)
                                  hkb rfl xc X' hxc hpre cq preRev.reverse hq hpre2 m' s' hx hpk ks htail]
                                exact passStart_hc_irrel q b { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK hcK (Z + k + 3) ks]
                              rw [show roundCostLeft (q := q) Z k preRev.reverse cq s' + (i - roundCostLeft (q := q) Z k preRev.reverse cq s') - roundCostLeft (q := q) Z k preRev.reverse cq s' = i - roundCostLeft (q := q) Z k preRev.reverse cq s' from by omega]
                            have hlt' : ((simDrive q b tab s0).run (i - roundCostLeft (q := q) Z k preRev.reverse cq s')
                                (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                < stateCount q b := by
                              rw [← hC]; exact hlt
                            have hacc' : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run (i - roundCostLeft (q := q) Z k preRev.reverse cq s')
                                (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val (k + 1) m'.isLt hcK (Z + k + 3) ks)).state.val
                                = a.val := by
                              rw [← hC]; exact hacc
                            have hpadpost' : ks.length ≤ ((s', false) :: x.post).length := by
                              simp only [List.length_cons] at hpadpost ⊢
                              omega
                            have hpadpre' : ks.length ≤ preRev.reverse.length := by
                              have hlen : x.pre.length = preRev.length + 1 := by
                                have h := congrArg List.length hrev
                                simp only [List.length_reverse, List.length_cons] at h
                                omega
                              simp only [List.length_cons] at hpadpre
                              simp only [List.length_reverse]
                              omega
                            obtain ⟨L1', L2', hL', hb1', r1', hpass1', hreg1'⟩ :=
                              ih (Z + k + 3) (k + 1) hcK { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } m'.val m'.isLt rfl hpreL hpostL hb' hpadpost' hpadpre' hrec
                                (i - roundCostLeft (q := q) Z k preRev.reverse cq s') hlt' hacc'
                            have hb1k : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
                              intro k' hk'
                              rw [List.mem_cons] at hk'
                              rcases hk' with rfl | hk'
                              · exact hkb
                              · exact hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk'))
                            have hmap : passRun q b tab Z c hc x (k :: L1') hb1k
                                = (passRun q b tab (Z + k + 3) (k + 1)
                                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                                    { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } L1'
                                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr (by rw [hL']; exact List.mem_append_left _ hk')))).map
                                    (fun r1 => ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩) := by
                              rw [passRun_left_unfold q b tab Z c hc x k L1' hb1k m' s' cq preRev hrev hpk]
                            refine ⟨k :: L1', L2', ?_, hb1k,
                              ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg1'⟩
                            · rw [hL', List.cons_append]
                            · rw [hmap, hpass1']
                              simp only [Option.map_some]



/-- **分支桥接总引理**：无论通路是「仍在预算内」还是「已死亡」，驱动层模拟层的接受态
    命中都对应某个前缀通路的接受终态。
    Branch bridge (combined): whether the pass is still within budget or already dead,
    an accepting simulation-layer hit yields an accepting prefix pass. -/
theorem passRun_accept_prefix (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) (a : Fin q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpadpost : L.length ≤ x.post.length)
    (hpadpre : L.length ≤ x.pre.length)
    (i : Nat)
    (hlt : ((simDrive q b tab s0).run i (passStart x m c hm hc Z L)).state.val
      < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 ((simDrive q b tab s0).run i
      (passStart x m c hm hc Z L)).state.val = a.val)
    (hcase : (∃ (r : PassRes q b),
        passRun q b tab Z c hc x L hb = some r ∧ i ≤ r.steps)
      ∨ passRun q b tab Z c hc x L hb = none) :
    ∃ (L1 L2 : List Nat), L = L1 ++ L2 ∧
      ∃ (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
        passRun q b tab Z c hc x L1 hb1 = some r1 ∧ r1.reg.state = a := by
  rcases hcase with ⟨r, hpass, hi⟩ | hpass
  · exact passRun_accept_prefix_alive q b tab s0 a L Z c hc x m hm
      hx hpre hpost hb r hpass i hi hlt hacc
  · exact passRun_accept_prefix_dead q b tab s0 a L Z c hc x m hm
      hx hpre hpost hb hpadpost hpadpre hpass i hlt hacc


/-- **由观察层接受命中得到接受前缀通路**：通路成功、预算内无内部接受态、且观察机
    在 `r.steps` 以内命中接受哨兵，则存在一个接受态为 `M.accept` 的前缀通路。
    An observer accept hit within the pass budget yields an accepting prefix pass. -/
theorem passRun_accept_prefix_of_obs_acc (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpadpost : L.length ≤ x.post.length)
    (hpadpre : L.length ≤ x.pre.length)
    (r : PassRes q b) (hpass : passRun q b M.step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b M.step M.start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b M.step M.start).run i
            (passStart x m c hm hc Z L)).state.val ≠ M.accept.val)
    (n : Nat) (hn : n ≤ r.steps)
    (hacc : ((simObs q b M).run n
      (Config.mk (embO q b (passStart x m c hm hc Z L).state)
        (passStart x m c hm hc Z L).tape)).state = obsAcc q b) :
    ∃ (L1 L2 : List Nat), L = L1 ++ L2 ∧
      ∃ (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
        passRun q b M.step Z c hc x L1 hb1 = some r1 ∧ r1.reg.state = M.accept := by
  -- 预算内观察状态都可观察
  have hobs := simObs_pass_obs q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
  -- 预算内观察机不会接受：命中必须是首次
  have hno : ∀ k : Nat, k < n →
      ((simObs q b M).run k
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
    intro k hk
    exact simObs_no_acc_upto q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc k
      (by omega)
  -- 逆投影：命中前一步的驱动状态是接受态
  obtain ⟨i, hi, hlt, hacci⟩ :=
    simObs_acc_hit q b M n (passStart x m c hm hc Z L)
      (fun j hj => hobs j (by omega)) hacc hno
  exact passRun_accept_prefix q b M.step M.start M.accept L Z c hc x m hm hx hpre
    hpost hb hpadpost hpadpre i hlt hacci (Or.inl ⟨r, hpass, by omega⟩)


end DTM

end Pnp
