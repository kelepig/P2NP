/-
  文件：Pnp/Machine/SimObsTail.lean
  File: Pnp/Machine/SimObsTail.lean

  主题：观察机 `simObs` 的状态轨迹只依赖驱动状态轨迹，与纸带尾部无关。
        若两条驱动轨迹在 `N` 步内的状态完全一致，则两条观察轨迹在 `N` 步内的
        状态也完全一致（纸带可以不同，但不会进入状态）。

  Topic: the observer `simObs` state trajectory depends only on the driver state
  trajectory, not on the tape tail. If two driver runs agree on their states for
  `N` steps, the two observer runs agree on theirs for `N` steps as well.

  说明（为什么加重「状态号在范围内」的前提）：
    `simObs` 的委托分支会先让 `simDrive` 走一步，而 `simDrive` 一步的结果依赖当前
    读到的符号。若初始状态恰好是驱动层的终态哨兵（状态号 `2 * stateCount`），
    驱动本身会原地冻结（状态轨迹恒定相等），但观察机在该内部状态仍按纸带符号委托，
    于是两条不同纸带的观察状态可能分叉。因此要排除这种退化起点：本文件的主定理
    显式要求两条初始驱动状态号 `< 2 * stateCount`（`passStart` 起点自动满足）。

  Note (why the range premise is needed):
    the delegation branch lets `simDrive` take a step whose result depends on the
    current symbol; if the initial driver state is the terminal sentinel
    (`2 * stateCount`) the driver freezes while the observer still delegates on the
    tape symbol, so different tapes may split. The main theorem therefore assumes
    both initial driver states are in range; `passStart` starts satisfy this.

  本文件给出：
    - `obs_sentinel_cases` / `simObs_halted_sentinel` / `simObs_run_sentinel_state`：
      哨兵状态的两个可能取值、在哨兵上不停机与运行冻结；
    - `simObs_stepConfig_fail_state`：相位 14 的单步落入失败哨兵；
    - `simObs_congr_invariant`：耦合归纳不变量（状态相等 + 纸带一致的重新编码）；
    - `simObs_run_state_congr`：主定理（带范围前提）；
    - `simObs_states_congr_of_passStart`：`passStart` 起点的直接推论。
  This file provides sentinel helpers, the coupled induction invariant, the main
  state-congruence theorem, and its `passStart` corollary.
-/

import Pnp.Machine.SimObsRun
import Pnp.Machine.SimBudget
import Pnp.Machine.PadBranch

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-! ## 哨兵状态的基本事实 -/

/-- 观察层状态号不小于驱动状态数时，只能是接受哨兵或失败哨兵。
    A state number at least `stateCountD` is either `obsAcc` or `obsFail`. -/
theorem obs_sentinel_cases (q b : Nat) (s : Fin (stateCountO q b))
    (h : ¬ s.val < stateCountD q b) :
    s = obsAcc q b ∨ s = obsFail q b := by
  have hs := s.isLt
  unfold stateCountO at hs
  have h1 : s.val = stateCountD q b ∨ s.val = stateCountD q b + 1 := by omega
  rcases h1 with h1 | h1
  · left
    apply Fin.ext
    show s.val = (obsAcc q b).val
    rw [h1]
    rfl
  · right
    apply Fin.ext
    show s.val = (obsFail q b).val
    rw [h1]
    rfl

/-- 位于哨兵状态的观察机已停机（接受 / 拒绝状态）。
    The observer is halted once it sits on a sentinel. -/
theorem simObs_halted_sentinel (q b : Nat) (M : NTM q) (s : Fin (stateCountO q b))
    (h : ¬ s.val < stateCountD q b) (t : Tape) :
    (simObs q b M).halted (Config.mk s t) = true := by
  rcases obs_sentinel_cases q b s h with rfl | rfl
  · exact halted_of_accept_or_reject (simObs q b M) _ (Or.inl rfl)
  · exact halted_of_accept_or_reject (simObs q b M) _ (Or.inr rfl)

/-- 哨兵状态上运行冻结：再跑任意步，状态不变。
    On a sentinel the run is frozen: the state never changes. -/
theorem simObs_run_sentinel_state (q b : Nat) (M : NTM q) (n : Nat)
    (c : Config (stateCountO q b)) (h : ¬ c.state.val < stateCountD q b) :
    ((simObs q b M).run n c).state = c.state := by
  have hhalt : (simObs q b M).halted c = true :=
    simObs_halted_sentinel q b M c.state h c.tape
  rw [run_of_halted (simObs q b M) c hhalt n]

/-- 模拟层相位 14 的单步（状态层面）：观察机进入失败哨兵。
    Phase-14 single step (state level): the observer enters the failure sentinel. -/
theorem simObs_stepConfig_fail_state (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (t : Tape)
    (hlt : st.val < stateCountD q b) (hin : st.val < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 st.val ≠ M.accept.val)
    (h14 : unpackPh (2 ^ b) 9 15 st.val = 14) :
    ((simObs q b M).stepConfig (Config.mk (embO q b st) t)).state = obsFail q b := by
  rw [stepConfig_state]
  rw [simObs_step_fail q b M (embO q b st) hlt hin hacc h14 t.read]

/-! ## 耦合归纳不变量 -/

/-- **耦合归纳不变量**：在两条驱动状态轨迹 `N` 步内一致的假设下，
    观察轨迹有两个性质同时成立：
      (1) 第 `n` 步的两个观察状态相等；
      (2) 只要第 `n` 步的观察状态还在驱动层（状态号 `< stateCountD`），
          它的整条格局就是第 `n` 步驱动格局的重新编码（状态与纸带都一致）。
    第 (2) 条保证「委托一步」时观察机纸带读数与驱动纸带一致，从而下一步状态也一致。

    Coupled induction invariant: state equality plus tape-faithful re-encoding while
    the observer is still in the driver layer. -/
theorem simObs_congr_invariant (q b : Nat) (M : NTM q)
    (c1 c2 : Config (stateCountD q b)) (N : Nat)
    (hr1 : c1.state.val < 2 * stateCount q b)
    (hr2 : c2.state.val < 2 * stateCount q b)
    (hN : ∀ i : Nat, i ≤ N →
      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i c1).state
      = ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i c2).state) :
    ∀ n : Nat, n ≤ N →
      ((simObs q b (M.haltNorm)).run n
          (Config.mk (embO q b c1.state) c1.tape)).state
        = ((simObs q b (M.haltNorm)).run n
          (Config.mk (embO q b c2.state) c2.tape)).state ∧
      (((simObs q b (M.haltNorm)).run n
          (Config.mk (embO q b c1.state) c1.tape)).state.val < stateCountD q b →
        ((simObs q b (M.haltNorm)).run n
            (Config.mk (embO q b c1.state) c1.tape))
          = Config.mk (embO q b
              ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state)
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape ∧
        ((simObs q b (M.haltNorm)).run n
            (Config.mk (embO q b c2.state) c2.tape))
          = Config.mk (embO q b
              ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state)
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape) := by
  intro n
  induction n with
  | zero =>
      -- 基例：第 0 步两侧都是初始格局；驱动第 0 步就是 `c_j` 本身
      intro _
      constructor
      · have h0 : c1.state = c2.state := by
          have := hN 0 (Nat.zero_le N)
          simpa only [DTM.run] using this
        simp only [DTM.run]
        rw [h0]
      · intro _
        constructor <;> simp only [DTM.run]
  | succ n ih =>
      intro hn1
      have hn : n ≤ N := by omega
      obtain ⟨hA, hB⟩ := ih hn
      -- 目标里的步数索引已经是 `n + 1`，可直接套用 `run_add` / `run_succ_last`
      by_cases hs : ((simObs q b (M.haltNorm)).run n
          (Config.mk (embO q b c1.state) c1.tape)).state.val < stateCountD q b
      · -- ---------- 情形一：第 n 步仍在驱动层（可重新编码） ----------
        obtain ⟨hrec1, hrec2⟩ := hB hs
        -- 驱动第 n 步的状态号仍在范围内
        have hrg1 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.val
            < 2 * stateCount q b :=
          simDrive_run_range q b (M.haltNorm).step (M.haltNorm).start n c1 hr1
        have hrg2 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
            < 2 * stateCount q b :=
          simDrive_run_range q b (M.haltNorm).step (M.haltNorm).start n c2 hr2
        -- 两条驱动第 n 步状态相等
        have heqst : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state
            = ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state :=
          hN n hn
        -- 观察机在两处都不停机
        have hhaltO1 : (simObs q b (M.haltNorm)).halted
            ((simObs q b (M.haltNorm)).run n
              (Config.mk (embO q b c1.state) c1.tape)) = false := by
          rw [hrec1]
          exact simObs_halted_inner q b (M.haltNorm)
            (embO q b ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state)
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.isLt
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape
        have hhaltO2 : (simObs q b (M.haltNorm)).halted
            ((simObs q b (M.haltNorm)).run n
              (Config.mk (embO q b c2.state) c2.tape)) = false := by
          rw [hrec2]
          exact simObs_halted_inner q b (M.haltNorm)
            (embO q b ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state)
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.isLt
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape
        -- 观察机走一步 = 对第 n 步重新编码格局做 `stepConfig`
        have hstep1 : (simObs q b (M.haltNorm)).run (n + 1)
            (Config.mk (embO q b c1.state) c1.tape)
            = (simObs q b (M.haltNorm)).stepConfig
                ((simObs q b (M.haltNorm)).run n
                  (Config.mk (embO q b c1.state) c1.tape)) :=
          run_succ_last (simObs q b (M.haltNorm)) n _ hhaltO1
        have hstep2 : (simObs q b (M.haltNorm)).run (n + 1)
            (Config.mk (embO q b c2.state) c2.tape)
            = (simObs q b (M.haltNorm)).stepConfig
                ((simObs q b (M.haltNorm)).run n
                  (Config.mk (embO q b c2.state) c2.tape)) :=
          run_succ_last (simObs q b (M.haltNorm)) n _ hhaltO2
        have hstep1' : (simObs q b (M.haltNorm)).run (n + 1)
            (Config.mk (embO q b c1.state) c1.tape)
            = (simObs q b (M.haltNorm)).stepConfig
                (Config.mk (embO q b
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state)
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape) := by
          rw [hstep1, hrec1]
        have hstep2' : (simObs q b (M.haltNorm)).run (n + 1)
            (Config.mk (embO q b c2.state) c2.tape)
            = (simObs q b (M.haltNorm)).stepConfig
                (Config.mk (embO q b
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state)
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape) := by
          rw [hstep2, hrec2]
        -- 驱动走一步 = 对第 n 步格局做 `stepConfig`
        have hhaltD1 : (simDrive q b (M.haltNorm).step (M.haltNorm).start).halted
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1) = false :=
          simDrive_halted_false_of_range q b (M.haltNorm).step (M.haltNorm).start
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape hrg1
        have hhaltD2 : (simDrive q b (M.haltNorm).step (M.haltNorm).start).halted
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2) = false :=
          simDrive_halted_false_of_range q b (M.haltNorm).step (M.haltNorm).start
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape hrg2
        have hstepD1 : (simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c1
            = (simDrive q b (M.haltNorm).step (M.haltNorm).start).stepConfig
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1) :=
          run_succ_last (simDrive q b (M.haltNorm).step (M.haltNorm).start) n c1 hhaltD1
        have hstepD2 : (simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c2
            = (simDrive q b (M.haltNorm).step (M.haltNorm).start).stepConfig
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2) :=
          run_succ_last (simDrive q b (M.haltNorm).step (M.haltNorm).start) n c2 hhaltD2
        -- 按第 n 步驱动状态所属的层与判定分支分类
        by_cases hin1 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.val
            < stateCount q b
        · -- 模拟层
          by_cases hacc1 : unpackM (2 ^ b) 9 15
              ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.val
              = (M.haltNorm).accept.val
          · -- 接受态：两侧都进入接受哨兵
            have hin2 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                < stateCount q b := by rw [← heqst]; exact hin1
            have hacc2 : unpackM (2 ^ b) 9 15
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                = (M.haltNorm).accept.val := by rw [← heqst]; exact hacc1
            have ha1 : ((simObs q b (M.haltNorm)).stepConfig
                (Config.mk (embO q b
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state)
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape)).state
                = obsAcc q b :=
              simObs_stepConfig_accept_state q b (M.haltNorm) _ _
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.isLt
                hin1 hacc1
            have ha2 : ((simObs q b (M.haltNorm)).stepConfig
                (Config.mk (embO q b
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state)
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape)).state
                = obsAcc q b :=
              simObs_stepConfig_accept_state q b (M.haltNorm) _ _
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.isLt
                hin2 hacc2
            have s1 : ((simObs q b (M.haltNorm)).run (n + 1)
                (Config.mk (embO q b c1.state) c1.tape)).state = obsAcc q b := by
              rw [hstep1', ha1]
            have s2 : ((simObs q b (M.haltNorm)).run (n + 1)
                (Config.mk (embO q b c2.state) c2.tape)).state = obsAcc q b := by
              rw [hstep2', ha2]
            constructor
            · rw [s1, s2]
            · intro hlt'
              exfalso
              rw [s1] at hlt'
              simp only [obsAcc, Fin.val_mk] at hlt'
              omega
          · by_cases h14 : unpackPh (2 ^ b) 9 15
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.val = 14
            · -- 相位 14：两侧都进入失败哨兵
              have hin2 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                  < stateCount q b := by rw [← heqst]; exact hin1
              have hacc2 : unpackM (2 ^ b) 9 15
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                  ≠ (M.haltNorm).accept.val := by rw [← heqst]; exact hacc1
              have h142 : unpackPh (2 ^ b) 9 15
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                  = 14 := by rw [← heqst]; exact h14
              have ha1 : ((simObs q b (M.haltNorm)).stepConfig
                  (Config.mk (embO q b
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state)
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape)).state
                  = obsFail q b :=
                simObs_stepConfig_fail_state q b (M.haltNorm) _ _
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state.isLt
                  hin1 hacc1 h14
              have ha2 : ((simObs q b (M.haltNorm)).stepConfig
                  (Config.mk (embO q b
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state)
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape)).state
                  = obsFail q b :=
                simObs_stepConfig_fail_state q b (M.haltNorm) _ _
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.isLt
                  hin2 hacc2 h142
              have s1 : ((simObs q b (M.haltNorm)).run (n + 1)
                  (Config.mk (embO q b c1.state) c1.tape)).state = obsFail q b := by
                rw [hstep1', ha1]
              have s2 : ((simObs q b (M.haltNorm)).run (n + 1)
                  (Config.mk (embO q b c2.state) c2.tape)).state = obsFail q b := by
                rw [hstep2', ha2]
              constructor
              · rw [s1, s2]
              · intro hlt'
                exfalso
                rw [s1] at hlt'
                simp only [obsFail, Fin.val_mk] at hlt'
                omega
            · -- 可委托：两侧都按驱动走一步的结果重新编码
              have hin2 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                  < stateCount q b := by rw [← heqst]; exact hin1
              have hacc2 : unpackM (2 ^ b) 9 15
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                  ≠ (M.haltNorm).accept.val := by rw [← heqst]; exact hacc1
              have h142 : unpackPh (2 ^ b) 9 15
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state.val
                  ≠ 14 := by rw [← heqst]; exact h14
              have hd1 : observeState q b (M.haltNorm)
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state :=
                ⟨hrg1, fun _ => ⟨hacc1, h14⟩⟩
              have hd2 : observeState q b (M.haltNorm)
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state :=
                ⟨hrg2, fun _ => ⟨hacc2, h142⟩⟩
              have hdel1 := simObs_stepConfig_delegate q b (M.haltNorm)
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape hd1
              have hdel2 := simObs_stepConfig_delegate q b (M.haltNorm)
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape hd2
              have hs1 : (simObs q b (M.haltNorm)).run (n + 1)
                  (Config.mk (embO q b c1.state) c1.tape)
                  = Config.mk (embO q b
                      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c1).state)
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c1).tape := by
                rw [hstep1', hdel1, ← hstepD1]
              have hs2 : (simObs q b (M.haltNorm)).run (n + 1)
                  (Config.mk (embO q b c2.state) c2.tape)
                  = Config.mk (embO q b
                      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c2).state)
                    ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c2).tape := by
                rw [hstep2', hdel2, ← hstepD2]
              constructor
              · rw [hs1, hs2, hN (n + 1) hn1]
              · intro _
                exact ⟨hs1, hs2⟩
        · -- 导航层：同样照搬驱动一步
          have hd1 : observeState q b (M.haltNorm)
              ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state :=
            ⟨hrg1, fun hv => absurd hv hin1⟩
          have hd2 : observeState q b (M.haltNorm)
              ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state :=
            ⟨hrg2, fun hv => absurd hv (by rw [← heqst]; exact hin1)⟩
          have hdel1 := simObs_stepConfig_delegate q b (M.haltNorm)
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).state
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c1).tape hd1
          have hdel2 := simObs_stepConfig_delegate q b (M.haltNorm)
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).state
            ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run n c2).tape hd2
          have hs1 : (simObs q b (M.haltNorm)).run (n + 1)
              (Config.mk (embO q b c1.state) c1.tape)
              = Config.mk (embO q b
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c1).state)
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c1).tape := by
            rw [hstep1', hdel1, ← hstepD1]
          have hs2 : (simObs q b (M.haltNorm)).run (n + 1)
              (Config.mk (embO q b c2.state) c2.tape)
              = Config.mk (embO q b
                  ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c2).state)
                ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run (n + 1) c2).tape := by
            rw [hstep2', hdel2, ← hstepD2]
          constructor
          · rw [hs1, hs2, hN (n + 1) hn1]
          · intro _
            exact ⟨hs1, hs2⟩
      · -- ---------- 情形二：第 n 步已是哨兵 ----------
        have hs2' : ¬ ((simObs q b (M.haltNorm)).run n
            (Config.mk (embO q b c2.state) c2.tape)).state.val < stateCountD q b := by
          rw [← hA]; exact hs
        have e1 : ((simObs q b (M.haltNorm)).run (n + 1)
            (Config.mk (embO q b c1.state) c1.tape)).state
            = ((simObs q b (M.haltNorm)).run n
              (Config.mk (embO q b c1.state) c1.tape)).state := by
          rw [DTM.run_add (simObs q b (M.haltNorm)) n 1]
          exact simObs_run_sentinel_state q b (M.haltNorm) 1
            ((simObs q b (M.haltNorm)).run n (Config.mk (embO q b c1.state) c1.tape)) hs
        have e2 : ((simObs q b (M.haltNorm)).run (n + 1)
            (Config.mk (embO q b c2.state) c2.tape)).state
            = ((simObs q b (M.haltNorm)).run n
              (Config.mk (embO q b c2.state) c2.tape)).state := by
          rw [DTM.run_add (simObs q b (M.haltNorm)) n 1]
          exact simObs_run_sentinel_state q b (M.haltNorm) 1
            ((simObs q b (M.haltNorm)).run n (Config.mk (embO q b c2.state) c2.tape)) hs2'
        constructor
        · rw [e1, hA, e2]
        · intro hlt'
          exfalso
          rw [e1] at hlt'
          exact hs hlt'

/-! ## 主定理 -/

/-- **观察命中与纸带尾部无关**：若两条驱动轨迹（同一驱动器、不同的初始纸带）在 `N` 步内的
    *状态* 完全一致，且两条初始驱动状态号都 `< 2 * stateCount`（非终态哨兵），
    则两条观察轨迹在 `N` 步内的状态也完全一致。

    **Observe-命中与纸带尾部无关** / **Observer states are independent of the tape tail**:
    if two driver runs (same driver, possibly different initial tapes) agree on their
    states for `N` steps and both initial driver states are in range, then their
    observer runs agree on their states for `N` steps. -/
theorem simObs_run_state_congr (q b : Nat) (M : NTM q)
    (c1 c2 : Config (stateCountD q b)) (N : Nat)
    (hr1 : c1.state.val < 2 * stateCount q b)
    (hr2 : c2.state.val < 2 * stateCount q b)
    (hN : ∀ i : Nat, i ≤ N →
      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i c1).state
      = ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i c2).state) :
    ∀ n : Nat, n ≤ N →
      ((simObs q b (M.haltNorm)).run n (Config.mk (embO q b c1.state) c1.tape)).state
      = ((simObs q b (M.haltNorm)).run n (Config.mk (embO q b c2.state) c2.tape)).state := by
  intro n hn
  exact (simObs_congr_invariant q b M c1 c2 N hr1 hr2 hN n hn).1

/-! ## `passStart` 起点的直接推论 -/

/-- `passStart` 起点的驱动状态号在模拟层，必 `< 2 * stateCount`。 -/
theorem passStart_state_val_lt (q b : Nat) (x : Reg q) (m c Z : Nat) (hm : m < q)
    (hc : c < 2 ^ b) (L : List Nat) :
    (passStart x m c hm hc Z L).state.val < 2 * stateCount q b := by
  have hlt : (passStart x m c hm hc Z L).state.val < stateCount q b := by
    simp only [passStart, embS, Fin.val_mk]
    exact (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le m) hm
  have hpos : 0 < stateCount q b := stateCount_pos q b hq
  omega

/-- **`passStart` 版观察状态一致性**：两条 `passStart` 轨迹（仅数字区 `L1`/`L2` 不同）
    的驱动状态在 `N` 步内一致，则观察状态在 `N` 步内也一致。
    `passStart` version: two pass starts differing only in the digit area have equal
    observer states as long as their driver states agree. -/
theorem simObs_states_congr_of_passStart (q b : Nat) (M : NTM q)
    (x : Reg q) (m c Z : Nat) (hm : m < q) (hc : c < 2 ^ b) (L1 L2 : List Nat) (N : Nat)
    (hN : ∀ i : Nat, i ≤ N →
      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i (passStart x m c hm hc Z L1)).state
      = ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i (passStart x m c hm hc Z L2)).state) :
    ∀ n : Nat, n ≤ N →
      ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passStart x m c hm hc Z L1).state) (passStart x m c hm hc Z L1).tape)).state
      = ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passStart x m c hm hc Z L2).state) (passStart x m c hm hc Z L2).tape)).state :=
  simObs_run_state_congr q b M
    (passStart x m c hm hc Z L1) (passStart x m c hm hc Z L2) N
    (passStart_state_val_lt q b x m c Z hm hc L1)
    (passStart_state_val_lt q b x m c Z hm hc L2)
    hN

end DTM

end Pnp
