/-
  文件：Pnp/Machine/SimHitRange.lean
  主题：`observeState` 的区间版——通路只在「前 `N` 步」（`N ≤ r.steps`）内可观察时，
        也能断言这 `N` 步的驱动状态满足 `observeState`。

  `simObs_pass_obs`（SimDecide）要求「整条通路内无接受态」，而反向完备性只需要
  「末轮第 5 步之前无接受态」；本文件把结论与前提里的 `r.steps` 换成任意 `N ≤ r.steps`。
  阶段 14 的排除仍用整条通路的终点（`passEnd` 相位 0）。

  Range-limited observability: the same argument as `simObs_pass_obs`, but only up to
  an arbitrary bound `N ≤ r.steps`.
-/

import Pnp.Machine.SimPassAppend

namespace Pnp

namespace DTM

/-- **区间版可观察性**：通路成功且前 `N` 步内无接受态 ⇒ 这 `N` 步的驱动状态都可观察。
    Observability up to `N ≤ r.steps` on a successful pass without interior accepts. -/
theorem simObs_pass_obs_upto (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b M.step Z c hc x L hb = some r)
    (N : Nat) (hN : N ≤ r.steps)
    (hnoacc : ∀ i : Nat, i < N →
      ∀ (h : ((simDrive q b M.step M.start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b M.step M.start).run i
            (passStart x m c hm hc Z L)).state.val ≠ M.accept.val) :
    ∀ i : Nat, i < N →
      observeState q b M ((simDrive q b M.step M.start).run i
        (passStart x m c hm hc Z L)).state := by
  intro i hi
  have hrun := simDrive_pass q b M.step M.start L Z c hc x m hm hx hpre hpost hb r hpass
  constructor
  · -- 状态范围
    have h0 : (passStart x m c hm hc Z L).state.val < 2 * stateCount q b := by
      have := passStart_state_lt q b x m c hm hc Z L
      omega
    exact simDrive_run_range q b M.step M.start i (passStart x m c hm hc Z L) h0
  · -- 非接受、非阶段 14
    intro hlt
    constructor
    · exact hnoacc i hi hlt
    · -- 阶段 14 是死点，会与终点阶段 0 矛盾（终点取自整条通路）
      intro h14
      have hstuck := simDrive_run_phase14_state q b M.step M.start
        (passStart x m c hm hc Z L) ⟨_, hlt⟩ i rfl h14 (r.steps - i)
      rw [show i + (r.steps - i) = r.steps from by omega, hrun] at hstuck
      have hp0 := passEnd_unpackPh q b r
      rw [hstuck] at hp0
      simp only [embS, Fin.val_mk] at hp0
      rw [h14] at hp0
      omega

end DTM

end Pnp
