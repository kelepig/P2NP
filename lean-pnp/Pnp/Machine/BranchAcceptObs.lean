/-
  文件：Pnp/Machine/BranchAcceptObs.lean

  主题：接受方向的分支级装配——「分支块列表前缀上的接受通路」+「尾部无关性」
        ⇒ 该分支的观察机在预算内命中 `obsAcc`。
  Topic: assembling accept-completeness at the branch level. A successful accepting pass
  over a prefix of the branch block list, plus tail-independence of the readings, makes
  the branch's observer hit `obsAcc` within the budget.

  要点：接受通路 `L = R ++ [0]` 中只有 `R` 的前 `|R|` 块参与各轮选号，最后一块只决定
  终点计数器；因此把尾部换成分支块列表 `R ++ L2` 后，驱动轨迹在前 `r.steps` 步内状态
  完全一致（`hst`），观察轨迹也随之一致（`SimObsTail`），接受命中被搬运过去。
  Key: only the first `|R|` blocks take part in the rounds; the last block only fixes the
  final counter, so replacing the tail keeps the driver states unchanged.
-/

import Pnp.Machine.BranchAccept
import Pnp.Machine.SimObsTail
import Pnp.Machine.SimBudget
import Pnp.Machine.BranchBlocks

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **分支级接受命中**：通路在 `R ++ [0]` 上成功且终态接受、驱动轨迹在前 `r.steps` 步
    与 `R ++ L2` 版本一致、预算 `K ≥ r.steps` ⇒ 分支块列表 `R ++ L2` 的观察机跑满 `K`
    步停在 `obsAcc`。
    Branch-level accept hit: an accepting pass over `R ++ [0]` transfers to the branch
    block list `R ++ L2` given state agreement of the driver runs. -/
theorem branch_obsAcc_of_pass_prefix (q b : Nat) (M : NTM q)
    (R L2 : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
    (m : Nat) (hm : m < q) (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ R ++ [0], k' + 2 < 2 ^ b)
    (hb2 : ∀ k' ∈ R ++ L2, k' + 2 < 2 ^ b)
    (r : PassRes q b)
    (hpass : passRun q b ((M.stutter).haltNorm).step Z c hc x (R ++ [0]) hb = some r)
    (hracc : r.reg.state = (M.stutter).haltNorm.accept)
    (K : Nat) (hK : r.steps ≤ K)
    (hst : ∀ j : Nat, j ≤ r.steps →
      ((simDrive q b ((M.stutter).haltNorm).step (M.stutter).haltNorm.start).run j
        (passStart x m c hm hc Z (R ++ [0]))).state
      = ((simDrive q b ((M.stutter).haltNorm).step (M.stutter).haltNorm.start).run j
        (passStart x m c hm hc Z (R ++ L2))).state) :
    ((simObs q b ((M.stutter).haltNorm)).run K
      (Config.mk (embO q b (passStart x m c hm hc Z (R ++ L2)).state)
        (passStart x m c hm hc Z (R ++ L2)).tape)).state = obsAcc q b := by
  have hLne : R ++ [0] ≠ [] := by simp
  -- 通路本身给出 `r.steps` 内的接受命中（未加尾部）
  obtain ⟨n, hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b (M.stutter) (R ++ [0]) hLne Z c hc x m hm hx
      hpre hpost hb r hpass hracc
  -- 观察状态在 `n ≤ r.steps` 处与加尾部版本一致
  have hcongr := simObs_states_congr_of_passStart q b (M.stutter) x m c Z hm hc
    (R ++ [0]) (R ++ L2) r.steps hst n hn
  -- 命中搬运到分支块列表
  have hhit2 : ((simObs q b ((M.stutter).haltNorm)).run n
      (Config.mk (embO q b (passStart x m c hm hc Z (R ++ L2)).state)
        (passStart x m c hm hc Z (R ++ L2)).tape)).state = obsAcc q b := by
    rw [← hcongr]
    simp only [obsStart] at hhit
    exact hhit
  exact simObs_run_accept_at_budget q b ((M.stutter).haltNorm) n K _ (by omega) hhit2

end DTM

end Pnp
