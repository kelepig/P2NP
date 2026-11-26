/-
  文件：Pnp/Machine/ObsBudget.lean
  File: Pnp/Machine/ObsBudget.lean

  主题：把「单分支预算判定」（`SimBudget`）搬到外层枚举器可用的**运行相位机**
        `obsPhase` 上：通路成功 + 终态接受 ⇒ 运行相位机在统一预算内停在接受态；
        观察机预算内不命中接受 ⇒ 运行相位机同样不接受。
  Topic: lifting `SimBudget`'s per-branch budget verdicts to the enumeration run phase
  `obsPhase` — accept composes with a successful accepting pass, and non-acceptance transfers.

  本文件给出（#225）：
    - `obsPhase_accepts_at_budget_of_passRun_accept`：成功通路 + 终态接受 ⇒ 接受（预算版）；
    - `obsPhase_not_accept_at_budget_of_simObs_no_acc`：观察机不命中 ⇒ 不接受（反驳形式）。
  Per-branch accept and reject bridges for the run phase.
-/

import Pnp.Machine.ObsPhase
import Pnp.Machine.SimBudget
import Pnp.Machine.Locality

namespace Pnp

namespace DTM

/-- **单分支接受（预算版，运行相位机）**：成功通路 + 终态接受 ⇒ `obsPhase` 在统一预算
    `2^((2·2^b+42)·T)` 内停在接受态。
    Per-branch accept: a successful pass ending in the accept state drives `obsPhase` to its
    accept state within the uniform budget. -/
theorem obsPhase_accepts_at_budget_of_passRun_accept (q b T : Nat) (M : NTM q)
    (L : List Nat) (hLne : L ≠ []) (hL : L.length ≤ T)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre' : ∀ p0 ∈ x.pre, p0.2 = false) (hpost' : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpre : x.pre.length ≤ T) (hZ : Z ≤ T)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hracc : r.reg.state = (M.haltNorm).accept) :
    ((obsPhase q b (M.haltNorm)).run (2 ^ ((2 * 2 ^ b + 42) * T))
        ⟨embOb q b (obsStart q b M x m c Z hm hc L).state,
          (obsStart q b M x m c Z hm hc L).tape⟩).state
      = (obsPhase q b (M.haltNorm)).accept := by
  -- 观察机在预算末端命中接受哨兵
  have hacc : ((simObs q b (M.haltNorm)).run (2 ^ ((2 * 2 ^ b + 42) * T))
      (obsStart q b M x m c Z hm hc L)).state = obsAcc q b :=
    obsAcc_at_budget_of_passRun_accept q b T M L hLne hL Z c hc x m hm hx
      hpre' hpost' hb hpre hZ r hpass hracc
  -- 接受等价把结论搬到运行相位机
  exact (obsPhase_accept_iff q b (M.haltNorm) _ _).mpr hacc

/-- **单分支不接受（预算版，运行相位机）**：观察机跑满 `K` 步不在接受哨兵 ⇒
    `obsPhase` 跑满 `K` 步不在接受态。
    Per-branch reject: if `simObs` is not at the accept sentinel after `K` steps, `obsPhase`
    is not at its accept state either. -/
theorem obsPhase_not_accept_at_budget_of_simObs_no_acc (q b K : Nat) (M : NTM q)
    (c : Config (stateCountO q b))
    (h : ((simObs q b M).run K c).state ≠ obsAcc q b) :
    ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state
      ≠ (obsPhase q b M).accept := by
  intro hacc
  exact h ((obsPhase_accept_iff q b M K c).mp hacc)

/-- **逐点不接受可搬运**：观察机在 `K` 步内从不命中接受哨兵 ⇒ 运行相位机在这 `K` 步内
    从不接受（`obsPhase_accept_iff` 逐点搬运）。
    Pointwise non-acceptance transfers: if `simObs` never hits the accept sentinel up to `K`,
    `obsPhase` never accepts up to `K`. -/
theorem obsPhase_no_accept_upto_of_simObs (q b K : Nat) (M : NTM q)
    (c : Config (stateCountO q b))
    (h : ∀ j, j ≤ K → ((simObs q b M).run j c).state ≠ obsAcc q b) :
    ∀ j, j ≤ K →
      ((obsPhase q b M).run j ⟨embOb q b c.state, c.tape⟩).state
        ≠ (obsPhase q b M).accept := by
  intro j hj hacc
  exact h j hj ((obsPhase_accept_iff q b M j c).mp hacc)

/-- **左副本绝缘下的接受判定搬运**：实际纸带只在理想纸带远端左侧多一段尾巴，且运行相位机
    从不「左端为空还左移」⇒ 两条运行的接受判定完全相同。E 机把输入副本挂在远端左侧后，
    判定语义由本引理搬运。
    Verdict transfer under left-tail insulation for the run phase machine. -/
theorem obsPhase_accept_iff_of_padLeft (q b K : Nat) (M : NTM q)
    (c1 c2 : Config (stateCountO q b + 1)) (hs : c1.state = c2.state)
    (hP : Tape.PadLeft c1.tape c2.tape)
    (hok : ∀ j, j < K → ((obsPhase q b M).run j c1).tape.left = [] →
      ((obsPhase q b M).step ((obsPhase q b M).run j c1).state
        ((obsPhase q b M).run j c1).tape.read).2.2 ≠ Dir.left) :
    ((obsPhase q b M).run K c2).state = (obsPhase q b M).accept
      ↔ ((obsPhase q b M).run K c1).state = (obsPhase q b M).accept := by
  have h := DTM.run_state_eq_of_padLeft' (obsPhase q b M) K c1 c2 hs hP hok
  rw [h]

end DTM

end Pnp
