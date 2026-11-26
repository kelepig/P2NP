/-
  文件：Pnp/Machine/SimExhaustObs.lean
  File: Pnp/Machine/SimExhaustObs.lean

  主题：耗尽轮在观察层的收口——通路成功且下一步查表有候选动作时，驱动器多模拟一步
        后在空数字区转入相位 14，观察机因此在终点后一步落入 `obsFail` 并保持到预算末。
  Topic: the observer-level exhaustion verdict. When a passing branch still has a rule for
  its next step, the driver performs that extra simulated step, hits phase 14 on the empty
  digit area, and the observer falls into `obsFail` right after the end and stays there.

  用途：这是拒绝方向「分支终止」判据的第三种情形（另外两种是通路中途查表失败与
  成功后原地停机），三种情形合起来覆盖所有分支，保证每条分支在预算内落到哨兵。
  Use: third termination case for rejecting branches (besides mid-pass failure and the
  stuck halting reject state); together they cover all branch shapes.

  本文件给出：
    - `simObs_budget_fail_of_passEnd_exhaust_gen`：给定耗尽轮的终点等式与读数，
      观察机在任意 `≥ N+1` 的预算末态都是 `obsFail`；
    - `simObs_budget_fail_of_passEnd_exhaust_{stay,right,left}`：三个移动方向的实例；
    - `simObs_no_accept_budget_of_passEnd_exhaust_*`：预算内从不接受（供枚举判定用）。
  This file provides the generic exhaustion verdict plus its three move-direction
  instances and the "never accepts within the budget" corollaries.
-/

import Pnp.Machine.SimObsRun
import Pnp.Machine.SimBudget

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **耗尽轮 ⇒ 预算末态失败（一般形）**：若驱动层从 `passEnd` 出发跑 `N` 步后到达
    模拟层相位 14（读数为 `m'`），且 `m'` 不是接受态，则观察机在任意预算 `≥ N + 1`
    的末态都是 `obsFail`。
    Generic verdict: an exhaustion round ending in phase 14 with a non-accepting reading
    makes the observer sit in `obsFail` at the end of any budget `≥ N + 1`. -/
theorem simObs_budget_fail_of_passEnd_exhaust_gen (q b : Nat) (M : NTM q) (r : PassRes q b)
    (N : Nat) (T : Tape) (m' : Fin q)
    (hrun : (simDrive q b (M.haltNorm).step M.start).run N (passEnd r) =
      Config.mk (embS (codeState q b m'.val 0 0 14 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide))) T)
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat) (hbud : N + 1 ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state = obsFail q b := by
  -- 起点在范围内（`passEnd` 是模拟层嵌入）
  have h0 : (passEnd r).state.val < 2 * stateCount q b := by
    simpa only [passEnd] using embS_range (codeState q b r.reg.state.val r.c 0 0
      r.reg.state.isLt r.hc (by decide) (by decide))
  -- 终点的读数不是接受态
  have haccv : m'.val ≠ M.accept.val := fun h => hacc (Fin.ext h)
  have hNend : driveM q b ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state
      ≠ M.accept.val := by
    rw [hrun]
    change driveM q b (embS (codeState q b m'.val 0 0 14 m'.isLt (Nat.two_pow_pos b)
      (by decide) (by decide))) ≠ M.accept.val
    rw [driveM_embS, codeState_unpackM]
    exact haccv
  -- 终点仍在模拟层
  have hltend : ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state.val
      < stateCount q b := by
    rw [hrun]
    simpa only [embS, Fin.val_mk] using (codeState q b m'.val 0 0 14 m'.isLt
      (Nat.two_pow_pos b) (by decide) (by decide)).isLt
  -- 全程读数非接受、全程在范围内 ⇒ 观察机委托直到失败
  have hne := simDrive_run_driveM_ne_accept q b M (passEnd r) h0 N hNend
  have hrg : ∀ i : Nat, i ≤ N →
      ((simDrive q b (M.haltNorm).step M.start).run i (passEnd r)).state.val
        < 2 * stateCount q b :=
    fun i _ => simDrive_run_range q b (M.haltNorm).step M.start i (passEnd r) h0
  rcases simObs_run_delegate_until_fail q b M N (passEnd r) hne hrg with hdel | hfail
  · -- 第 `N` 步仍是委托形态：终点是相位 14 ⇒ 下一步进 `obsFail`
    have hstO : ((simObs q b (M.haltNorm)).run N
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state
        = embO q b ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state :=
      congrArg Config.state hdel
    have hreading : unpackM (2 ^ b) 9 15
        ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state.val
        ≠ M.accept.val := by
      have h := hne N (Nat.le_refl N)
      rwa [driveM, ite_eq_left hltend] at h
    have h14 : unpackPh (2 ^ b) 9 15
        ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state.val = 14 := by
      rw [hrun]
      simpa only [embS, Fin.val_mk] using codeState_unpackPh q b m'.val 0 0 14 m'.isLt
        (Nat.two_pow_pos b) (by decide) (by decide)
    have hfail1 : ((simObs q b (M.haltNorm)).run (N + 1)
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state = obsFail q b := by
      have := simObs_phase14_fail_persists q b (M.haltNorm) N 0
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)
        (embO q b ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state)
        hstO ((simDrive q b (M.haltNorm).step M.start).run N (passEnd r)).state.isLt
        hltend hreading h14
      simpa using this
    rw [show budget = (N + 1) + (budget - (N + 1)) from by omega]
    exact simObs_run_fail_persists q b (M.haltNorm) (N + 1) (budget - (N + 1)) _ hfail1
  · -- 已经失败：保持到预算末
    rw [show budget = N + (budget - N) from by omega]
    exact simObs_run_fail_persists q b (M.haltNorm) N (budget - N) _ hfail

/-- **耗尽轮（原地）⇒ 预算末态失败**：通路停在 `passEnd` 后还有候选动作（原地），
    驱动器再模拟一步后转入相位 14；观察机在预算 `≥ N+1` 处为 `obsFail`。
    Exhaustion after a stay pass: the observer sits in `obsFail` at the budget end. -/
theorem simObs_budget_fail_of_passEnd_exhaust_stay (q b : Nat) (M : NTM q) (r : PassRes q b)
    (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.stay))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : 18 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + r.z ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state = obsFail q b := by
  obtain ⟨T, hrun⟩ :=
    simDrive_passEnd_exhaust_stay q b (M.haltNorm).step (M.haltNorm).start r m' s' hpk
  exact simObs_budget_fail_of_passEnd_exhaust_gen q b M r _ T m' hrun hacc budget (by omega)

/-- **耗尽轮（右移）⇒ 预算末态失败**。Exhaustion after a right-moving pass. -/
theorem simObs_budget_fail_of_passEnd_exhaust_right (q b : Nat) (M : NTM q) (r : PassRes q b)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : r.reg.post = p :: post') (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.right))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : 18 + (codeFst p.1 :: List.reverse (codeCells (r.reg.pre ++ [(s', false)]))).length
      + r.z ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state = obsFail q b := by
  obtain ⟨T, hrun⟩ :=
    simDrive_passEnd_exhaust_right q b (M.haltNorm).step (M.haltNorm).start r p post' hp hpost
      m' s' hpk
  exact simObs_budget_fail_of_passEnd_exhaust_gen q b M r _ T m' hrun hacc budget (by omega)

/-- **耗尽轮（左移）⇒ 预算末态失败**。Exhaustion after a left-moving pass. -/
theorem simObs_budget_fail_of_passEnd_exhaust_left (q b : Nat) (M : NTM q) (r : PassRes q b)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hpre : r.reg.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.left))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : 18 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + r.z ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state = obsFail q b := by
  obtain ⟨T, hrun⟩ :=
    simDrive_passEnd_exhaust_left q b (M.haltNorm).step (M.haltNorm).start r cq pre' hq hpre
      m' s' hpk
  exact simObs_budget_fail_of_passEnd_exhaust_gen q b M r _ T m' hrun hacc budget (by omega)

/-- **耗尽轮（原地）⇒ 预算内从不接受**。Never accepts within the budget (stay). -/
theorem simObs_no_accept_budget_of_passEnd_exhaust_stay (q b : Nat) (M : NTM q)
    (r : PassRes q b) (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.stay))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : 18 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + r.z ≤ budget) :
    ∀ n : Nat, n ≤ budget →
      ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state ≠ obsAcc q b := by
  refine simObs_no_accept_of_final_not q b (M.haltNorm) budget _ ?_
  rw [simObs_budget_fail_of_passEnd_exhaust_stay q b M r m' s' hpk hacc budget hbud]
  intro hh
  have hv := congrArg Fin.val hh
  simp only [obsFail, obsAcc, Fin.val_mk] at hv
  omega

/-- **耗尽轮（右移）⇒ 预算内从不接受**。Never accepts within the budget (right). -/
theorem simObs_no_accept_budget_of_passEnd_exhaust_right (q b : Nat) (M : NTM q)
    (r : PassRes q b) (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : r.reg.post = p :: post') (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.right))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : 18 + (codeFst p.1 :: List.reverse (codeCells (r.reg.pre ++ [(s', false)]))).length
      + r.z ≤ budget) :
    ∀ n : Nat, n ≤ budget →
      ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state ≠ obsAcc q b := by
  refine simObs_no_accept_of_final_not q b (M.haltNorm) budget _ ?_
  rw [simObs_budget_fail_of_passEnd_exhaust_right q b M r p post' hp hpost m' s' hpk hacc
    budget hbud]
  intro hh
  have hv := congrArg Fin.val hh
  simp only [obsFail, obsAcc, Fin.val_mk] at hv
  omega

/-- **耗尽轮（左移）⇒ 预算内从不接受**。Never accepts within the budget (left). -/
theorem simObs_no_accept_budget_of_passEnd_exhaust_left (q b : Nat) (M : NTM q)
    (r : PassRes q b) (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hpre : r.reg.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.left))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : 18 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + r.z ≤ budget) :
    ∀ n : Nat, n ≤ budget →
      ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state ≠ obsAcc q b := by
  refine simObs_no_accept_of_final_not q b (M.haltNorm) budget _ ?_
  rw [simObs_budget_fail_of_passEnd_exhaust_left q b M r cq pre' hq hpre m' s' hpk hacc
    budget hbud]
  intro hh
  have hv := congrArg Fin.val hh
  simp only [obsFail, obsAcc, Fin.val_mk] at hv
  omega

end DTM

end Pnp
