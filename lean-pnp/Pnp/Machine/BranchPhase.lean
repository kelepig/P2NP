/-
  文件：Pnp/Machine/BranchPhase.lean
  File: Pnp/Machine/BranchPhase.lean

  主题：分支族完备性在**运行相位机** `obsPhase` 上的形式——原机在 `T` 步内接受时，
        存在轮数 `t ≤ T` 与下标 `i < B^T`，使该分支的 `obsPhase` 在统一预算内停在接受态。
        这是外层枚举器 E 接受侧（`hAcc`）可直接引用的接口。
  Topic: family completeness lifted to the run phase `obsPhase` — the exact interface E's
  accept direction can quote.

  本文件给出（#226）：
    - `obsPhase_accept_mono`：预算内接受 ⇒ 任意更大预算仍接受；
    - `exists_branch_obsPhase_accept_of_acceptsWithin`：接受 ⇒ 某分支的 `obsPhase` 在预算内接受。
  Per-branch accept at the phase-machine level.
-/

import Pnp.Machine.BranchHit
import Pnp.Machine.ObsBudget

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **接受单调**：`obsPhase` 在前 `n` 步接受，则在任意更大预算 `budget` 下仍接受。
    先经 `obsPhase_accept_iff` 回到观察机，用 `simObs_run_accept_at_budget` 延长，
    再用一次 `obsPhase_accept_iff` 搬回。
    Accept monotonicity: an accept within `n` steps persists under any larger budget. -/
theorem obsPhase_accept_mono (q b : Nat) (M : NTM q) (n budget : Nat)
    (c : Config (stateCountO q b)) (hn : n ≤ budget)
    (h : ((obsPhase q b M).run n ⟨embOb q b c.state, c.tape⟩).state
      = (obsPhase q b M).accept) :
    ((obsPhase q b M).run budget ⟨embOb q b c.state, c.tape⟩).state
      = (obsPhase q b M).accept := by
  -- 观察机在前 n 步接受
  have hS : ((simObs q b M).run n c).state = obsAcc q b :=
    (obsPhase_accept_iff q b M n c).mp h
  -- 延长到更大预算
  have hS' : ((simObs q b M).run budget c).state = obsAcc q b :=
    simObs_run_accept_at_budget q b M n budget c hn hS
  -- 搬回运行相位机
  exact (obsPhase_accept_iff q b M budget c).mpr hS'

/-- **分支族完备性（运行相位机版）**：若 `M` 在 `T` 步内接受，则存在轮数 `t ≤ T` 与
    下标 `i < B^T`，使分支族成员 `branchBlocks B t i` 的运行相位机在统一预算
    `T'·costCap + 6` 内停在接受态。
    Family completeness (phase-machine version): acceptance within `T` steps yields a family
    member whose run phase stops at the accept state within the uniform budget. -/
theorem exists_branch_obsPhase_accept_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (T' : Nat) (hTT : T ≤ T')
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
        ⟨embOb q b (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  -- 观察机侧的完备性（#141）
  obtain ⟨t, i, ht1, htT, hi, hhit⟩ :=
    exists_branch_hit_of_acceptsWithin M hB hBpos w T b hbnd hT T' hTT Z x hx hxw
      hd1 hd2 hxacc hacc
  -- 观察机命中 ⇒ 运行相位机接受
  exact ⟨t, i, ht1, htT, hi,
    (obsPhase_accept_iff q b ((M.stutter).haltNorm) _ _).mpr hhit⟩

end DTM

end Pnp
