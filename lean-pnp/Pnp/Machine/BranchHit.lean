/-
  文件：Pnp/Machine/BranchHit.lean
  File: Pnp/Machine/BranchHit.lean

  主题：接受方向的分支族完备性——原机在 `T` 步内接受 ⇒ 分支族 `branchBlocks B t i`
        （`1 ≤ t ≤ T`、`i < B^T`）中存在一支，其观察机在统一预算内命中 `obsAcc`。
  Topic: branch-family completeness for the accept direction. Acceptance within `T`
  steps makes some family member's observer hit `obsAcc` within the uniform budget.

  设计说明（auto-run-log #141）：分支族按「轮数 `t` 与下标 `i`」双参数枚举，而不是固定
  `t = T`。这样接受命中所用的通路与写进纸带的块表**完全相同**（`branchBlocks B t i`），
  无需证明「尾部替换下驱动状态不变」；代价是分支数乘上 `T + 1`，仍是 2 的指数级。
  Design (#141): the family is indexed by both the round count `t` and the index `i`, so the
  accepting pass runs on exactly the tape that is written down; no tape-tail stability is
  needed. The price is a factor `T + 1` in the branch count, still exponential.

  本文件给出：
    - `exists_branch_hit_of_acceptsWithin`：完备性（接受 ⇒ 某分支命中）；
    - 可靠性由 `BranchReject.acceptsWithin_of_branch_hit` 逐分支调用（命中 ⇒ 接受）。
  This file provides the completeness direction; soundness is the existing per-branch verdict.
-/

import Pnp.Machine.BranchAccept
import Pnp.Machine.BranchReject
import Pnp.Machine.SimBudget

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **分支族完备性**：若 `M` 在 `T` 步内接受，则存在轮数 `t ≤ T` 与下标 `i < B^T`，
    使分支族成员 `branchBlocks B t i` 的观察机在统一预算 `T'·costCap + 6` 内命中 `obsAcc`。
    Family completeness: acceptance within `T` steps yields a family member whose observer
    hits `obsAcc` within the uniform budget. -/
theorem exists_branch_hit_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (T' : Nat) (hTT : T ≤ T')
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((simObs q b ((M.stutter).haltNorm)).run
        (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
        (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i))).state = obsAcc q b := by
  -- 1. 接受 ⇒ 分支族中某成员的通路成功且终态为接受
  obtain ⟨t, i, r, ht1, htT, hi, hpass, hracc⟩ :=
    exists_pass_branchBlocks_of_acceptsWithin M hB hBpos w T b hbnd hT Z x hx hxw
      hd1 hd2 hxacc hacc
  have htpos : 0 < t := by omega
  -- 2. 块表非空（至少一轮）
  have hne : branchBlocks B t i ≠ [] := by
    intro h
    have hlen := branchBlocks_length B t i htpos
    rw [h, List.length_nil] at hlen
    omega
  -- 3. 通路终态接受 ⇒ 观察机在 `r.steps` 内命中
  obtain ⟨n, hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b (M.stutter) (branchBlocks B t i) hne
      Z (seqHead B T i) (seqHead_lt_pow B t i b hBpos hbnd) x x.state.val x.state.isLt
      rfl hx.1 hx.2 (branchBlocks_hb B t i b hBpos hbnd) r hpass hracc
  -- 4. 命中在统一预算内（块数 ≤ T ≤ T'）
  have hblen : (branchBlocks B t i).length ≤ T' := by
    rw [branchBlocks_length B t i htpos]
    omega
  have hsteps := passRun_steps_le_uniform q b ((M.stutter).haltNorm).step Z (seqHead B T i)
    (seqHead_lt_pow B t i b hBpos hbnd) x (branchBlocks B t i)
    (branchBlocks_hb B t i b hBpos hbnd) r hpass T' hblen
  exact ⟨t, i, ht1, htT, hi,
    simObs_run_accept_at_budget q b ((M.stutter).haltNorm) n _ _ (by omega) hhit⟩

/-- **分支族完备性（显式命中时刻版）**：与 `exists_branch_hit_of_acceptsWithin` 同条件，
    但额外输出**命中时刻 `n` 及其多项式上界**（`n ≤ T'·costCap + 6`）。
    E 机把这一时刻当作冻结时刻：右侧预留覆盖到 `n` 即可用
    `run_accept_eq_at_budget_of_right_append` 把判据搬到实际纸带。
    Same as the completeness lemma, but exposing the hit time `n` and its polynomial bound, so
    E can use `n` as the freeze time for the right-tail verdict transfer. -/
theorem exists_branch_hit_time_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (T' : Nat) (hTT : T ≤ T')
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i n : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      n ≤ T' * costCap x.pre.length Z T' (2 ^ b) + 6 ∧
      ((simObs q b ((M.stutter).haltNorm)).run n
        (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i))).state = obsAcc q b := by
  obtain ⟨t, i, r, ht1, htT, hi, hpass, hracc⟩ :=
    exists_pass_branchBlocks_of_acceptsWithin M hB hBpos w T b hbnd hT Z x hx hxw
      hd1 hd2 hxacc hacc
  have htpos : 0 < t := by omega
  have hne : branchBlocks B t i ≠ [] := by
    intro h
    have hlen := branchBlocks_length B t i htpos
    rw [h, List.length_nil] at hlen
    omega
  obtain ⟨n, hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b (M.stutter) (branchBlocks B t i) hne
      Z (seqHead B T i) (seqHead_lt_pow B t i b hBpos hbnd) x x.state.val x.state.isLt
      rfl hx.1 hx.2 (branchBlocks_hb B t i b hBpos hbnd) r hpass hracc
  have hblen : (branchBlocks B t i).length ≤ T' := by
    rw [branchBlocks_length B t i htpos]
    omega
  have hsteps := passRun_steps_le_uniform q b ((M.stutter).haltNorm).step Z (seqHead B T i)
    (seqHead_lt_pow B t i b hBpos hbnd) x (branchBlocks B t i)
    (branchBlocks_hb B t i b hBpos hbnd) r hpass T' hblen
  exact ⟨t, i, n, ht1, htT, hi, by omega, hhit⟩

end DTM

end Pnp
