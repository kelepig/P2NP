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

/-- **分支级可靠性（运行相位机版）**：某分支的运行相位机在统一预算内停在接受态 ⇒
    原机 `w` 在 `T'` 步内接受。把 `obsPhase` 的关注接受经 `obsPhase_accept_iff` 换回观察机命中，
    再调 `acceptsWithin_of_branch_hit`。
    Branch soundness (phase-machine version): if a branch's run phase stops at the accept
    state within the uniform budget, then `M` accepts `w` within `T'` steps. -/
theorem acceptsWithin_of_branch_obsPhase_acc (q b B T i : Nat) (M : NTM q) (w : List Bool)
    (T' : Nat)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hAcc : ((obsPhase q b ((M.stutter).haltNorm)).run
      (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
      ⟨embOb q b (obsStart q b (M.stutter) x m c Z hm hc (branchBlocks B T i)).state,
        (obsStart q b (M.stutter) x m c Z hm hc (branchBlocks B T i)).tape⟩).state
      = (obsPhase q b ((M.stutter).haltNorm)).accept) :
    M.AcceptsWithin w T' := by
  -- 运行相位机接受 ⇒ 观察机命中（`obsPhase_accept_iff` 的从左到右）
  have hHit : ((simObs q b ((M.stutter).haltNorm)).run
      (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
      (Config.mk (embO q b (passStart x m c hm hc Z (branchBlocks B T i)).state)
        (passStart x m c hm hc Z (branchBlocks B T i)).tape)).state = obsAcc q b :=
    (obsPhase_accept_iff q b ((M.stutter).haltNorm) _
      (obsStart q b (M.stutter) x m c Z hm hc (branchBlocks B T i))).mp hAcc
  -- 观察机命中 ⇒ 原机接受（#139 的分支级可靠性）
  exact acceptsWithin_of_branch_hit q b B T i M w T' hB hb hl Z c hc x m hm hx hxM hxw
    hpre hpost hpadpost hpadpre hlen hHit

/-- **分支族完备性（运行相位机 + 统一指数预算）**：与 `exists_branch_obsPhase_accept_of_acceptsWithin`
    相同的完备性，但预算换成与 `SimBudget` 同一口径的 `2^((2·2^b+42)·(T+1))`——E 机逐分支跑满
    预算时用的正是这个数。前提只需 `x.pre.length`、`Z` 不超过 `T+1`（初始区域两侧预留 `T+1` 格）。
    Family completeness at the uniform exponential budget `2^((2·2^b+42)·(T+1))` — the budget the
    enumerator E actually runs each branch for. Only `x.pre.length` and `Z` must fit in `T+1`. -/
theorem exists_branch_obsPhase_accept_two_pow_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hpre : x.pre.length ≤ T + 1) (hZ : Z ≤ T + 1)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run (2 ^ ((2 * 2 ^ b + 42) * (T + 1)))
        ⟨embOb q b (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  -- 1. 接受 ⇒ 某分支通路成功且终态接受
  obtain ⟨t, i, r, ht1, htT, hi, hpass, hracc⟩ :=
    exists_pass_branchBlocks_of_acceptsWithin M hB hBpos w T b hbnd hT Z x hx hxw
      hd1 hd2 hxacc hacc
  have htpos : 0 < t := by omega
  -- 2. 块表非空
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
  -- 4. 通路步数不超过统一指数预算（#130 的全局 `T` 版）
  have hblen : (branchBlocks B t i).length ≤ T + 1 := by
    rw [branchBlocks_length B t i htpos]
    omega
  have hsteps := passRun_steps_le_two_pow_T q b (T + 1) ((M.stutter).haltNorm).step
    Z (seqHead B T i) (seqHead_lt_pow B t i b hBpos hbnd) x (branchBlocks B t i)
    (branchBlocks_hb B t i b hBpos hbnd) hpre hZ hblen r hpass
  -- 5. 命中延长到统一预算
  have hbud : n ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) := Nat.le_trans hn hsteps
  have hhit2 := simObs_run_accept_at_budget q b ((M.stutter).haltNorm) n
    (2 ^ ((2 * 2 ^ b + 42) * (T + 1))) _ hbud hhit
  -- 6. 观察机命中 ⇒ 运行相位机接受
  exact ⟨t, i, ht1, htT, hi,
    (obsPhase_accept_iff q b ((M.stutter).haltNorm) _ _).mpr hhit2⟩

end DTM

end Pnp
