/-
  文件：Pnp/Machine/EnumSpec.lean
  File: Pnp/Machine/EnumSpec.lean

  主题：外层枚举器的**规格层**——把「逐分支跑观察机、任一命中即接受」写成纯数据函数，
        并证明它恰好判定 `AcceptsWithin`。
  Topic: the specification layer of the outer enumerator. The branch sweep is written as a
  pure Boolean function over the branch family, and proved to accept exactly `AcceptsWithin`.

  说明：#141 把分支族定为 `(t, i)` 双参数（`branchBlocks B t i`，`1 ≤ t ≤ T`、
  `i < B^T`）。本文件给出族列表 `branchList`、族扫描 `anyBranchHit`，以及
  **`anyBranchHit_iff_acceptsWithin`**：在统一预算 `T·costCap+6` 下扫描命中 ⇔ 原机在
  `T` 步内接受。之后机器层义务 = 实现 `anyBranchHit` 并在指数步内停机。
  Note (#141): the family is indexed by both the round count `t` and the index `i`; this
  file gives the family list, the sweep, and its exact semantics. The remaining machine
  obligation is to implement the sweep within the exponential budget.
-/

import Pnp.Machine.BranchHit
import Pnp.Machine.SimBudget

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **分支族列表**：全部 `(t, i)`，`t = 1 … T`、`i < B^T`。
    The branch family as a list of pairs. -/
def branchList (B T : Nat) : List (Nat × Nat) :=
  (List.range T).flatMap (fun t => (List.range (B ^ T)).map (fun i => (t + 1, i)))

/-- 分支族成员关系：`(t, i)` 在族中 ⇔ `1 ≤ t ≤ T` 且 `i < B^T`。
    Membership in the branch family. -/
theorem mem_branchList (B T t i : Nat) :
    (t, i) ∈ branchList B T ↔ 1 ≤ t ∧ t ≤ T ∧ i < B ^ T := by
  simp only [branchList, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨t0, ht0, i0, hi0, hteq, hieq⟩
    subst hteq hieq
    exact ⟨Nat.succ_le_succ (Nat.zero_le t0), Nat.succ_le_of_lt ht0, hi0⟩
  · rintro ⟨ht1, htT, hi⟩
    refine ⟨t - 1, by omega, i, hi, by omega, rfl⟩

/-- **分支族扫描**：逐一检查每个族成员的观察机是否在预算 `K` 内停在 `obsAcc`。
    The sweep: check every family member for an `obsAcc` hit within the budget. -/
def anyBranchHit (q b B T K : Nat) (M : NTM q) (hBpos : 0 < B) (hbnd : B + 2 < 2 ^ b)
    (x : Reg q) (Z : Nat) : Bool :=
  (branchList B T).any (fun p =>
    decide (((simObs q b ((M.stutter).haltNorm)).run K
      (obsStart q b (M.stutter) x x.state.val (seqHead B T p.2) Z x.state.isLt
        (seqHead_lt_pow B p.1 p.2 b hBpos hbnd)
        (branchBlocks B p.1 p.2))).state = obsAcc q b))

/-- **扫描的语义**：在统一预算 `T·costCap+6` 下，族扫描命中 ⇔ 原机在 `T` 步内接受。
    Sweep semantics at the uniform budget: a hit in the family is equivalent to acceptance
    within `T` steps. -/
theorem anyBranchHit_iff_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T + 1 ≤ x.pre.length) (hd2 : T + 1 ≤ x.post.length)
    (hxacc : x.state ≠ M.accept) :
    anyBranchHit q b B T (T * costCap x.pre.length Z T (2 ^ b) + 6) M hBpos hbnd x Z = true
      ↔ M.AcceptsWithin w T := by
  constructor
  · -- 命中 ⇒ 接受（逐分支可靠性的逆否）
    intro h
    rw [anyBranchHit, List.any_eq_true] at h
    obtain ⟨⟨t, i⟩, hmem, hdec⟩ := h
    obtain ⟨ht1, htT, hi⟩ := (mem_branchList B T t i).mp hmem
    have hact : ((simObs q b ((M.stutter).haltNorm)).run
        (T * costCap x.pre.length Z T (2 ^ b) + 6)
        (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i))).state = obsAcc q b :=
      of_decide_eq_true hdec
    have hlen : (branchBlocks B t i).length ≤ T := by
      rw [branchBlocks_length B t i (by omega : 0 < t)]
      exact htT
    exact acceptsWithin_of_branch_hit q b B t i M w T hBpos hbnd
      (stutter_step_length_le M B hB) Z (seqHead B T i) (seqHead_lt_pow B t i b hBpos hbnd)
      x x.state.val x.state.isLt rfl hx hxw hx.1 hx.2
      (by rw [branchBlocks_length B t i (by omega : 0 < t)]; omega)
      (by rw [branchBlocks_length B t i (by omega : 0 < t)]; omega) hlen hact
  · -- 接受 ⇒ 命中（分支族完备性）
    intro hacc
    obtain ⟨t, i, ht1, htT, hi, hhit⟩ :=
      exists_branch_hit_of_acceptsWithin M hB hBpos w T b hbnd hT T (Nat.le_refl T) Z x hx
        hxw (by omega) (by omega) hxacc hacc
    rw [anyBranchHit, List.any_eq_true]
    exact ⟨(t, i), (mem_branchList B T t i).mpr ⟨ht1, htT, hi⟩, by
      simp only [decide_eq_true_eq]
      exact hhit⟩

/-- **扫描语义（预留形态）**：初始区域取 `initReg M.start w (T+1) (T+1)`（两侧各预留
    `T+1` 格空白）时，族扫描命中 ⇔ 原机在 `T` 步内接受。所有前提均可满足，是外层
    机器要实现的判定接口。
    Sweep semantics for the concrete padded initial region; every premise is satisfiable. -/
theorem anyBranchHit_iff_acceptsWithin_pad {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (hstart : M.start ≠ M.accept) :
    anyBranchHit q b B T (T * costCap (T + 1) Z T (2 ^ b) + 6) M hBpos hbnd
        (Reg.initReg M.start w (T + 1) (T + 1)) Z = true
      ↔ M.AcceptsWithin w T := by
  -- 预留区域的三项前提：前长恰为 `T+1`、后长 ≥ `T+1`、与初始格局语义相同
  have hpre : (Reg.initReg M.start w (T + 1) (T + 1)).pre.length = T + 1 := by
    simp [Reg.initReg]
  have hpost : T + 1 ≤ (Reg.initReg M.start w (T + 1) (T + 1)).post.length := by
    simp only [Reg.initReg, List.length_append, List.length_map, List.length_drop,
      List.length_replicate]
    omega
  have hxw : CfgEquiv (Reg.initReg M.start w (T + 1) (T + 1)).toConfig (M.init w) :=
    ⟨rfl, Or.inl (Reg.initReg_sameInf M.start w (T + 1) (T + 1))⟩
  have hxacc : (Reg.initReg M.start w (T + 1) (T + 1)).state ≠ M.accept := hstart
  have h := anyBranchHit_iff_acceptsWithin M hB hBpos w T b hbnd hT Z
    (Reg.initReg M.start w (T + 1) (T + 1)) (Reg.initReg_markersOK _ _ _ _) hxw
    (by omega) hpost hxacc
  simpa only [hpre] using h

end DTM

end Pnp
