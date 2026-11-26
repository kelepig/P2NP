/-
  文件：Pnp/Machine/SimAcceptComplete.lean
  主题：把「原机在 T 步内接受」整条翻成「存在一条成功通路，终态区域为接受态」。

  链路（承接 auto-run-log #117 的语义部分）：
    `M.AcceptsWithin w T`
      --acceptsWithin_iff_exists_index-->  ∃ i < B^T，`M.runWith T (seqOfIndex B T i) = some c`，`c` 接受；
      --stutter（索引整体 +1）-->          `M.stutter.runWith T (σ) = some c`，`σ` 各项 ∈ [1, B]；
      --exists_stepNs_accept_of_runWith_mem--> 计数迭代 `stepNs (M.stutter) t τ x` 停在接受态；
      --exists_passRun_accept_of_stepNs_bounded-->  成功通路 `passRun`，终态区域接受。

  之所以先经 `seqOfIndex`：它保证选择序列每一项都 < B，从而使 stutter 后的每一项
  都落在「≥1 且加 1 后仍 < 2^b」的范围内（前提 `B + 2 < 2 ^ b`）。

  Whole accept bridge: `M` accepts within `T` iff some successful pass over the stutter
  machine (all choices ≥ 1 and bounded) ends in the accepting state.
-/

import Pnp.Machine.SimPassComplete
import Pnp.Machine.Stutter
import Pnp.IndexedSimulation
import Pnp.Machine.PadInv

namespace Pnp

namespace DTM

/-- **接受方向总桥**：若 `M` 在 `T` 步内接受输入 `w`，且模拟区起点 `x` 与 `M.init w`
    逐字一致、两侧空白足够（`T ≤ pre/post` 长度），则在占位机 `M.stutter` 的规范形下，
    存在一条成功通路，其终态区域为接受态。
    Whole accept bridge from `AcceptsWithin` to a successful accepting pass. -/
theorem exists_passRun_accept_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T : Nat) (b : Nat) (hbnd : B + 2 < 2 ^ b)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hacc : M.AcceptsWithin w T) :
    ∃ (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (c : Nat) (hc : c < 2 ^ b)
      (r : PassRes q b),
      passRun q b (M.stutter.haltNorm).step Z c hc x L hb = some r ∧
        r.reg.state = M.accept := by
  -- 计数器下标形态的接受语义：给出 `seqOfIndex` 解码后的接受运行
  obtain ⟨i, _hi, c, hrun, haccC⟩ :=
    (acceptsWithin_iff_exists_index hB hBpos w T).mp hacc
  -- 转到占位机：选择索引整体 +1，每一项都落进 [1, B]
  have hrunS : (M.stutter).runWith T ((seqOfIndex B T i).map (fun y => y + 1))
      (M.init w) = some c := by
    rw [NTM.stutter_runWith]
    exact hrun
  -- 空白预留不改变运行：把 `M.init w` 侧的成功运行搬到区域侧
  obtain ⟨c2, hrunx, hst⟩ :=
    NTM.runWith_cfgEquiv (M.stutter) T _ hxw.symm c hrunS
  have haccS : c2.state = (M.stutter).accept := by rw [← hst]; exact haccC
  -- 计数迭代找到停在接受态的前缀
  obtain ⟨t, τ, z, _htT, _hlen, hmem, hstepNs, haccZ, _⟩ :=
    exists_stepNs_accept_of_runWith_mem (M.stutter) T
      ((seqOfIndex B T i).map (fun y => y + 1)) x c2 hx hd1 hd2 hrunx haccS
  -- 每项 ≥ 1 且加 1 后 < 2^b（由 `seqOfIndex` 的界 `d < B` 与 `B + 2 < 2^b`）
  have hAll : ∀ a ∈ (seqOfIndex B T i).map (fun y => y + 1), 1 ≤ a ∧ a + 1 < 2 ^ b := by
    intro a ha
    obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp ha
    have hdB : d < B := seqOfIndex_lt_bound B T i hBpos d hdmem
    constructor <;> omega
  have hb2 : 2 < 2 ^ b := by omega
  exact exists_passRun_accept_of_stepNs_bounded (M.stutter) Z x
    ((seqOfIndex B T i).map (fun y => y + 1)) hAll hb2 t τ z hmem hstepNs haccZ

/-- **带长度界的接受总线**：同 `exists_passRun_accept_of_acceptsWithin`，额外保证
    数字列表 `L.length ≤ T`（供外层按预算跑观察机使用）。
    Whole accept bridge with the extra bound `|L| ≤ T`. -/
theorem exists_passRun_accept_of_acceptsWithin_len {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T : Nat) (b : Nat) (hbnd : B + 2 < 2 ^ b)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hacc : M.AcceptsWithin w T) :
    ∃ (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (c : Nat) (hc : c < 2 ^ b)
      (r : PassRes q b),
      passRun q b (M.stutter.haltNorm).step Z c hc x L hb = some r ∧
        r.reg.state = M.accept ∧ L.length ≤ T := by
  obtain ⟨i, _hi, c, hrun, haccC⟩ :=
    (acceptsWithin_iff_exists_index hB hBpos w T).mp hacc
  have hrunS : (M.stutter).runWith T ((seqOfIndex B T i).map (fun y => y + 1))
      (M.init w) = some c := by
    rw [NTM.stutter_runWith]
    exact hrun
  -- 空白预留不改变运行：把 `M.init w` 侧的成功运行搬到区域侧
  obtain ⟨c2, hrunx, hst⟩ :=
    NTM.runWith_cfgEquiv (M.stutter) T _ hxw.symm c hrunS
  have haccS : c2.state = (M.stutter).accept := by rw [← hst]; exact haccC
  obtain ⟨t, τ, z, htT, hlen, hmem, hstepNs, haccZ, _⟩ :=
    exists_stepNs_accept_of_runWith_mem (M.stutter) T
      ((seqOfIndex B T i).map (fun y => y + 1)) x c2 hx hd1 hd2 hrunx haccS
  have hAll : ∀ a ∈ (seqOfIndex B T i).map (fun y => y + 1), 1 ≤ a ∧ a + 1 < 2 ^ b := by
    intro a ha
    obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp ha
    have hdB : d < B := seqOfIndex_lt_bound B T i hBpos d hdmem
    constructor <;> omega
  have hb2 : 2 < 2 ^ b := by omega
  obtain ⟨L, hb, c', hc', r, hpass, hracc, hLlen⟩ :=
    exists_passRun_accept_of_stepNs_bounded_len (M.stutter) Z x
      ((seqOfIndex B T i).map (fun y => y + 1)) hAll hb2 t τ z hmem hstepNs haccZ
  exact ⟨L, hb, c', hc', r, hpass, hracc, Nat.le_trans hLlen (Nat.le_trans hlen htT)⟩

end DTM

end Pnp
