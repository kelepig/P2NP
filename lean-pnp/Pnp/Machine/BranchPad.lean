/-
  文件：Pnp/Machine/BranchPad.lean
  主题：把**带右侧预留的初始区域**代入分支族完备性引理，得到 E 机可直接引用的形态。

  背景：E 的区域取 `Reg.initReg M.start w (T+1) kr`——左侧 `T+1` 个空白格（覆盖 `t ≤ T`
  的左移），右侧 `kr` 个空白格（覆盖 `T` 步的右移，并在 #234 的意义下给出右尾绝缘。
  本文件把 `BranchPhase` 的 `(t,i)` 分支完备性在 `x = initReg ...` 上实例化，前提只剩
  「`kr ≥ T`」「`Z ≤ T+1`」与「起始态不是接受态」（`M.start ≠ M.accept`；该退化情形在
  `InExp` 层单列：起始即接受则语言为全集，平凡属 EXP）。

  Instantiating the branch-family completeness at the padded initial region, so that E can
  quote it directly.
-/

import Pnp.Machine.BranchPhase
import Pnp.Machine.RightPad

namespace Pnp

namespace DTM

variable {q : Nat}

namespace Reg

/-- 初始区域左侧格数 = `kl`。 The initial region has exactly `kl` cells on the left. -/
theorem initReg_pre_length (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (initReg st w kl kr).pre.length = kl := by
  simp [initReg]

/-- 初始区域右侧格数 = 输入剩余格数 + `kr`。
    The initial region has the remaining input cells plus `kr` cells on the right. -/
theorem initReg_post_length (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (initReg st w kl kr).post.length = ((w.map some).drop 1).length + kr := by
  simp [initReg, List.length_append]

/-- 右侧预留 `kr` 格时，右侧格数至少是 `kr`。 The right side has at least `kr` cells. -/
theorem initReg_post_ge (st : Fin q) (w : List Bool) (kl kr : Nat) :
    kr ≤ (initReg st w kl kr).post.length := by
  rw [initReg_post_length]
  omega

/-- 初始区域的 `toConfig` 与 `M.init w` 是语义等价格局（任意预留都成立）。
    The padded initial region is semantically equivalent to `M.init w`, for any padding. -/
theorem initReg_cfgEquiv (M : NTM q) (w : List Bool) (kl kr : Nat) :
    CfgEquiv (initReg M.start w kl kr).toConfig (M.init w) :=
  ⟨rfl, Or.inl (initReg_sameInf M.start w kl kr)⟩

end Reg

/-- **分支族完备性（带预留初始区域版）**：`M` 在 `T` 步内接受 ⇒ 存在 `t ≤ T`、`i < B^T`，
    使该分支的运行相位机在统一指数预算内停在接受态。区域取
    `Reg.initReg M.start w (T+1) kr`（左侧 `T+1` 格、右侧 `kr ≥ T` 格）。
    Family completeness at the padded initial region: the hypotheses reduce to `kr ≥ T`,
    `Z ≤ T + 1` and `M.start ≠ M.accept`. -/
theorem exists_branch_obsPhase_accept_of_acceptsWithin_initReg {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (hZ : Z ≤ T + 1) (kr : Nat) (hkr : T ≤ kr)
    (hstart : M.start ≠ M.accept) (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (2 ^ ((2 * 2 ^ b + 42) * (T + 1)))
        ⟨embOb q b (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  refine exists_branch_obsPhase_accept_two_pow_of_acceptsWithin M hB hBpos w T b hbnd hT Z
    (Reg.initReg M.start w (T + 1) kr) (Reg.initReg_markersOK M.start w (T + 1) kr)
    (Reg.initReg_cfgEquiv M w (T + 1) kr) ?_ ?_ hstart ?_ hZ hacc
  · rw [Reg.initReg_pre_length]; omega
  · have := Reg.initReg_post_ge M.start w (T + 1) kr
    omega
  · rw [Reg.initReg_pre_length]
    exact Nat.le_refl _

end DTM

end Pnp
