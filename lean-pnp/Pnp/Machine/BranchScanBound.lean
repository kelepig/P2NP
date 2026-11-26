/-
  文件：Pnp/Machine/BranchScanBound.lean
  File: Pnp/Machine/BranchScanBound.lean

  主题：**E 外层循环的总步数上界**——分支数 `T·B^T` 乘以逐分支整段成本，
        整体仍被 `2^(n^K+K)` 控制（`T = n^k + k`）。
  Topic: total step bound of E's outer loop — the number of branches times the
  per-branch cost is still absorbed by `2^(n^K+K)`.

  用途（B5 义务 e）：E 机的 `hHalt` 外壳。逐分支成本由
  `branchRunStep_le_two_pow` 给出，分支数由 `EnumBound` 的指数壳吸收。
  Purpose: the `hHalt` shell for machine E.
-/

import Pnp.Machine.BranchMachineTwo
import Pnp.Machine.EnumBound

namespace Pnp

namespace DTM

/-- **E 外层循环总步数的指数上界**：存在固定指数 `K`，使任意输入 `w`
    （`T = |w|^k + k`、`Z ≤ T+1`、`B ≤ 2^b`、`l'.length ≤ T`）下，
    「`T·B^T` 个分支 × 逐分支整段成本」不超过 `2^(|w|^K + K)`。
    Exponential total-step bound for E's outer branch loop: for some fixed `K`,
    branch count times per-branch cost is at most `2^(|w|^K + K)`. -/
theorem exists_branchScan_exp_bound {q : Nat} (st : Fin q) (B b k : Nat) :
    ∃ K : Nat, ∀ (w : List Bool) (Z T : Nat) (a : Sym) (l' : List Sym),
      T = w.length ^ k + k → Z ≤ T + 1 → B ≤ 2 ^ b → l'.length ≤ T →
      T * B ^ T
        * (expandCost (a :: l') + 1
            + ((padStr (branchPad st w Z T B b - 1)).length + 1
              + (3 * branchPad st w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
            + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
                  (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
                + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length
                    Z T B b))
      ≤ 2 ^ (w.length ^ K + K) := by
  -- 复用 `EnumBound` 的族壳：`L := 2^(b+20)`（逐分支的额外常数因子）、`C := 0`
  obtain ⟨K, hK⟩ := exists_family_obsPhase_exp_bound B b k (2 ^ (b + 20)) 0
  refine ⟨K, ?_⟩
  intro w Z T a l' hTl hZ hB hl'
  -- 把 `T` 换成 `|w|^k + k`，使目标与 `hK` 的形状一致
  subst hTl
  -- 逐分支成本 ≤ `2^(b+20) · 2^((2·2^b+42)(|w|^k+k+1))`
  have hstep := branchRunStep_le_two_pow st w a l' Z (w.length ^ k + k) B b hZ hB hl'
  have hstep' : expandCost (a :: l') + 1
        + ((padStr (branchPad st w Z (w.length ^ k + k) B b - 1)).length + 1
          + (3 * branchPad st w Z (w.length ^ k + k) B b + 3 * l'.length + 1 + 1 + 1)) + 1
        + (roundCostStay (Reg.initReg st w (w.length ^ k + k + 1)
              (branchPad st w Z (w.length ^ k + k) B b)) Z B
            (Reg.initReg st w (w.length ^ k + k + 1)
              (branchPad st w Z (w.length ^ k + k) B b)).cur
          + branchBudget (Reg.initReg st w (w.length ^ k + k + 1)
              (branchPad st w Z (w.length ^ k + k) B b)).pre.length Z (w.length ^ k + k) B b)
      ≤ 2 ^ (b + 20) * 2 ^ ((2 * 2 ^ b + 42) * (w.length ^ k + k + 1)) := by
    refine Nat.le_trans hstep (Nat.le_of_eq ?_)
    rw [show (2 * 2 ^ b + 42) * (w.length ^ k + k + 1) + (b + 20)
        = (b + 20) + (2 * 2 ^ b + 42) * (w.length ^ k + k + 1) from by omega,
      Nat.pow_add]
  -- 分支数因子单调放大到 `(|w|^k+k+1)`，再交给 `hK`
  have hmono : (w.length ^ k + k) * B ^ (w.length ^ k + k)
        * (expandCost (a :: l') + 1
            + ((padStr (branchPad st w Z (w.length ^ k + k) B b - 1)).length + 1
              + (3 * branchPad st w Z (w.length ^ k + k) B b + 3 * l'.length + 1 + 1 + 1)) + 1
            + (roundCostStay (Reg.initReg st w (w.length ^ k + k + 1)
                  (branchPad st w Z (w.length ^ k + k) B b)) Z B
                (Reg.initReg st w (w.length ^ k + k + 1)
                  (branchPad st w Z (w.length ^ k + k) B b)).cur
              + branchBudget (Reg.initReg st w (w.length ^ k + k + 1)
                  (branchPad st w Z (w.length ^ k + k) B b)).pre.length
                  Z (w.length ^ k + k) B b))
      ≤ (w.length ^ k + k + 1) * B ^ (w.length ^ k + k)
        * (2 ^ (b + 20) * 2 ^ ((2 * 2 ^ b + 42) * (w.length ^ k + k + 1)) + 0) :=
    Nat.mul_le_mul
      (Nat.mul_le_mul (by omega) (Nat.le_refl _))
      (Nat.le_trans hstep' (by omega))
  exact Nat.le_trans hmono (hK w.length)

end DTM

end Pnp
