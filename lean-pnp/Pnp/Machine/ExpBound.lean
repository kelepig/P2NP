/-
  文件：Pnp/Machine/ExpBound.lean
  主题：暴力搜索成本的指数上界（B5 时间界的第一块算术）。

  `bruteForce B T` 要尝试 `B^T` 条分支，每条分支模拟 `T` 步、每步常数开销 `c`，
  总成本约为 `B^T * (c*T + c)`。本文件证明它不超过 `2^((B+c)*T + c)`：

    - `self_le_two_pow`：`n ≤ 2^n`；
    - `pow_le_two_pow_mul`：`B^T ≤ 2^(B*T)`；
    - `bruteForce_cost_le`：总成本 ≤ `2^((B+c)*T + c)`。

  剩余算术（把 `(B+c)*(n^k+k)+c` 吸收进 `n^K + K`）留在下一步。

  说明（用户 2026-11-25 指令）：本文件的引理只是**零依赖主工程**的自足版本；
  Mathlib 若已有对应通用结论，`lean-mathlib/` 对照工程应直接 import 引用，
  不在本项目重证。新增算术前先查 Mathlib。
-/

import Pnp.Classes

namespace Pnp

/-- 任意自然数不超过 2 的它自己次方。 -/
theorem self_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      have ha : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

/-- `B^T ≤ 2^(B*T)`。 -/
theorem pow_le_two_pow_mul (B T : Nat) : B ^ T ≤ 2 ^ (B * T) := by
  have h : B ^ T ≤ (2 ^ B) ^ T := Nat.pow_le_pow_left (self_le_two_pow B) T
  rwa [← Nat.pow_mul] at h

/-- 暴力搜索的成本上界：`B^T` 条分支 × 每条 `c*T + c` 步。 -/
theorem bruteForce_cost_le (B c T : Nat) :
    B ^ T * (c * T + c) ≤ 2 ^ ((B + c) * T + c) := by
  calc B ^ T * (c * T + c)
      ≤ 2 ^ (B * T) * 2 ^ (c * T + c) :=
        Nat.mul_le_mul (pow_le_two_pow_mul B T) (self_le_two_pow _)
    _ = 2 ^ (B * T + (c * T + c)) := (Nat.pow_add 2 _ _).symm
    _ = 2 ^ ((B + c) * T + c) := by
        rw [Nat.add_mul]
        congr 1
        omega


/-- `n ≥ 2` 时，多项式因子 `a` 被 `n^a` 吸收。 -/
theorem le_pow_of_two_le {n : Nat} (hn : 2 ≤ n) (a : Nat) : a ≤ n ^ a :=
  Nat.le_trans (self_le_two_pow a) (Nat.pow_le_pow_left hn a)

/-- `a * n^k ≤ n^(a+k)`（`n ≥ 2`）。 -/
theorem mul_pow_le_pow_add {a k n : Nat} (hn : 2 ≤ n) :
    a * n ^ k ≤ n ^ (a + k) := by
  calc a * n ^ k ≤ n ^ a * n ^ k := Nat.mul_le_mul_right _ (le_pow_of_two_le hn a)
    _ = n ^ (a + k) := (Nat.pow_add n a k).symm

/-- `2 * n^M ≤ n^(M+1)`（`n ≥ 2`）。 -/
theorem two_mul_pow_le {M n : Nat} (hn : 2 ≤ n) :
    2 * n ^ M ≤ n ^ (M + 1) := by
  calc 2 * n ^ M ≤ n * n ^ M := Nat.mul_le_mul_right _ hn
    _ = n ^ M * n := Nat.mul_comm _ _
    _ = n ^ (M + 1) := (Nat.pow_succ n M).symm

/-- 两个幂项之和被下一个幂吸收（`n ≥ 2`，`i j ≤ M`）。 -/
theorem two_pow_le_one {i j M n : Nat} (hn : 2 ≤ n) (hi : i ≤ M) (hj : j ≤ M) :
    n ^ i + n ^ j ≤ n ^ (M + 1) := by
  have h1 : n ^ i ≤ n ^ M := Nat.pow_le_pow_right (by omega) hi
  have h2 : n ^ j ≤ n ^ M := Nat.pow_le_pow_right (by omega) hj
  calc n ^ i + n ^ j ≤ n ^ M + n ^ M := Nat.add_le_add h1 h2
    _ = 2 * n ^ M := by rw [Nat.two_mul]
    _ ≤ n ^ (M + 1) := two_mul_pow_le hn


/-- 主吸收定理：`a*(n^k+k)+c` 被某个 `n^K + K` 控制（存在固定 `K`）。 -/
theorem exists_poly_pow_bound (a c k : Nat) :
    ∃ K : Nat, ∀ n : Nat, a * (n ^ k + k) + c ≤ n ^ K + K := by
  let e0 := a * (0 ^ k + k) + c
  let e1 := a * (1 ^ k + k) + c
  let m := (a + k) + (a * k + c)
  let K := m + e0 + e1 + 2
  refine ⟨K, ?_⟩
  have hK : 0 < K := by
    dsimp only [K]
    omega
  have h0 : e0 ≤ K := by
    dsimp only [K]
    calc e0 ≤ m + e0 := Nat.le_add_left e0 m
      _ ≤ m + e0 + e1 + 2 := by
          have h1 := Nat.le_add_right (m + e0) e1
          have h2 := Nat.le_add_right ((m + e0) + e1) 2
          exact Nat.le_trans h1 h2
  have h1 : e1 ≤ K := by
    dsimp only [K]
    calc e1 ≤ m + e0 + e1 := Nat.le_add_left e1 (m + e0)
      _ ≤ m + e0 + e1 + 2 := Nat.le_add_right _ 2
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · rw [show 0 ^ K = 0 from Nat.zero_pow hK, Nat.zero_add]
      exact h0
    · rw [show 1 ^ K = 1 from Nat.one_pow K]
      exact Nat.le_trans h1 (Nat.le_add_left K 1)
  · have hL : a * (n ^ k + k) + c = a * n ^ k + (a * k + c) := by
      rw [Nat.mul_add, Nat.add_assoc]
    rw [hL]
    have h1a : a * n ^ k ≤ n ^ (a + k) := mul_pow_le_pow_add hn
    have h2a : a * k + c ≤ n ^ (a * k + c) := le_pow_of_two_le hn (a * k + c)
    have hi : a + k ≤ m := by
      dsimp only [m]
      exact Nat.le_add_right _ _
    have hj : a * k + c ≤ m := by
      dsimp only [m]
      exact Nat.le_add_left _ _
    have hsum : n ^ (a + k) + n ^ (a * k + c) ≤ n ^ (m + 1) :=
      two_pow_le_one hn hi hj
    have hbound : a * n ^ k + (a * k + c) ≤ n ^ (m + 1) :=
      Nat.le_trans (Nat.add_le_add h1a h2a) hsum
    have hKM : m + 1 ≤ K := by
      dsimp only [K]
      omega
    have hmono : n ^ (m + 1) ≤ n ^ K := Nat.pow_le_pow_right (by omega) hKM
    exact Nat.le_trans (Nat.le_trans hbound hmono) (Nat.le_add_right _ _)
/-- 主时间界：暴力搜索（`B^T` 条分支、每条 `c*T+c` 步，`T = n^k+k`）的成本
    被某个固定的 `2^(n^K + K)` 控制。 -/
theorem exists_exp_time_bound (B c k : Nat) :
    ∃ K : Nat, ∀ n : Nat,
      B ^ (n ^ k + k) * (c * (n ^ k + k) + c) ≤ 2 ^ (n ^ K + K) := by
  obtain ⟨K', hK'⟩ := exists_poly_pow_bound (B + c) c k
  refine ⟨K', ?_⟩
  intro n
  have hcost := bruteForce_cost_le B c (n ^ k + k)
  exact Nat.le_trans hcost (Nat.pow_le_pow_right (by decide) (hK' n))

end Pnp
