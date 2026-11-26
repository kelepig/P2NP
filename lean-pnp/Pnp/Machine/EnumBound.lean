/-
  文件：Pnp/Machine/EnumBound.lean
  File: Pnp/Machine/EnumBound.lean

  主题：分支族枚举（`(t,i)` 双参数，#141）的总步数指数上界。
  Topic: exponential step bound for the two-parameter branch-family sweep (#141).

  族大小是 `(T+1)·B^T`，单分支成本是 `T·polyCost + C`（`C` 含复位与写块开销）。
  本文把三者一起吸收进某个 `2^(n^K+K)`，作为外层机器 `hHalt` 的算术外壳。
  The family has `(T+1)·B^T` members and each costs `T·polyCost + C`; the product is
  absorbed into `2^(n^K+K)`, the arithmetic shell for the enumerator's halting bound.
-/

import Pnp.Machine.EnumSpec
import Pnp.Machine.SimExpBound

namespace Pnp

namespace DTM

/-- **分支族枚举的总成本上界**：存在固定 `K`，使
    `(T+1)·B^T·(T·polyCost(Bk,T) + C) ≤ 2^(n^K+K)`（`T = n^k + k`）。
    Total cost of the family sweep is bounded by `2^(n^K+K)`. -/
theorem exists_family_exp_bound (B Bk k C : Nat) :
    ∃ K : Nat, ∀ n : Nat,
      (n ^ k + k + 1) * B ^ (n ^ k + k)
        * ((n ^ k + k) * polyCost Bk (n ^ k + k) + C) ≤ 2 ^ (n ^ K + K) := by
  -- 线性吸收：`a·T + a + (C+2) ≤ n^K0 + K0`
  obtain ⟨K0, hK0⟩ :=
    exists_poly_pow_bound (B + 2 * Bk + 43) ((B + 2 * Bk + 43) + C + 2) k
  refine ⟨K0 + C + 1, fun n => ?_⟩
  -- 指数随底数单调地放大：`n^K0 + K0 ≤ n^(K0+C+1) + (K0+C+1)`
  have hmono : n ^ K0 + K0 ≤ n ^ (K0 + C + 1) + (K0 + C + 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- 底数 0：`0^K0 ≤ 1`，右侧指数为正故为 0，余下由 `C + 1` 吸收
      subst hn
      cases K0 with
      | zero => simp
      | succ K0' => simp; omega
    · have h1 : n ^ K0 ≤ n ^ (K0 + C + 1) := Nat.pow_le_pow_right hn (by omega)
      omega
  by_cases hT0 : n ^ k + k = 0
  · -- `T = 0`：左侧只剩常数 `C`，被 `2^K` 吸收
    have hleft : (n ^ k + k + 1) * B ^ (n ^ k + k)
        * ((n ^ k + k) * polyCost Bk (n ^ k + k) + C) = C := by
      rw [hT0]
      simp
    rw [hleft]
    have hC : C ≤ 2 ^ (n ^ (K0 + C + 1) + (K0 + C + 1)) := by
      have h1 : C ≤ 2 ^ C := self_le_two_pow C
      have h2 : 2 ^ C ≤ 2 ^ (K0 + C + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 ^ (K0 + C + 1)
          ≤ 2 ^ (n ^ (K0 + C + 1) + (K0 + C + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact hC
  · -- `T ≥ 1`：逐因子换成 2 的幂再合并
    have hT : 1 ≤ n ^ k + k := by omega
    have h1 : n ^ k + k + 1 ≤ 2 ^ (n ^ k + k + 1) := self_le_two_pow _
    have h2 : B ^ (n ^ k + k) ≤ 2 ^ (B * (n ^ k + k)) := pow_le_two_pow_mul B _
    have h3 : (n ^ k + k) * polyCost Bk (n ^ k + k)
        ≤ 2 ^ ((2 * Bk + 42) * (n ^ k + k)) := polyCost_mul_le Bk _
    have h4 : C ≤ 2 ^ C := self_le_two_pow C
    have h34 : (n ^ k + k) * polyCost Bk (n ^ k + k) + C
        ≤ 2 ^ ((2 * Bk + 42) * (n ^ k + k) + C + 1) := by
      have hM : (2 * Bk + 42) * (n ^ k + k) ≤ (2 * Bk + 42) * (n ^ k + k) + C :=
        Nat.le_add_right _ _
      have hC' : C ≤ (2 * Bk + 42) * (n ^ k + k) + C := Nat.le_add_left _ _
      have hsum := add_pow_le hM hC'
      calc (n ^ k + k) * polyCost Bk (n ^ k + k) + C
          ≤ 2 ^ ((2 * Bk + 42) * (n ^ k + k)) + 2 ^ C := Nat.add_le_add h3 h4
        _ ≤ 2 ^ ((2 * Bk + 42) * (n ^ k + k) + C + 1) := hsum
    have hmain : (n ^ k + k + 1) * B ^ (n ^ k + k)
        * ((n ^ k + k) * polyCost Bk (n ^ k + k) + C)
        ≤ 2 ^ ((n ^ k + k + 1) + B * (n ^ k + k)
          + ((2 * Bk + 42) * (n ^ k + k) + C + 1)) := by
      calc (n ^ k + k + 1) * B ^ (n ^ k + k)
          * ((n ^ k + k) * polyCost Bk (n ^ k + k) + C)
          ≤ 2 ^ (n ^ k + k + 1) * 2 ^ (B * (n ^ k + k))
            * 2 ^ ((2 * Bk + 42) * (n ^ k + k) + C + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h34
        _ = 2 ^ ((n ^ k + k + 1) + B * (n ^ k + k)
            + ((2 * Bk + 42) * (n ^ k + k) + C + 1)) := by
            rw [← Nat.pow_add, ← Nat.pow_add]
    -- 指数线性化并吸收
    have hexp : (n ^ k + k + 1) + B * (n ^ k + k)
        + ((2 * Bk + 42) * (n ^ k + k) + C + 1)
        ≤ (B + 2 * Bk + 43) * (n ^ k + k) + ((B + 2 * Bk + 43) + C + 2) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
      omega
    have hlin : (B + 2 * Bk + 43) * (n ^ k + k) + ((B + 2 * Bk + 43) + C + 2)
        ≤ n ^ K0 + K0 := hK0 n
    calc (n ^ k + k + 1) * B ^ (n ^ k + k)
        * ((n ^ k + k) * polyCost Bk (n ^ k + k) + C)
        ≤ 2 ^ ((n ^ k + k + 1) + B * (n ^ k + k)
          + ((2 * Bk + 42) * (n ^ k + k) + C + 1)) := hmain
      _ ≤ 2 ^ ((B + 2 * Bk + 43) * (n ^ k + k) + ((B + 2 * Bk + 43) + C + 2)) :=
          Nat.pow_le_pow_right (by omega) hexp
      _ ≤ 2 ^ (n ^ K0 + K0) := Nat.pow_le_pow_right (by omega) hlin
      _ ≤ 2 ^ (n ^ (K0 + C + 1) + (K0 + C + 1)) :=
          Nat.pow_le_pow_right (by omega) hmono

end DTM

end Pnp
