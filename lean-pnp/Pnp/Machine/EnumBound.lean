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

/-- **含观察机预算的枚举总成本上界**（#241）：E 的逐分支成本取「指数预算覆盖版」
    ——每分支要写 `kr` 个空白副垫并跑满 `2^((2·2^b+42)·(T+1))` 步观察机；
    族大小 `(T+1)·B^T` 乘上去仍被某个 `2^(n^K+K)` 吸收（`T = n^k + k`）。
    Total enumeration cost including the exponential per-branch observer budget is still
    `2^(n^K+K)`, so EXP affords the budget-covering (exponential padding) design. -/
theorem exists_family_obsPhase_exp_bound (B b k L C : Nat) :
    ∃ K : Nat, ∀ n : Nat,
      (n ^ k + k + 1) * B ^ (n ^ k + k)
        * (L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) + C) ≤ 2 ^ (n ^ K + K) := by
  -- 线性吸收：`A·T + (A+L+C+1) ≤ n^K0 + K0`
  obtain ⟨K0, hK0⟩ :=
    exists_poly_pow_bound (B + 2 * 2 ^ b + 43) (B + 2 * 2 ^ b + 43 + L + C + 1) k
  refine ⟨K0, fun n => ?_⟩
  -- 三个因子各自换成 2 的幂
  have h1 : n ^ k + k + 1 ≤ 2 ^ (n ^ k + k + 1) := self_le_two_pow _
  have h2 : B ^ (n ^ k + k) ≤ 2 ^ (B * (n ^ k + k)) := pow_le_two_pow_mul B _
  have hL : L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1))
      ≤ 2 ^ (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1)) := by
    calc L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1))
        ≤ 2 ^ L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) :=
          Nat.mul_le_mul_right _ (self_le_two_pow L)
      _ = 2 ^ (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1)) := (Nat.pow_add 2 L _).symm
  -- 常数项 `C` 并入同一个幂
  have h3 : L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) + C
      ≤ 2 ^ (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1) := by
    have hC : C ≤ 2 ^ C := self_le_two_pow C
    have hle1 : L + (2 * 2 ^ b + 42) * (n ^ k + k + 1)
        ≤ L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C := Nat.le_add_right _ _
    have hle2 : C ≤ L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C := Nat.le_add_left _ _
    calc L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) + C
        ≤ 2 ^ (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1)) + 2 ^ C := Nat.add_le_add hL hC
      _ ≤ 2 ^ (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1) := add_pow_le hle1 hle2
  -- 三因子相乘
  have hmain : (n ^ k + k + 1) * B ^ (n ^ k + k)
      * (L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) + C)
      ≤ 2 ^ ((n ^ k + k + 1) + B * (n ^ k + k)
        + (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1)) := by
    calc (n ^ k + k + 1) * B ^ (n ^ k + k)
        * (L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) + C)
        ≤ 2 ^ (n ^ k + k + 1) * 2 ^ (B * (n ^ k + k))
          * 2 ^ (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = 2 ^ ((n ^ k + k + 1) + B * (n ^ k + k)
          + (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1)) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
  -- 指数线性化并吸收进 `n^K0 + K0`
  -- 关键：先把 `B * T` 换成 `B * (T+1)`，再整块折成 `(B+2·2^b+43)*(T+1)`
  have hBT : B * (n ^ k + k) ≤ B * (n ^ k + k + 1) := Nat.mul_le_mul_left B (by omega)
  have hcoef : 1 + B + (2 * 2 ^ b + 42) ≤ B + 2 * 2 ^ b + 43 := by omega
  have hsumEq : (1 + B + (2 * 2 ^ b + 42)) * (n ^ k + k + 1)
      = (n ^ k + k + 1) + B * (n ^ k + k + 1)
        + (2 * 2 ^ b + 42) * (n ^ k + k + 1) := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  have hfac : (n ^ k + k + 1) + B * (n ^ k + k + 1) + (2 * 2 ^ b + 42) * (n ^ k + k + 1)
      ≤ (B + 2 * 2 ^ b + 43) * (n ^ k + k + 1) := by
    rw [← hsumEq]
    exact Nat.mul_le_mul_right _ hcoef
  have hdist : (B + 2 * 2 ^ b + 43) * (n ^ k + k + 1)
      = (B + 2 * 2 ^ b + 43) * (n ^ k + k) + (B + 2 * 2 ^ b + 43) := by
    rw [show n ^ k + k + 1 = (n ^ k + k) + 1 from rfl, Nat.mul_add, Nat.mul_one]
  have hexp : (n ^ k + k + 1) + B * (n ^ k + k)
      + (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1)
      ≤ (B + 2 * 2 ^ b + 43) * (n ^ k + k)
        + ((B + 2 * 2 ^ b + 43) + L + C + 1) := by
    have hstep : (n ^ k + k + 1) + B * (n ^ k + k)
        + (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1)
        ≤ (n ^ k + k + 1) + B * (n ^ k + k + 1)
          + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + (L + C + 1) := by omega
    calc (n ^ k + k + 1) + B * (n ^ k + k)
        + (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1)
        ≤ (n ^ k + k + 1) + B * (n ^ k + k + 1)
          + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + (L + C + 1) := hstep
      _ ≤ (B + 2 * 2 ^ b + 43) * (n ^ k + k + 1) + (L + C + 1) :=
          Nat.add_le_add_right hfac _
      _ = (B + 2 * 2 ^ b + 43) * (n ^ k + k) + (B + 2 * 2 ^ b + 43) + (L + C + 1) := by
          rw [hdist]
      _ ≤ (B + 2 * 2 ^ b + 43) * (n ^ k + k)
          + ((B + 2 * 2 ^ b + 43) + L + C + 1) := by omega
  calc (n ^ k + k + 1) * B ^ (n ^ k + k)
      * (L * 2 ^ ((2 * 2 ^ b + 42) * (n ^ k + k + 1)) + C)
      ≤ 2 ^ ((n ^ k + k + 1) + B * (n ^ k + k)
        + (L + (2 * 2 ^ b + 42) * (n ^ k + k + 1) + C + 1)) := hmain
    _ ≤ 2 ^ ((B + 2 * 2 ^ b + 43) * (n ^ k + k)
        + ((B + 2 * 2 ^ b + 43) + L + C + 1)) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ 2 ^ (n ^ K0 + K0) := Nat.pow_le_pow_right (by omega) (hK0 n)

end DTM

end Pnp
