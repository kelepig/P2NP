/-
  文件：Pnp/Machine/SimExpBound.lean
  主题：枚举外层总成本的指数上界（义务 d 收口）。

  单个分支的模拟成本由 `passRun_steps_le` 给出：
      `r.steps ≤ |ks| · costCap(|x.pre|, Z, |ks|, 2^b)`。
  在枚举器中 `|x.pre|`、`Z` 均被 `T = |ks|` 控制，于是单分支成本是 `T` 的二次多项式
  （系数只依赖机器的常量 `2^b`）。本文把它化成 `T · polyCost(2^b, T) ≤ 2^(K₁·T)`，
  再与外层 `B^T` 条分支相乘得 `≤ 2^((B+K₁)·T)`，最后经 `exists_poly_pow_bound`
  收进 `2^(n^K+K)`。

  Per-branch cost is a polynomial in `T` (coefficients fixed by the machine), hence
  dominated by `2^(K₁·T)`; multiplying by `B^T` and absorbing stays exponential.
-/
import Pnp.Machine.ExpBound
import Pnp.Machine.SimProgBound

namespace Pnp

/-- `a * b ≤ 2^(a+b)`（两边各自不超过 `2` 的自身次方）。 -/
theorem mul_le_two_pow_add (a b : Nat) : a * b ≤ 2 ^ (a + b) := by
  calc a * b ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul (self_le_two_pow a) (self_le_two_pow b)
    _ = 2 ^ (a + b) := (Nat.pow_add 2 a b).symm

/-- 两个幂之和被「最大指数加一」吸收：`i,j ≤ M ⇒ 2^i + 2^j ≤ 2^(M+1)`。 -/
theorem add_pow_le {i j M : Nat} (hi : i ≤ M) (hj : j ≤ M) :
    2 ^ i + 2 ^ j ≤ 2 ^ (M + 1) := by
  calc 2 ^ i + 2 ^ j ≤ 2 ^ M + 2 ^ M :=
        Nat.add_le_add (Nat.pow_le_pow_right (by decide) hi) (Nat.pow_le_pow_right (by decide) hj)
    _ = 2 * 2 ^ M := by rw [Nat.two_mul]
    _ = 2 ^ (M + 1) := by rw [Nat.pow_succ]; exact Nat.mul_comm 2 (2 ^ M)

/-- 单分支成本的多项式上界：`40 + 14T + 2·T(Bk+3) + 2Bk`。
    Polynomial envelope of one branch's simulated cost. -/
def polyCost (Bk T : Nat) : Nat := 40 + 14 * T + 2 * (T * (Bk + 3)) + 2 * Bk

namespace DTM

/-- `costCap` 在 `|x.pre| ≤ T`、`Z ≤ T` 下被 `polyCost` 控制。
    `costCap` is bounded by `polyCost` once prefix and zero-counter are `≤ T`. -/
theorem costCap_le_poly (P Z T Bk : Nat) (hP : P ≤ T) (hZ : Z ≤ T) :
    costCap P Z T Bk ≤ polyCost Bk T := by
  unfold costCap polyCost
  have hPt : P + T ≤ T + T := by omega
  have h6 : 6 * (P + T) ≤ 6 * (T + T) := Nat.mul_le_mul_left 6 hPt
  have hZt : Z + T * (Bk + 3) ≤ T + T * (Bk + 3) := Nat.add_le_add_right hZ _
  have h2 : 2 * (Z + T * (Bk + 3)) ≤ 2 * (T + T * (Bk + 3)) := Nat.mul_le_mul_left 2 hZt
  have h2e : 2 * (T + T * (Bk + 3)) = 2 * T + 2 * (T * (Bk + 3)) :=
    Nat.mul_add 2 T (T * (Bk + 3))
  rw [h2e] at h2
  omega

end DTM

/-- `polyCost` 的线性展开：`polyCost Bk T = (14+2(Bk+3))·T + (40+2Bk)`。 -/
theorem polyCost_eq (Bk T : Nat) :
    polyCost Bk T = (14 + 2 * (Bk + 3)) * T + (40 + 2 * Bk) := by
  unfold polyCost
  have hc : 2 * (T * (Bk + 3)) = (2 * (Bk + 3)) * T := by ac_rfl
  rw [Nat.add_mul, hc]
  omega

/-- **单分支成本被指数吸收**：`T · polyCost(Bk,T) ≤ 2^((2Bk+42)·T)`。
    One branch's total simulated cost is absorbed by an exponential. -/
theorem polyCost_mul_le (Bk T : Nat) :
    T * polyCost Bk T ≤ 2 ^ ((2 * Bk + 42) * T) := by
  rcases Nat.eq_zero_or_pos T with h0 | h1
  · subst h0
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  · have hT : 1 ≤ T := by omega
    -- `T·T ≤ 2^(2T)`
    have hTT : T * T ≤ 2 ^ (2 * T) := by
      have h := mul_le_two_pow_add T T
      rw [Nat.two_mul]
      exact h
    -- 二次项：`(14+2(Bk+3))·T·T ≤ 2^((22+2Bk)·T)`
    have hA_bound : (14 + 2 * (Bk + 3)) * (T * T) ≤ 2 ^ ((22 + 2 * Bk) * T) := by
      have hexp : (14 + 2 * (Bk + 3)) + 2 * T ≤ (22 + 2 * Bk) * T := by
        have hAle : 14 + 2 * (Bk + 3) ≤ (14 + 2 * (Bk + 3)) * T := by
          have hm := Nat.mul_le_mul_left (14 + 2 * (Bk + 3)) hT
          rwa [Nat.mul_one] at hm
        have hsum : 14 + 2 * (Bk + 3) + 2 * T
            ≤ (14 + 2 * (Bk + 3)) * T + 2 * T := Nat.add_le_add_right hAle _
        have heq : (14 + 2 * (Bk + 3)) * T + 2 * T = (14 + 2 * (Bk + 3) + 2) * T :=
          (Nat.add_mul (14 + 2 * (Bk + 3)) 2 T).symm
        rw [heq] at hsum
        have hc : 14 + 2 * (Bk + 3) + 2 = 22 + 2 * Bk := by omega
        rwa [hc] at hsum
      calc (14 + 2 * (Bk + 3)) * (T * T)
          ≤ 2 ^ (14 + 2 * (Bk + 3)) * 2 ^ (2 * T) :=
            Nat.mul_le_mul (self_le_two_pow _) hTT
        _ = 2 ^ ((14 + 2 * (Bk + 3)) + 2 * T) := (Nat.pow_add 2 _ _).symm
        _ ≤ 2 ^ ((22 + 2 * Bk) * T) := Nat.pow_le_pow_right (by decide) hexp
    -- 一次项：`T·(40+2Bk) ≤ 2^((41+2Bk)·T)`
    have hB_bound : T * (40 + 2 * Bk) ≤ 2 ^ ((41 + 2 * Bk) * T) := by
      have hexp : 40 + 2 * Bk + T ≤ (41 + 2 * Bk) * T := by
        have hKle : 40 + 2 * Bk ≤ (40 + 2 * Bk) * T := by
          have hm := Nat.mul_le_mul_left (40 + 2 * Bk) hT
          rwa [Nat.mul_one] at hm
        have hsum : 40 + 2 * Bk + T ≤ (40 + 2 * Bk) * T + T := Nat.add_le_add_right hKle _
        have heq : (40 + 2 * Bk) * T + T = (40 + 2 * Bk + 1) * T :=
          (DTM.natMul_succ (40 + 2 * Bk) T).symm
        rw [heq] at hsum
        have hc : 40 + 2 * Bk + 1 = 41 + 2 * Bk := by omega
        rwa [hc] at hsum
      calc T * (40 + 2 * Bk) = (40 + 2 * Bk) * T := Nat.mul_comm _ _
        _ ≤ 2 ^ (40 + 2 * Bk) * 2 ^ T :=
            Nat.mul_le_mul (self_le_two_pow _) (self_le_two_pow T)
        _ = 2 ^ ((40 + 2 * Bk) + T) := (Nat.pow_add 2 _ _).symm
        _ ≤ 2 ^ ((41 + 2 * Bk) * T) := Nat.pow_le_pow_right (by decide) hexp
    -- 尾步：`(41+2Bk)·T + 1 ≤ (2Bk+42)·T`
    have hstep : (41 + 2 * Bk) * T + 1 ≤ (2 * Bk + 42) * T := by
      have hm := DTM.natMul_succ (41 + 2 * Bk) T
      have hc : 41 + 2 * Bk + 1 = 2 * Bk + 42 := by omega
      rw [hc] at hm
      rw [hm]
      exact Nat.add_le_add_left hT _
    have hsq : T * ((14 + 2 * (Bk + 3)) * T) = (14 + 2 * (Bk + 3)) * (T * T) := by
      ac_rfl
    rw [polyCost_eq, Nat.mul_add, hsq]
    calc (14 + 2 * (Bk + 3)) * (T * T) + T * (40 + 2 * Bk)
        ≤ 2 ^ ((22 + 2 * Bk) * T) + 2 ^ ((41 + 2 * Bk) * T) :=
          Nat.add_le_add hA_bound hB_bound
      _ ≤ 2 ^ ((41 + 2 * Bk) * T + 1) :=
          add_pow_le (Nat.mul_le_mul_right T (by omega)) (Nat.le_refl _)
      _ ≤ 2 ^ ((2 * Bk + 42) * T) := Nat.pow_le_pow_right (by decide) hstep

/-- **枚举总成本的指数上界**：`B^T` 条分支、每条 `T·polyCost` 步（`T = n^k+k`），
    总成本被某个固定的 `2^(n^K+K)` 控制。
    Total enumerator cost is bounded by `2^(n^K+K)` for some fixed `K`. -/
theorem exists_enum_exp_bound (B Bk k : Nat) :
    ∃ K : Nat, ∀ n : Nat,
      B ^ (n ^ k + k) * ((n ^ k + k) * polyCost Bk (n ^ k + k)) ≤ 2 ^ (n ^ K + K) := by
  obtain ⟨K, hK⟩ := exists_poly_pow_bound (B + (2 * Bk + 42)) 0 k
  refine ⟨K, fun n => ?_⟩
  have hK' : (B + (2 * Bk + 42)) * (n ^ k + k) ≤ n ^ K + K := by
    have := hK n
    rwa [Nat.add_zero] at this
  have hpc := polyCost_mul_le Bk (n ^ k + k)
  have hB := pow_le_two_pow_mul B (n ^ k + k)
  have hmain : B ^ (n ^ k + k) * ((n ^ k + k) * polyCost Bk (n ^ k + k))
      ≤ 2 ^ ((B + (2 * Bk + 42)) * (n ^ k + k)) := by
    calc B ^ (n ^ k + k) * ((n ^ k + k) * polyCost Bk (n ^ k + k))
        ≤ 2 ^ (B * (n ^ k + k)) * 2 ^ ((2 * Bk + 42) * (n ^ k + k)) :=
          Nat.mul_le_mul hB hpc
      _ = 2 ^ (B * (n ^ k + k) + (2 * Bk + 42) * (n ^ k + k)) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ ((B + (2 * Bk + 42)) * (n ^ k + k)) :=
          congrArg (fun e => 2 ^ e) (Nat.add_mul B (2 * Bk + 42) (n ^ k + k)).symm
  exact Nat.le_trans hmain (Nat.pow_le_pow_right (by decide) hK')

namespace DTM

/-- **通路成本的二次上界**：把 `passRun_steps_le` 的多项式因子换成 `polyCost`。
    Polynomial restatement of `passRun_steps_le` under the enumerator invariants. -/
theorem passRun_steps_le_poly (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b)
      (hP : x.pre.length ≤ ks.length) (hZ : Z ≤ ks.length) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r →
      r.steps ≤ ks.length * polyCost (2 ^ b) ks.length := by
  intro Z c hc x ks hb hP hZ r hp
  have h1 := passRun_steps_le q b tab Z c hc x ks hb r hp
  have h2 : costCap x.pre.length Z ks.length (2 ^ b) ≤ polyCost (2 ^ b) ks.length :=
    costCap_le_poly _ _ _ _ hP hZ
  exact Nat.le_trans h1 (Nat.mul_le_mul_left ks.length h2)

/-- **单分支预算的指数形式**：通路步数直接 ≤ `2^((2·2^b+42)·T)`，
    供外层枚举按固定预算跑 `simObs` 使用。
    Exponential per-branch budget, the form the outer enumerator consumes. -/
theorem passRun_steps_le_two_pow (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b)
      (hP : x.pre.length ≤ ks.length) (hZ : Z ≤ ks.length) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r →
      r.steps ≤ 2 ^ ((2 * 2 ^ b + 42) * ks.length) := by
  intro Z c hc x ks hb hP hZ r hp
  exact Nat.le_trans (passRun_steps_le_poly q b tab Z c hc x ks hb hP hZ r hp)
    (polyCost_mul_le (2 ^ b) ks.length)

/-- `costCap` 的全局 `T` 上界：`|pre| ≤ T`、`Z ≤ T`、轮数 `≤ T` ⇒ `costCap ≤ polyCost Bk T`。
    枚举器里前缀（输入 + `T` 个空白）、`Z`、轮数都被全局时间界 `T` 控制。
    Global-`T` envelope of `costCap`, matching the resolver's initial padding. -/
theorem costCap_le_poly' (P Z L Bk T : Nat) (hP : P ≤ T) (hZ : Z ≤ T) (hL : L ≤ T) :
    costCap P Z L Bk ≤ polyCost Bk T := by
  unfold costCap polyCost
  have h1 : 6 * (P + L) ≤ 6 * (T + T) := by
    apply Nat.mul_le_mul_left 6
    omega
  have hZt : Z + L * (Bk + 3) ≤ T + T * (Bk + 3) := by
    have hLm : L * (Bk + 3) ≤ T * (Bk + 3) := Nat.mul_le_mul_right (Bk + 3) hL
    omega
  have h2 : 2 * (Z + L * (Bk + 3)) ≤ 2 * (T + T * (Bk + 3)) := Nat.mul_le_mul_left 2 hZt
  have h2e : 2 * (T + T * (Bk + 3)) = 2 * T + 2 * (T * (Bk + 3)) :=
    Nat.mul_add 2 T (T * (Bk + 3))
  rw [h2e] at h2
  omega

/-- **枚举器单分支预算（全局 `T` 版）**：`|pre|,Z,|ks| ≤ T` ⇒ 通路步数 `≤ 2^((2·2^b+42)·T)`。
    Per-branch budget indexed by the global time bound `T`, the form the enumerator uses
    (its initial simulation region is the input padded by `T` blanks on each side). -/
theorem passRun_steps_le_two_pow_T (q b T : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b)
      (hpre : x.pre.length ≤ T) (hZ : Z ≤ T) (hlen : ks.length ≤ T) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r →
      r.steps ≤ 2 ^ ((2 * 2 ^ b + 42) * T) := by
  intro Z c hc x ks hb hpre hZ hlen r hp
  have h1 := passRun_steps_le q b tab Z c hc x ks hb r hp
  have hcap : costCap x.pre.length Z ks.length (2 ^ b) ≤ polyCost (2 ^ b) T :=
    costCap_le_poly' _ _ _ _ _ hpre hZ hlen
  have h2 : ks.length * costCap x.pre.length Z ks.length (2 ^ b)
      ≤ T * polyCost (2 ^ b) T := by
    calc ks.length * costCap x.pre.length Z ks.length (2 ^ b)
        ≤ ks.length * polyCost (2 ^ b) T := Nat.mul_le_mul_left ks.length hcap
      _ ≤ T * polyCost (2 ^ b) T := Nat.mul_le_mul_right (polyCost (2 ^ b) T) hlen
  exact Nat.le_trans (Nat.le_trans h1 h2) (polyCost_mul_le (2 ^ b) T)

end DTM
end Pnp
