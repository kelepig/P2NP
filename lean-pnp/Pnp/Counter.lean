/-
  文件：Pnp/Counter.lean
  主题：B 进制计数器（B5 阶段 3c-ii 的算术零件）。

  模拟器在单带上维护一个「长度为 T、每位 < B」的计数器，逐个枚举分支下标。
  本文件先只在纯列表层定义「加一」：

    - `incDigits B ds`：最低位在前的 B 进制加一；溢出（全部为 B-1）时回绕为全 0；
    - `incDigits_length`：加一不改变位数；
    - `incDigits_lt`：若每位 < B，加一后每位仍 < B。

  与 `indexOf` / `seqOfIndex` 的数值对应关系（模 B^T）留到机器实现阶段再证。
-/

import Pnp.Indexing

namespace Pnp

/-- B 进制加一：最低位在列表头部；所有位都是 B-1 时整体回绕为全 0。 -/
def incDigits (B : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => if d + 1 < B then (d + 1) :: ds else 0 :: incDigits B ds

/-- 加一不改变计数器的位数。 -/
theorem incDigits_length (B : Nat) :
    ∀ ds : List Nat, (incDigits B ds).length = ds.length
  | [] => rfl
  | d :: ds => by
      rw [incDigits]
      split
      · rfl
      · simp only [List.length_cons]
        exact congrArg Nat.succ (incDigits_length B ds)

/-- 若每一位都小于 B，则加一后每一位仍小于 B（要求 B > 0）。 -/
theorem incDigits_lt (B : Nat) (hB : 0 < B) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < B) → ∀ x ∈ incDigits B ds, x < B
  | [], _, x, hx => by simp [incDigits] at hx
  | d :: ds, hds, x, hx => by
      have hds' : ∀ y ∈ ds, y < B :=
        fun y hy => hds y (List.mem_cons_of_mem _ hy)
      rw [incDigits] at hx
      split at hx
      · -- 不进位：新头为 d+1，其余位不变
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · assumption
        · exact hds' x hx
      · -- 进位：新头为 0，其余位递归加一
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hB
        · exact incDigits_lt B hB ds hds' x hx

/-- 加一后解码出的下标恰好前进 1（模 `B^位数`）；全为 B-1 时回绕为 0。 -/
theorem indexOf_incDigits (B : Nat) (hB : 0 < B) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < B) →
      indexOf B (incDigits B ds) = (indexOf B ds + 1) % B ^ ds.length := by
  intro ds
  induction ds with
  | nil => simp [incDigits, indexOf]
  | cons d rest ih =>
      intro hall
      have hd : d < B := hall d List.mem_cons_self
      have hrest : ∀ x : Nat, x ∈ rest → x < B :=
        fun x hx => hall x (List.mem_cons_of_mem _ hx)
      have hlt := indexOf_lt_pow B hB rest hrest
      have hrec := ih hrest
      rw [incDigits]
      split
      · -- 不进位：只把首位加一
        rename_i hc
        simp only [indexOf, List.length_cons]
        rw [Nat.pow_succ']
        have hlt' : d + B * indexOf B rest + 1 < B * B ^ rest.length := by
          have h1 : d + 1 + B * indexOf B rest < B + B * indexOf B rest :=
            Nat.add_lt_add_right hc (B * indexOf B rest)
          have h2 : B + B * indexOf B rest = B * (indexOf B rest + 1) := by
            rw [Nat.mul_succ]
            omega
          have h3 : B * (indexOf B rest + 1) ≤ B * B ^ rest.length :=
            Nat.mul_le_mul_left B (Nat.succ_le_of_lt hlt)
          calc
            d + B * indexOf B rest + 1 = d + 1 + B * indexOf B rest := by omega
            _ < B + B * indexOf B rest := h1
            _ = B * (indexOf B rest + 1) := h2
            _ ≤ B * B ^ rest.length := h3
        rw [Nat.mod_eq_of_lt hlt']
        omega
      · -- 进位：首位归零，递归处理剩余位
        rename_i hc
        have hdB : d + 1 = B := by
          have hle : d + 1 ≤ B := Nat.succ_le_of_lt hd
          omega
        simp only [indexOf, List.length_cons]
        rw [hrec, Nat.pow_succ']
        have hrw : d + B * indexOf B rest + 1 = B * (indexOf B rest + 1) := by
          rw [Nat.mul_succ]
          omega
        rw [hrw, Nat.mul_mod_mul_left B (indexOf B rest + 1) (B ^ rest.length)]
        omega

/-- 把计数器连续加一 `k` 次（枚举循环的纯列表层骨架）。 -/
def incDigitsIter (B : Nat) : Nat → List Nat → List Nat
  | 0, ds => ds
  | k + 1, ds => incDigitsIter B k (incDigits B ds)

/-- 反复加一不改变位数。 -/
theorem incDigitsIter_length (B : Nat) (k : Nat) :
    ∀ ds : List Nat, (incDigitsIter B k ds).length = ds.length := by
  induction k with
  | zero => intro ds; rfl
  | succ k ih => intro ds; rw [incDigitsIter, ih, incDigits_length]

/-- 反复加一保持「每位 < B」。 -/
theorem incDigitsIter_lt (B : Nat) (hB : 0 < B) (k : Nat) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < B) →
      ∀ x ∈ incDigitsIter B k ds, x < B := by
  induction k with
  | zero => intro ds h x hx; exact h x hx
  | succ k ih =>
      intro ds h x hx
      -- `incDigitsIter B (k+1) ds` 按定义就是先加一再迭代 `k` 次
      have hx' : x ∈ incDigitsIter B k (incDigits B ds) := hx
      exact ih (incDigits B ds) (incDigits_lt B hB ds h) x hx'

/-- 反复加一 `k` 次后，解码下标恰好前进 `k`（模 `B^位数`）。 -/
theorem indexOf_incDigitsIter (B : Nat) (hB : 0 < B) (k : Nat) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < B) →
      indexOf B (incDigitsIter B k ds) = (indexOf B ds + k) % B ^ ds.length := by
  induction k with
  | zero =>
      intro ds h
      rw [incDigitsIter, Nat.add_zero, Nat.mod_eq_of_lt (indexOf_lt_pow B hB ds h)]
  | succ k ih =>
      intro ds h
      rw [incDigitsIter,
        ih (incDigits B ds) (incDigits_lt B hB ds h),
        incDigits_length, indexOf_incDigits B hB ds h,
        Nat.mod_add_mod,
        show indexOf B ds + 1 + k = indexOf B ds + (k + 1) by omega]

/-- 全零计数器的下标为 0。 -/
theorem indexOf_replicate_zero (B T : Nat) : indexOf B (List.replicate T 0) = 0 := by
  induction T with
  | zero => rfl
  | succ T ih => simp [List.replicate_succ, indexOf, ih]

/-- 下标 0 解码为全零序列。 -/
theorem seqOfIndex_zero (B T : Nat) : seqOfIndex B T 0 = List.replicate T 0 := by
  induction T with
  | zero => rfl
  | succ T ih => simp [seqOfIndex, List.replicate_succ, ih]

/-- 全零计数器每位都小于 `B`（`B > 0`）。 -/
theorem replicate_zero_lt (B T : Nat) (hB : 0 < B) :
    ∀ d ∈ List.replicate T 0, d < B := by
  intro d hd
  rw [List.mem_replicate] at hd
  rw [hd.2]
  exact hB

/-- 枚举循环的完备性：第 `j` 次加一后，计数器正好解码为 `seqOfIndex B T j`。 -/
theorem incDigitsIter_eq_seqOfIndex (B T : Nat) (hB : 0 < B)
    (j : Nat) (hj : j < B ^ T) :
    incDigitsIter B j (List.replicate T 0) = seqOfIndex B T j := by
  have hlt0 := replicate_zero_lt B T hB
  have hlen : (incDigitsIter B j (List.replicate T 0)).length = T := by
    rw [incDigitsIter_length, List.length_replicate]
  have hlt : ∀ x ∈ incDigitsIter B j (List.replicate T 0), x < B :=
    incDigitsIter_lt B hB j _ hlt0
  -- 由「编码再解码还原」把计数器写成 seqOfIndex 的形式
  have hdec := seqOfIndex_indexOf B hB (incDigitsIter B j (List.replicate T 0)) hlt
  rw [hlen] at hdec
  rw [← hdec]
  -- 解码出的下标 = j（全零初值、未回绕）
  rw [indexOf_incDigitsIter B hB j (List.replicate T 0) hlt0,
    List.length_replicate, indexOf_replicate_zero, Nat.zero_add,
    Nat.mod_eq_of_lt hj]

/-- 枚举循环的回绕：加一 `B^T` 次后计数器回到全零。 -/
theorem incDigitsIter_wrap (B T : Nat) (hB : 0 < B) :
    incDigitsIter B (B ^ T) (List.replicate T 0) = List.replicate T 0 := by
  have hlt0 := replicate_zero_lt B T hB
  have hlen : (incDigitsIter B (B ^ T) (List.replicate T 0)).length = T := by
    rw [incDigitsIter_length, List.length_replicate]
  have hlt : ∀ x ∈ incDigitsIter B (B ^ T) (List.replicate T 0), x < B :=
    incDigitsIter_lt B hB (B ^ T) _ hlt0
  have hdec := seqOfIndex_indexOf B hB (incDigitsIter B (B ^ T) (List.replicate T 0)) hlt
  rw [hlen] at hdec
  rw [← hdec]
  rw [indexOf_incDigitsIter B hB (B ^ T) (List.replicate T 0) hlt0,
    List.length_replicate, indexOf_replicate_zero, Nat.zero_add, Nat.mod_self,
    seqOfIndex_zero]

end Pnp
