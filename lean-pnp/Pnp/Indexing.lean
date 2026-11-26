/-
  文件：Pnp/Indexing.lean
  主题：下标与选择序列的互转（B5 阶段 3 的算术底座）。

  模拟器在单带上维护一个计数器 i，从 0 数到 B^T - 1，并把 i 解码成
  「长度为 T、每项小于 B」的选择序列。本文件先在纯列表/算术层证明：

    - `seqOfIndex B T i`：把 i 按 B 进制解码成长度 T 的序列（低位在头）；
    - `indexOf B s`：把序列按 B 进制编码回下标；
    - `seqOfIndex_mem_allSeqs`：解码结果一定在 `allSeqs B T` 中；
    - `seqOfIndex_indexOf`：先编码再解码还原原序列；
    - `exists_index_of_mem_allSeqs`：枚举里的每条序列都有下标表示，
      且下标 < B^T。

  这些都是纯计算事实，不涉及图灵机；阶段 3 的机器实现仍需完成。
-/

import Pnp.Enumeration

namespace Pnp

/-- 把下标 i 按 B 进制解码成长度 T 的序列，最低位放在最前面。 -/
def seqOfIndex (B : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | T + 1, i => (i % B) :: seqOfIndex B T (i / B)

/-- 把序列按 B 进制编码成下标（最低位在最前面）。 -/
def indexOf (B : Nat) : List Nat → Nat
  | [] => 0
  | d :: rest => d + B * indexOf B rest

/-- 解码结果的长度恰为 T。 -/
theorem seqOfIndex_length (B : Nat) (T : Nat) (i : Nat) :
    (seqOfIndex B T i).length = T := by
  induction T generalizing i with
  | zero => rfl
  | succ T ih =>
      simp only [seqOfIndex, List.length_cons, ih]

/-- 解码结果的每一项都小于 B（要求 B > 0）。 -/
theorem seqOfIndex_lt_bound (B : Nat) (T : Nat) (i : Nat) (hB : 0 < B) :
    ∀ x : Nat, x ∈ seqOfIndex B T i → x < B := by
  induction T generalizing i with
  | zero =>
      intro x hx
      simp [seqOfIndex] at hx
  | succ T ih =>
      intro x hx
      simp only [seqOfIndex, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.mod_lt i hB
      · exact ih (i / B) x hx

/-- 解码结果一定是枚举 `allSeqs B T` 中的一个元素。 -/
theorem seqOfIndex_mem_allSeqs (B : Nat) (T : Nat) (i : Nat) (hB : 0 < B) :
    seqOfIndex B T i ∈ allSeqs B T := by
  rw [mem_allSeqs]
  exact ⟨seqOfIndex_length B T i, seqOfIndex_lt_bound B T i hB⟩

/-- 先编码再解码，得到原序列（要求每项 < B 且 B > 0）。 -/
theorem seqOfIndex_indexOf (B : Nat) (hB : 0 < B) :
    ∀ (s : List Nat), (∀ x : Nat, x ∈ s → x < B) →
      seqOfIndex B s.length (indexOf B s) = s := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons d rest ih =>
      intro hall
      have hd : d < B := hall d List.mem_cons_self
      have hrest : ∀ x : Nat, x ∈ rest → x < B :=
        fun x hx => hall x (List.mem_cons_of_mem _ hx)
      -- 解码首项与尾部分别还原
      have hmod : (d + B * indexOf B rest) % B = d := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
      have hdiv : (d + B * indexOf B rest) / B = indexOf B rest := by
        rw [Nat.add_mul_div_left d (indexOf B rest) hB, Nat.div_eq_of_lt hd]
        omega
      simp only [seqOfIndex, indexOf, List.length_cons]
      rw [hmod, hdiv]
      rw [ih hrest]

/-- 编码下标严格小于 B^长度（要求每项 < B 且 B > 0）。 -/
theorem indexOf_lt_pow (B : Nat) (_hB : 0 < B) :
    ∀ (s : List Nat), (∀ x : Nat, x ∈ s → x < B) →
      indexOf B s < B ^ s.length := by
  intro s
  induction s with
  | nil => intro _; simp [indexOf]
  | cons d rest ih =>
      intro hall
      have hd : d < B := hall d List.mem_cons_self
      have hrest : ∀ x : Nat, x ∈ rest → x < B :=
        fun x hx => hall x (List.mem_cons_of_mem _ hx)
      have ih' := ih hrest
      simp only [indexOf, List.length_cons]
      rw [Nat.pow_succ']
      -- d + B*j < B*(j+1) ≤ B*B^T
      have step1 : d + B * indexOf B rest < B * (indexOf B rest + 1) := by
        have hlt := Nat.add_lt_add_right hd (B * indexOf B rest)
        rw [Nat.mul_succ]
        omega
      have step2 : B * (indexOf B rest + 1) ≤ B * B ^ rest.length :=
        Nat.mul_le_mul_left B (Nat.succ_le_of_lt ih')
      exact Nat.lt_of_lt_of_le step1 step2

/-- 枚举里的每条序列都能用某个下标 i < B^T 解码得到。 -/
theorem exists_index_of_mem_allSeqs {B T : Nat} (hB : 0 < B) {s : List Nat}
    (hs : s ∈ allSeqs B T) :
    ∃ i : Nat, i < B ^ T ∧ seqOfIndex B T i = s := by
  obtain ⟨hlen, hall⟩ := mem_allSeqs.mp hs
  refine ⟨indexOf B s, ?_, ?_⟩
  · rw [← hlen]
    exact indexOf_lt_pow B hB s hall
  · rw [← hlen]
    exact seqOfIndex_indexOf B hB s hall

/-- 解码结果的第 j 项恰好是 `i / B^j % B`。
    机器实现按块读计数器时，用这个式子把每一块和对应数字对齐。 -/
theorem seqOfIndex_eq_map_range (B T i : Nat) :
    seqOfIndex B T i = (List.range T).map (fun j => i / B ^ j % B) := by
  induction T generalizing i with
  | zero => simp [seqOfIndex]
  | succ T ih =>
      rw [seqOfIndex, List.range_succ_eq_map, List.map_cons, ih (i / B)]
      simp only [List.map_map]
      congr 1
      · simp
      · apply List.map_congr_left
        intro j _
        rw [Nat.div_div_eq_div_mul]
        congr 1
        rw [Nat.pow_succ', Nat.mul_comm]

end Pnp
