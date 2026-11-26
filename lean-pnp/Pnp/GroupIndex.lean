/-
  文件：Pnp/GroupIndex.lean
  主题：计数器下标 ↔ 定宽比特块选择（单带模拟器的语义桥）。

  机器层枚举用**二进制计数器**（`binIncFlag`）扫描 `0 … 2^{bT} − 1`；
  每次模拟一步需要一个来自 `[0, B)` 的选择编号，而 `B ≤ 2^b`。
  本文件把「下标 i 的第 j 个 b 位块」定义成第 j 步的选择：

    - `digitAt b i j`：`i / 2^{bj}` 的低 `b` 位（`bitsToNat`）；
    - `digitsOfIndex b T i`：第 0 … T−1 步的选择序列。

  已证：
    - `digitsOfIndex_eq_seqOfIndex`：它等于 `seqOfIndex (2^b) T i`；
    - `digitAt_lt` / `digitsOfIndex_lt_bound`：每位选择 < 2^b；
    - `exists_index_digitsOfIndex` / `exists_index_for_seqs`：任何 `B ≤ 2^b`
      下的选择序列都能被某个下标 i < 2^{bT} 精确复现（枚举是穷尽的）；
    - `digitsOfIndex_mem`：反过来，每个下标的解码都在 `allSeqs (2^b) T` 里。

  因此模拟器无需额外的「合法性检查」：编号超出候选表的步，`NTM.stepWith`
  直接返回 `none`（见 `lt_step_length_of_stepWith`），该分支自然失败。
-/

import Pnp.Bits
import Pnp.Enumeration

namespace Pnp

/-- 下标 i 的第 j 个 b 位块解码出的选择编号。 -/
def digitAt (b i j : Nat) : Nat := bitsToNat (bitsBlock b i j)

/-- 下标 i 对应的、长度 T 的选择序列（第 j 位是第 j 步的选择）。 -/
def digitsOfIndex (b T i : Nat) : List Nat :=
  (List.range T).map (fun j => digitAt b i j)

/-- 每个选择编号严格小于 `2^b`。 -/
theorem digitAt_lt (b i j : Nat) : digitAt b i j < 2 ^ b := by
  simp only [digitAt, bitsBlock]
  simpa [bitsOfNat_length] using bitsToNat_lt (bitsOfNat b (i / 2 ^ (b * j)))

/-- 解码序列的长度为 T。 -/
theorem digitsOfIndex_length (b T i : Nat) : (digitsOfIndex b T i).length = T := by
  simp [digitsOfIndex]

/-- 与 `seqOfIndex (2^b) T` 对齐：块解码就是定宽位解码。 -/
theorem digitsOfIndex_eq_seqOfIndex (b T i : Nat) :
    digitsOfIndex b T i = seqOfIndex (2 ^ b) T i := by
  unfold digitsOfIndex digitAt
  rw [← blocksToDigits_bitsBlock b T i]
  simp [blocksToDigits]

/-- 每个下标的解码都在 `allSeqs (2^b) T` 中。 -/
theorem digitsOfIndex_mem (b T i : Nat) :
    digitsOfIndex b T i ∈ allSeqs (2 ^ b) T := by
  rw [digitsOfIndex_eq_seqOfIndex]
  exact seqOfIndex_mem_allSeqs (2 ^ b) T i (Nat.two_pow_pos b)

/-- 解码序列的每一项都小于 `2^b`。 -/
theorem digitsOfIndex_lt_bound {b T i x : Nat} (hx : x ∈ digitsOfIndex b T i) :
    x < 2 ^ b := by
  have := (mem_allSeqs.mp (digitsOfIndex_mem b T i)).2 x hx
  exact this

/-- **枚举穷尽性**：任何长度 T、每项 < 2^b 的选择序列，都被某个
    下标 i < 2^{bT} 精确解码出来。 -/
theorem exists_index_digitsOfIndex (b T : Nat) (cs : List Nat)
    (hlen : cs.length = T) (hbound : ∀ x ∈ cs, x < 2 ^ b) :
    ∃ i : Nat, i < 2 ^ (b * T) ∧ digitsOfIndex b T i = cs := by
  have hB : 0 < 2 ^ b := Nat.two_pow_pos b
  have hmem : cs ∈ allSeqs (2 ^ b) T := by
    rw [mem_allSeqs]
    exact ⟨hlen, hbound⟩
  obtain ⟨i, hlt, hidx⟩ := exists_index_of_mem_allSeqs hB hmem
  refine ⟨i, ?_, ?_⟩
  · rw [← Nat.pow_mul] at hlt
    exact hlt
  · rw [digitsOfIndex_eq_seqOfIndex]
    exact hidx

/-- 上一条的 `B ≤ 2^b` 版本：`branchBound` 作为基数的选择序列
    （每项 < B）也能被二元计数器穷尽。 -/
theorem exists_index_for_seqs (b T B : Nat) (hB : B ≤ 2 ^ b) {s : List Nat}
    (hs : s ∈ allSeqs B T) :
    ∃ i : Nat, i < 2 ^ (b * T) ∧ digitsOfIndex b T i = s := by
  obtain ⟨hlen, hall⟩ := mem_allSeqs.mp hs
  exact exists_index_digitsOfIndex b T s hlen (fun x hx => by
    have := hall x hx
    omega)

end Pnp
