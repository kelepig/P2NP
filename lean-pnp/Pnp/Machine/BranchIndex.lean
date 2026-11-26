/-
  文件：Pnp/Machine/BranchIndex.lean
  File: Pnp/Machine/BranchIndex.lean

  主题：外层枚举器的**分支计数器解码**——把单个全局下标 `j ∈ [0, T·B^T)`
        解成族成员 `(t, i)`（`t = j / B^T + 1`、`i = j % B^T`）。
  Topic: decoding the outer branch counter. A single global index `j < T · B^T`
  decodes to the family member `(t, i)` via `t = j / B^T + 1`, `i = j % B^T`.

  用途（B5 外层枚举）：E 的循环体只有一个二进制计数器，逐轮 `j ↦ j+1`；
  本文件给出「计数器值 ⇒ (轮数 t, 编号 i)」的算术，包括
  界、单射、满射（每个族成员都有下标），以及与 `branchList` 成员关系的对接。
  Purpose (B5 outer enumeration): E's loop carries one binary counter; this file
  provides the decoding arithmetic (bounds, injectivity, surjectivity) and its link
  to the family list `branchList`.
-/

import Pnp.Machine.EnumSpec

namespace Pnp

namespace DTM

/-- **分支计数器解码**：全局下标 `j` ⇒ 族成员 `(t, i)`。
    Branch counter decoding: global index `j` to the family member `(t, i)`. -/
def branchOfIndex (B T j : Nat) : Nat × Nat := (j / B ^ T + 1, j % B ^ T)

/-- 解码结果的编号分量总在界内：`i < B^T`。 -/
theorem branchOfIndex_snd_lt (B T j : Nat) (hBpos : 0 < B) :
    (branchOfIndex B T j).2 < B ^ T := by
  simp only [branchOfIndex]
  exact Nat.mod_lt j (Nat.pow_pos hBpos)

/-- 下标在 `T·B^T` 以内时，解码出的轮数不超过 `T`。 -/
theorem branchOfIndex_fst_le (B T j : Nat) (hBpos : 0 < B) (_hT : 0 < T)
    (hj : j < T * B ^ T) : (branchOfIndex B T j).1 ≤ T := by
  have hpow : 0 < B ^ T := Nat.pow_pos hBpos
  have hdiv : j / B ^ T < T := (Nat.div_lt_iff_lt_mul hpow).mpr hj
  simp only [branchOfIndex]
  exact Nat.succ_le_of_lt hdiv

/-- **解码落在族中**：`j < T·B^T` ⇒ `branchOfIndex B T j ∈ branchList B T`。 -/
theorem branchOfIndex_mem (B T j : Nat) (hBpos : 0 < B) (hT : 0 < T)
    (hj : j < T * B ^ T) : branchOfIndex B T j ∈ branchList B T := by
  have h1 : 1 ≤ (branchOfIndex B T j).1 := by
    simp only [branchOfIndex]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have h2 : (branchOfIndex B T j).1 ≤ T := branchOfIndex_fst_le B T j hBpos hT hj
  have h3 : (branchOfIndex B T j).2 < B ^ T := branchOfIndex_snd_lt B T j hBpos
  exact (mem_branchList B T (branchOfIndex B T j).1 (branchOfIndex B T j).2).mpr
    ⟨h1, h2, h3⟩

/-- **解码是单射**：`T·B^T` 以内的两个下标解码相同 ⇒ 下标相同。 -/
theorem branchOfIndex_inj (B T j j' : Nat) (hBpos : 0 < B)
    (h : branchOfIndex B T j = branchOfIndex B T j') : j = j' := by
  have hpow : 0 < B ^ T := Nat.pow_pos hBpos
  have h' := h
  simp only [branchOfIndex, Prod.mk.injEq] at h'
  have hdiv : j / B ^ T = j' / B ^ T := Nat.succ.inj h'.1
  have hmod : j % B ^ T = j' % B ^ T := h'.2
  calc j = B ^ T * (j / B ^ T) + j % B ^ T :=
        (Nat.div_add_mod j (B ^ T)).symm
    _ = B ^ T * (j' / B ^ T) + j' % B ^ T := by rw [hdiv, hmod]
    _ = j' := Nat.div_add_mod j' (B ^ T)

/-- **解码是满射（称手下标）**：族成员 `(t, i)` 的下标是 `(t − 1)·B^T + i`。
    Surjectivity with an explicit index: `(t - 1) * B^T + i` decodes to `(t, i)`. -/
theorem branchOfIndex_exists (B T t i : Nat) (hBpos : 0 < B) (_hT : 0 < T)
    (ht1 : 1 ≤ t) (hi : i < B ^ T) :
    branchOfIndex B T ((t - 1) * B ^ T + i) = (t, i) := by
  have hpow : 0 < B ^ T := Nat.pow_pos hBpos
  have hmul : (t - 1) * B ^ T = B ^ T * (t - 1) := Nat.mul_comm _ _
  -- 除法：`B^T * (t−1) + i` 除以 `B^T` 得 `t−1`（余数 `i < B^T` 丢掉）
  have hdiv : ((t - 1) * B ^ T + i) / B ^ T = t - 1 := by
    rw [hmul, Nat.mul_add_div hpow, Nat.div_eq_of_lt hi, Nat.add_zero]
  -- 余数：`B^T * m + i` 模 `B^T` 等于 `i % B^T = i`
  have hmod : ((t - 1) * B ^ T + i) % B ^ T = i := by
    rw [hmul, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  simp only [branchOfIndex, hdiv, hmod, Nat.sub_add_cancel ht1]

/-- 称手下标落在 `T·B^T` 以内（配合 `branchOfIndex_exists` 使用）。 -/
theorem branchOfIndex_exists_lt (B T t i : Nat) (ht1 : 1 ≤ t) (htT : t ≤ T)
    (hi : i < B ^ T) : (t - 1) * B ^ T + i < T * B ^ T := by
  have hpred : t - 1 < T := by omega
  have h1 : (t - 1) * B ^ T + i < (t - 1) * B ^ T + B ^ T :=
    Nat.add_lt_add_left hi _
  have h2 : (t - 1) * B ^ T + B ^ T = t * B ^ T := by
    have hs : Nat.succ (t - 1) = t := Nat.sub_add_cancel ht1
    rw [← Nat.succ_mul, hs]
  have h3 : t * B ^ T ≤ T * B ^ T := Nat.mul_le_mul_right _ htT
  omega


/-- 常数映射的求和：`(range n).map (const c)` 求和 = `n * c`。 -/
theorem sum_map_const_range (c n : Nat) :
    ((List.range n).map (fun _ => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [Nat.succ_mul]

/-- 分支族列表的长度：恰有 `T·B^T` 个族成员（E 的循环轮数）。
    Length of the family list: `T · B^T` members. -/
theorem branchList_length (B T : Nat) : (branchList B T).length = T * B ^ T := by
  simp only [branchList, List.length_flatMap, List.length_map, List.length_range]
  rw [sum_map_const_range]

/-- **分支族的计数器形式**：整个分支族（`1 ≤ t ≤ T`、`i < B^T`）上的存在量化，
    等价于「遍历全局计数器 `j < T·B^T` 并按 `branchOfIndex` 解码」。
    E 的外层循环只维护一个计数器 `j`，本件是「循环覆盖全族」的语义桥。
    Existence over the whole branch family equals scanning the single global counter
    `j < T·B^T` and decoding by `branchOfIndex`. -/
theorem exists_branch_iff_exists_index (B T : Nat) (hBpos : 0 < B) (hT : 0 < T)
    (P : Nat → Nat → Prop) :
    (∃ t i, 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧ P t i) ↔
      ∃ j, j < T * B ^ T ∧ P (branchOfIndex B T j).1 (branchOfIndex B T j).2 := by
  constructor
  · rintro ⟨t, i, ht1, htT, hi, hP⟩
    refine ⟨(t - 1) * B ^ T + i, branchOfIndex_exists_lt B T t i ht1 htT hi, ?_⟩
    rwa [branchOfIndex_exists B T t i hBpos hT ht1 hi]
  · rintro ⟨j, hj, hP⟩
    exact ⟨(branchOfIndex B T j).1, (branchOfIndex B T j).2,
      Nat.succ_le_succ (Nat.zero_le _),
      branchOfIndex_fst_le B T j hBpos hT hj,
      branchOfIndex_snd_lt B T j hBpos, hP⟩

/-- **计数器遍历 = 存在量化**：`List.range n` 上的 `any` 为真，当且仅当存在 `j < n` 使其为真。
    这是 E 外层循环「跑完所有分支、任一命中即接受」的列表层规格。
    Scanning the counter range with `any` equals an existential over `j < n`. -/
theorem any_range_iff_exists (P : Nat → Bool) (n : Nat) :
    (List.range n).any P = true ↔ ∃ j, j < n ∧ P j = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hP⟩
    exact ⟨j, List.mem_range.mp hj, hP⟩
  · rintro ⟨j, hj, hP⟩
    exact ⟨j, List.mem_range.mpr hj, hP⟩

/-- **分支总数 `T·B^T` 的指数上界**：`B ≤ 2^b` ⇒ `T·B^T ≤ 2^(T + b·T)`。
    E 的外层循环轮数是 `T·B^T`，本件是 `hHalt` 里「轮数因子」的算术外壳。
    Exponential bound on the number of branches `T·B^T`. -/
theorem branchCount_le_two_pow (B T b : Nat) (hB : B ≤ 2 ^ b) :
    T * B ^ T ≤ 2 ^ (T + b * T) := by
  have h1 : T ≤ 2 ^ T := self_le_two_pow T
  have h2 : B ^ T ≤ 2 ^ (b * T) := by
    have h : B ^ T ≤ (2 ^ b) ^ T := Nat.pow_le_pow_left hB T
    rwa [← Nat.pow_mul] at h
  have h3 : T * B ^ T ≤ 2 ^ T * 2 ^ (b * T) := Nat.mul_le_mul h1 h2
  rwa [← Nat.pow_add] at h3

end DTM

end Pnp
