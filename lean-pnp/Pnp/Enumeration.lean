/-
  文件：Pnp/Enumeration.lean
  主题：穷举「长度为 T、每项小于 B」的所有选择序列（B5 阶段 1）。

  背景：
    NP ⊆ EXP 的模拟器要对每条非确定分支逐一尝试。分支用自然数列表编码，
    长度不超过 T、每个编号小于分支上界 B。本文件先在没有机器的层面
    把「枚举是穷尽且无误」讲清楚：
      - `allSeqs B T` 给出所有长度为 T、每项 < B 的序列；
      - `mem_allSeqs` 证明成员恰好就是满足这两个条件的序列。

  这一层不涉及图灵机，风险低；阶段 2/3（分支上界、单带模拟器）见
  `docs/07-B5-模拟器设计.md`。当前**没有**证明 NP ⊆ EXP。
-/

namespace Pnp

/-- 所有长度为 T、每项小于 B 的选择序列（按字典序展开）。 -/
def allSeqs (B : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | T + 1 => (List.range B).flatMap (fun i => (allSeqs B T).map (fun s => i :: s))

/-- 成员刻画：`s` 在枚举里，当且仅当长度恰为 T 且每项都小于 B。 -/
theorem mem_allSeqs {B T : Nat} {s : List Nat} :
    s ∈ allSeqs B T ↔ s.length = T ∧ ∀ x ∈ s, x < B := by
  induction T generalizing s with
  | zero =>
      -- 长度为 0 时枚举里只有空串；剩下的方向是「空串没有元素」
      simp [allSeqs]
      rintro rfl
      simp
  | succ T ih =>
      rw [allSeqs]
      simp only [List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · -- 枚举里的序列形如 i :: t
        rintro ⟨i, hiB, t, ht, rfl⟩
        have ht' := ih.mp ht
        constructor
        · simp [ht'.1]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hiB
          · exact ht'.2 x hx
      · -- 反过来：按首项 i 与尾部 t 拆开
        rintro ⟨hlen, hall⟩
        cases s with
        | nil => simp at hlen
        | cons i t =>
            refine ⟨i, hall i List.mem_cons_self, t, ?_, rfl⟩
            rw [ih]
            constructor
            · simpa using hlen
            · intro x hx
              exact hall x (List.mem_cons_of_mem _ hx)

end Pnp
