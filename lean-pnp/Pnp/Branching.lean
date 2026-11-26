/-
  文件：Pnp/Branching.lean
  主题：非确定机的分支上界（B5 阶段 2）。

  一台非确定机在每一步最多有有限个候选动作。因为状态集与字母表都是有限的，
  可以对所有 (状态, 符号) 的候选列表长度取最大值，得到一个常数上界 B：
  任何一步的候选编号都小于 B。

  这个 B 是后面「枚举 B^T 条分支」的基数。本文件只做上界的存在性与证明，
  不涉及模拟器本身（阶段 3 见 docs/07-B5-模拟器设计.md）。
-/

import Pnp.Classes

namespace Pnp

/-- 纸带字母表的三个符号，按列表穷举。 -/
def allSym : List Sym := [none, some true, some false]

/-- 任意符号都在 `allSym` 中。 -/
theorem mem_allSym (a : Sym) : a ∈ allSym := by
  cases a with
  | none => simp [allSym]
  | some b => cases b <;> simp [allSym]

/-- 折叠取最大值给出上界：若 `x ∈ xs`，则 `f x` 不超过 `xs.foldr (max ∘ f)`。 -/
theorem le_foldr_max {α : Type} (f : α → Nat) (init : Nat) (xs : List α) :
    ∀ x : α, x ∈ xs → f x ≤ xs.foldr (fun y acc => max (f y) acc) init := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons y ys ih =>
      intro x hx
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · -- x 就是表头
        exact Nat.le_max_left _ _
      · -- x 在尾部，用归纳假设
        exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)

namespace NTM

variable {q : Nat}

/-- 把所有 (状态, 符号) 的候选动作个数摊平成一张表。 -/
def branchLengths (M : NTM q) : List Nat :=
  (List.finRange q).flatMap
    (fun s => allSym.map (fun a => (M.step s a).length))

/-- 分支上界：候选动作个数的最大值（空表时为 0）。 -/
def branchBound (M : NTM q) : Nat :=
  M.branchLengths.foldr max 0

/-- 任何一步的候选动作个数都不超过 `branchBound`。 -/
theorem length_step_le_branchBound (M : NTM q) (s : Fin q) (a : Sym) :
    (M.step s a).length ≤ M.branchBound := by
  unfold branchBound branchLengths
  -- 先证明目标长度确实出现在摊平后的表里
  have hmem : (M.step s a).length ∈
      (List.finRange q).flatMap
        (fun s => allSym.map (fun a => (M.step s a).length)) := by
    rw [List.mem_flatMap]
    refine ⟨s, List.mem_finRange s, ?_⟩
    rw [List.mem_map]
    exact ⟨a, mem_allSym a, rfl⟩
  -- 再用「折叠取最大值」引理
  exact le_foldr_max (fun n => n) 0 _ _ hmem

end NTM

end Pnp
