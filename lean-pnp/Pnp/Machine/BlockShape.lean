/-
  文件：Pnp/Machine/BlockShape.lean
  主题：非空白二进制块的结构分解。

  枚举循环的「一轮」引理 `enumLoop_round` 需要块形如
  `true^k ++ false :: rest`；本文件证明：任何只含 0/1 的非空白块，
  要么全是 1（此时应走溢出分支），要么恰好有这种「前 k 位 1、第 k+1 位 0」的形状。

  这条引理把「机器读块」与「计数器数值」解耦：后续对下标的归纳只需关心形状。
-/

import Pnp.Machine.Inc

namespace Pnp

namespace DTM

/-- 非空白二进制块的结构二分：
    要么全是 1，要么形如 `replicate k (some true) ++ some false :: rest`。 -/
theorem block_shape : ∀ (blk : List Sym), (∀ x ∈ blk, x ≠ none) →
    (∃ (k : Nat) (rest : List Sym),
        blk = List.replicate k (some true) ++ some false :: rest) ∨
      blk = List.replicate blk.length (some true)
  | [], _ => Or.inr (by simp)
  | x :: xs, h => by
      have hx : x ≠ none := h x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      -- 头符号只能是 0 或 1
      have hx' : x = some true ∨ x = some false := by
        cases x with
        | none => exact absurd rfl hx
        | some b => cases b with
          | false => exact Or.inr rfl
          | true => exact Or.inl rfl
      rcases block_shape xs hxs with ⟨k, rest, hk⟩ | hk
      · -- 尾部已有 0
        rcases hx' with hT | hF
        · subst hT
          exact Or.inl ⟨k + 1, rest, by
            rw [hk, replicate_succ_cons, List.cons_append]⟩
        · subst hF
          exact Or.inl ⟨0, xs, by simp⟩
      · -- 尾部全是 1
        rcases hx' with hT | hF
        · subst hT
          exact Or.inr (by rw [hk]; simp [List.length_cons, replicate_succ_cons])
        · subst hF
          exact Or.inl ⟨0, xs, by simp⟩

end DTM

end Pnp
