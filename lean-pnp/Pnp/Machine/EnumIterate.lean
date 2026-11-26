/-
  文件：Pnp/Machine/EnumIterate.lean
  主题：枚举循环的多轮归纳——`2^T` 轮后溢出停机。

  把 `enumLoop_round`（首轮）、`enumLoop_round1`（第二轮起）与
  `enumLoop_overflow1`（第二轮起的溢出分支）按轮的次数串起来：

    - 起点：块是全 0 的 `T` 位计数器，右侧紧跟一个空白；
    - 每一轮：块值加 1（`blockVal_round`），左侧保持一个空白；
    - 块的取值递减测度 `2^T − 1 − blockVal blk` 每轮减 1；
    - 测度为 0 时块必全为 1（`blockVal_eq_max`），溢出分支清零并接受。

  由此得到整机定理：从全 0 计数器出发，`2^T` 轮内一定接受，步数有线性上界
  `(2^T − 1) · (2T + 6) + (2T + 5)`。
-/

import Pnp.Machine.EnumLoop
import Pnp.Machine.BlockShape
import Pnp.Machine.BlockValue

namespace Pnp

namespace DTM

/-- 多轮枚举（后续轮，左侧已有一个空白）：
    若块 `blk` 长 `T`、全非空白、剩余测度 `n = 2^T − 1 − blockVal blk`，
    则 `n` 轮内整机接受，步数不超过 `n·(2T+6) + (2T+5)`。 -/
theorem enumLoop_enum_blank (T : Nat) :
    ∀ (n : Nat) (blk : List Sym),
      blk.length = T →
      (∀ x ∈ blk, x ≠ none) →
      n = 2 ^ T - 1 - blockVal blk →
      ∃ m, m ≤ n * (2 * T + 6) + (2 * T + 5) ∧
        enumLoop.run m
            { state := loopIncState 0,
              tape := { left := [none], right := blk ++ [none] } } =
          { state := (10 : Fin 12),
            tape := { left := [none],
                      right := List.replicate (T + 2) (some false) } } := by
  intro n
  induction n with
  | zero =>
      intro blk hlen hne hval
      -- 测度为 0：块必为全 1，走溢出分支
      have hlt : blockVal blk < 2 ^ blk.length := blockVal_lt blk
      rw [hlen] at hlt
      have hmax : blockVal blk = 2 ^ blk.length - 1 := by
        rw [hlen]
        omega
      have hall : blk = List.replicate T (some true) := by
        rw [← hlen]
        exact blockVal_eq_max blk hne hmax
      refine ⟨2 * T + 5, by omega, ?_⟩
      rw [hall]
      rw [show 2 * T + 5 = (T + 1) + 1 + (T + 3) by omega]
      exact enumLoop_overflow1 T
  | succ n ih =>
      intro blk hlen hne hval
      -- 测度为正：块不是全 1
      have hlt : blockVal blk < 2 ^ blk.length := blockVal_lt blk
      rw [hlen] at hlt
      rcases block_shape blk hne with ⟨k, rest0, hshape⟩ | hall
      · -- 形状 `true^k ++ false :: rest0`：走一轮 `enumLoop_round1`
        rw [hshape] at hlen hne hval ⊢
        -- 长度关系与末尾空白
        have hk : k + 1 ≤ T := by
          have h2 := hlen
          simp only [List.length_append, List.length_replicate, List.length_cons] at h2
          omega
        have hrest : rest0 ++ [none] ≠ [] := by simp
        have hrest0ne : ∀ x ∈ rest0, x ≠ none := by
          intro x hx
          exact hne x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
        -- 一轮的结果（对齐右侧的拼接括号）
        have hEq : List.replicate k (some false) ++ some true :: (rest0 ++ [none])
            = (List.replicate k (some false) ++ some true :: rest0) ++ [none] := by
          simp [List.append_assoc]
        have hround0 := enumLoop_round1 k (rest0 ++ [none]) hrest
        have hround : enumLoop.run (2 * k + 6)
              { state := loopIncState 0,
                tape := { left := [none],
                          right := (List.replicate k (some true) ++ some false :: rest0) ++ [none] } }
            = { state := (0 : Fin 12),
                tape := { left := [none],
                          right := (List.replicate k (some false) ++ some true :: rest0) ++ [none] } } := by
          rw [show 2 * k + 6 = (k + 1) + 1 + (k + 3) + 1 by omega]
          rw [show (List.replicate k (some true) ++ some false :: rest0) ++ [none]
                = List.replicate k (some true) ++ some false :: (rest0 ++ [none]) by
            simp [List.append_assoc]]
          rw [hround0]
          rw [hEq]
        -- 递归所用的新块
        have hnewlen : (List.replicate k (some false) ++ some true :: rest0).length = T := by
          simp only [List.length_append, List.length_replicate, List.length_cons] at hlen ⊢
          omega
        have hnewne : ∀ x ∈ List.replicate k (some false) ++ some true :: rest0, x ≠ none := by
          intro x hx
          rcases List.mem_append.mp hx with h1 | h2
          · rw [List.mem_replicate] at h1
            rw [h1.2]
            decide
          · rcases List.mem_cons.mp h2 with rfl | h3
            · decide
            · exact hrest0ne x h3
        have hbv : blockVal (List.replicate k (some false) ++ some true :: rest0)
            = blockVal (List.replicate k (some true) ++ some false :: rest0) + 1 :=
          blockVal_round k rest0
        have hval' : n = 2 ^ T - 1 - blockVal (List.replicate k (some false) ++ some true :: rest0) := by
          rw [hbv]; omega
        rcases ih (List.replicate k (some false) ++ some true :: rest0) hnewlen hnewne hval'
          with ⟨m, hm, hrun⟩
        refine ⟨(2 * k + 6) + m, ?_, ?_⟩
        · -- 步数上界
          have hk6 : 2 * k + 6 ≤ 2 * T + 6 := by omega
          have hexp : (n + 1) * (2 * T + 6) = n * (2 * T + 6) + (2 * T + 6) :=
            Nat.succ_mul n (2 * T + 6)
          calc (2 * k + 6) + m
              ≤ (2 * T + 6) + (n * (2 * T + 6) + (2 * T + 5)) :=
                Nat.add_le_add hk6 hm
            _ = (n + 1) * (2 * T + 6) + (2 * T + 5) := by
                rw [hexp]
                omega
        · -- 拼装：一轮 + 递归
          rw [DTM.run_add enumLoop (2 * k + 6) m, hround]
          exact hrun
      · -- 全 1：与「测度为正」矛盾
        rw [hall] at hval
        rw [blockVal_replicate_true, hlen] at hval
        omega

/-- 整机定理（首轮从左侧空白开始）：全 0 的 `T` 位计数器（右侧一个空白）
    在 `(2^T − 1)·(2T+6) + (2T+5)` 步内枚举完所有 `2^T` 个下标并接受。 -/
theorem enumLoop_enum_zero (T : Nat) :
    ∃ m, m ≤ (2 ^ T - 1) * (2 * T + 6) + (2 * T + 5) ∧
      enumLoop.run m
          { state := loopIncState 0,
            tape := { left := [], right := List.replicate T (some false) ++ [none] } } =
        { state := (10 : Fin 12),
          tape := { left := [none],
                    right := List.replicate (T + 2) (some false) } } := by
  cases T with
  | zero =>
      -- 0 位计数器：直接溢出
      refine ⟨5, by simp, ?_⟩
      rw [show 5 = (0 + 1) + 1 + (0 + 3) by omega]
      exact enumLoop_overflow 0 [none] (Or.inr rfl)
  | succ T =>
      -- 首轮：块本来就是「最低位 0」
      have hrest : List.replicate T (some false) ++ [none] ≠ [] := by simp
      have hround0 := enumLoop_round 0 (List.replicate T (some false) ++ [none]) hrest
      have hround : enumLoop.run 6
            { state := loopIncState 0,
              tape := { left := [],
                        right := List.replicate (T + 1) (some false) ++ [none] } }
          = { state := (0 : Fin 12),
              tape := { left := [none],
                        right := (some true :: List.replicate T (some false)) ++ [none] } } := by
        rw [show 6 = (0 + 1) + 1 + (0 + 3) + 1 by omega]
        rw [show List.replicate (T + 1) (some false) ++ [none]
              = List.replicate 0 (some true) ++ some false :: (List.replicate T (some false) ++ [none]) by
          simp [List.replicate_succ]]
        rw [hround0]
        simp [List.replicate]
      -- 后续轮：块 = `true :: false^T`
      have hnewlen : (some true :: List.replicate T (some false)).length = (T + 1) := by simp
      have hnewne : ∀ x ∈ some true :: List.replicate T (some false), x ≠ none := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | h3
        · decide
        · rw [List.mem_replicate] at h3
          rw [h3.2]
          decide
      have hbv : blockVal (some true :: List.replicate T (some false)) = 1 := by
        simp [blockVal, symVal, blockVal_replicate_false]
      have hval : 2 ^ (T + 1) - 2 = 2 ^ (T + 1) - 1
          - blockVal (some true :: List.replicate T (some false)) := by
        rw [hbv]
        have : 1 ≤ 2 ^ (T + 1) := Nat.one_le_two_pow
        omega
      rcases enumLoop_enum_blank (T + 1) (2 ^ (T + 1) - 2)
        (some true :: List.replicate T (some false)) hnewlen hnewne hval with ⟨m, hm, hrun⟩
      refine ⟨6 + m, ?_, ?_⟩
      · -- 上界：(2^{T+1}−1)·B 展开成 (2^{T+1}−2)·B + B
        have hexp : (2 ^ (T + 1) - 1) * (2 * (T + 1) + 6)
            = (2 ^ (T + 1) - 2) * (2 * (T + 1) + 6) + (2 * (T + 1) + 6) := by
          rw [show 2 ^ (T + 1) - 1 = (2 ^ (T + 1) - 2) + 1 by
            have hh : 2 ≤ 2 ^ (T + 1) := by
              have h1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
              have hmul := Nat.mul_le_mul_left 2 h1
              rw [Nat.mul_comm 2 (2 ^ T)] at hmul
              rw [Nat.pow_succ]
              simpa using hmul
            omega,
            Nat.add_mul, Nat.one_mul]
        have hB : 6 ≤ 2 * (T + 1) + 6 := by omega
        calc 6 + m
            ≤ 6 + ((2 ^ (T + 1) - 2) * (2 * (T + 1) + 6) + (2 * (T + 1) + 5)) :=
                Nat.add_le_add_left hm 6
          _ ≤ (2 * (T + 1) + 6)
                + ((2 ^ (T + 1) - 2) * (2 * (T + 1) + 6) + (2 * (T + 1) + 5)) :=
                Nat.add_le_add_right hB _
          _ = ((2 ^ (T + 1) - 2) * (2 * (T + 1) + 6) + (2 * (T + 1) + 6))
                + (2 * (T + 1) + 5) := by
                ac_rfl
          _ = (2 ^ (T + 1) - 1) * (2 * (T + 1) + 6) + (2 * (T + 1) + 5) := by
                rw [hexp]
      · -- 拼装：首轮 + 后续
        rw [DTM.run_add enumLoop 6 m, hround]
        exact hrun

end DTM

end Pnp
