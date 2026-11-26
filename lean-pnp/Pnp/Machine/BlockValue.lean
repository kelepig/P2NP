/-
  文件：Pnp/Machine/BlockValue.lean
  主题：二进制块的数值语义（低位在左）。

  枚举循环每转一轮，块（`List Sym`，只含 0/1）的数值就加 1；块全是 1 时
  再加一就溢出。本文件只做纯列表算术，把「块的形状」翻译成「块的值」：

    - `symVal`：单个符号的值（1 记 1，0 或空白记 0）；
    - `blockVal`：块按低位在左解释的数值。

  关键引理：
    - `blockVal_append`：块拼接时高位块左移 `2^{|前缀|}`；
    - `blockVal_round`：`true^k ++ false :: rest` 的值比
      `false^k ++ true :: rest` 的值小 1（即「加一」的数值效果）；
    - `blockVal_lt`：长度 `n` 的块取值小于 `2^n`；
    - `blockVal_all_true`：`n` 个 1 的块值为 `2^n - 1`。

  后续对轮数归纳时，用 `2^T - 1 - blockVal blk` 作递减测度。
-/

import Pnp.Machine.Inc

namespace Pnp

namespace DTM

/-- 单个符号的数值：`some true` 记 1，其余记 0。 -/
def symVal : Sym → Nat
  | some true => 1
  | _ => 0

/-- 块的数值（低位在左）：`blockVal (s :: rest) = symVal s + 2 * blockVal rest`。 -/
def blockVal : List Sym → Nat
  | [] => 0
  | s :: rest => symVal s + 2 * blockVal rest

/-- 单符号取值小于 2。 -/
theorem symVal_lt_two (s : Sym) : symVal s < 2 := by
  cases s with
  | none => simp [symVal]
  | some b => cases b <;> simp [symVal]

/-- 长度 `n` 的块取值小于 `2^n`。 -/
theorem blockVal_lt (blk : List Sym) : blockVal blk < 2 ^ blk.length := by
  induction blk with
  | nil => simp [blockVal]
  | cons s rest ih =>
      have h1 := symVal_lt_two s
      have h2 : 2 * blockVal rest < 2 * 2 ^ rest.length := by omega
      rw [List.length_cons, Nat.pow_succ']
      simp only [blockVal]
      omega

/-- 块拼接：`blockVal (a ++ b) = blockVal a + 2^{|a|} * blockVal b`。 -/
theorem blockVal_append (a b : List Sym) :
    blockVal (a ++ b) = blockVal a + 2 ^ a.length * blockVal b := by
  induction a with
  | nil => simp [blockVal]
  | cons s rest ih =>
      rw [List.cons_append, List.length_cons, Nat.pow_succ']
      simp only [blockVal, ih]
      simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.mul_assoc]

/-- `k` 个 0 的块值为 0。 -/
theorem blockVal_replicate_false (k : Nat) :
    blockVal (List.replicate k (some false)) = 0 := by
  induction k with
  | zero => simp [blockVal]
  | succ k ih => rw [List.replicate_succ, blockVal, symVal, ih]; simp

/-- `k` 个 1 的块值为 `2^k - 1`。 -/
theorem blockVal_replicate_true (k : Nat) :
    blockVal (List.replicate k (some true)) = 2 ^ k - 1 := by
  induction k with
  | zero => simp [blockVal]
  | succ k ih =>
      rw [List.replicate_succ, blockVal, symVal, ih, Nat.pow_succ]
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

/-- `n` 个 1 的块再加一正好是 `2^n`（溢出临界值）。 -/
theorem blockVal_all_true (n : Nat) :
    blockVal (List.replicate n (some true)) + 1 = 2 ^ n := by
  rw [blockVal_replicate_true]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- 一轮「加一」的数值效果：`true^k ++ false :: rest` 加一后恰好大 1。 -/
theorem blockVal_round (k : Nat) (rest : List Sym) :
    blockVal (List.replicate k (some false) ++ some true :: rest)
      = blockVal (List.replicate k (some true) ++ some false :: rest) + 1 := by
  rw [blockVal_append, blockVal_append, blockVal_replicate_false,
    blockVal_replicate_true, List.length_replicate, List.length_replicate]
  simp only [blockVal, symVal, Nat.zero_add]
  have hle : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hmul : 2 ^ k * (1 + 2 * blockVal rest) = 2 ^ k + 2 ^ k * (2 * blockVal rest) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hmul]
  omega

/-- 末尾补一个空白不改变块值。 -/
theorem blockVal_append_none (l : List Sym) :
    blockVal (l ++ [none]) = blockVal l := by
  rw [blockVal_append]
  simp [blockVal, symVal]

/-- 块拼接（单个符号）：`blockVal (s :: rest) = symVal s + 2 * blockVal rest`。 -/
theorem blockVal_cons (s : Sym) (rest : List Sym) :
    blockVal (s :: rest) = symVal s + 2 * blockVal rest := rfl

/-- 满值判定：非空白块若取值恰为 `2^{|blk|} - 1`，则它全是 1。 -/
theorem blockVal_eq_max (blk : List Sym) (hne : ∀ x ∈ blk, x ≠ none)
    (hmax : blockVal blk = 2 ^ blk.length - 1) :
    blk = List.replicate blk.length (some true) := by
  induction blk with
  | nil => simp
  | cons s rest ih =>
      have hs : s ≠ none := hne s List.mem_cons_self
      have hne' : ∀ x ∈ rest, x ≠ none :=
        fun x hx => hne x (List.mem_cons_of_mem _ hx)
      have hlt : blockVal rest < 2 ^ rest.length := blockVal_lt rest
      have hpow : 1 ≤ 2 ^ rest.length := Nat.one_le_two_pow
      cases s with
      | none => exact absurd rfl hs
      | some b =>
        cases b with
        | false =>
            -- 头位是 0：值最大也只有 2^{m+1} − 2，矛盾
            simp only [blockVal, symVal, List.length_cons, Nat.pow_succ'] at hmax
            omega
        | true =>
            simp only [blockVal, symVal, List.length_cons, Nat.pow_succ'] at hmax
            have hrest : blockVal rest = 2 ^ rest.length - 1 := by omega
            rw [ih hne' hrest]
            simp only [List.length_cons, List.length_replicate]
            rw [replicate_succ_cons]

end DTM

end Pnp
