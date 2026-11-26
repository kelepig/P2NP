/-
  文件：Pnp/Bits.lean
  主题：定宽二进制编码（低位在前的 `List Bool`）。

  用途：B5 的枚举循环用二进制计数器（`Machine/Inc.lean`）计数，
  每个 B 进制「数字」需要在纸带上用 `b` 个比特表示（`B ≤ 2^b`）。
  本文件给出纯列表层的编码与解码，并证明：
    - 编码长度恰为 `b`；
    - 解码值 < `2^b`；
    - `n < 2^b` 时先编码再解码还原为 `n`。

  编码方向：`bitsOfNat b n` 的第 i 位是 `n.testBit i`（低位在前）。
-/

import Pnp.Indexing

namespace Pnp

/-- 定宽二进制编码：取 `n` 的低 `b` 位，低位在前。 -/
def bitsOfNat : Nat → Nat → List Bool
  | 0, _ => []
  | b + 1, n => n.testBit 0 :: bitsOfNat b (n / 2)

/-- 二进制解码：低位在前的加权和。 -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- 编码长度等于位宽。 -/
theorem bitsOfNat_length (b n : Nat) : (bitsOfNat b n).length = b := by
  induction b generalizing n with
  | zero => simp [bitsOfNat]
  | succ b ih => simp [bitsOfNat, ih]

/-- 解码值严格小于 `2^长度`。 -/
theorem bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
      have hb : (if b then 1 else 0) < 2 := by cases b <;> decide
      simp only [bitsToNat, List.length_cons, Nat.pow_succ']
      omega

/-- 末尾补 0 不改变解码值。 -/
theorem bitsToNat_append_false (bs : List Bool) :
    bitsToNat (bs ++ [false]) = bitsToNat bs := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih => simp [bitsToNat, ih]

/-- 取最低位再解码与取模一致：`(if bit0 then 1 else 0) = n % 2`。 -/
theorem testBit_zero_toNat (n : Nat) :
    (if n.testBit 0 then (1 : Nat) else 0) = n % 2 := by
  by_cases h : n % 2 = 1
  · simp [Nat.testBit_zero, h]
  · have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    have h0 : n % 2 = 0 := by omega
    simp [Nat.testBit_zero, h0]

/-- 模恒等式：`n % 2 + 2 * (n/2 % 2^b) = n % 2^(b+1)`。 -/
theorem mod_two_pow_succ (n b : Nat) :
    (n % 2) + 2 * (n / 2 % 2 ^ b) = n % 2 ^ (b + 1) := by
  have hpow : 2 * 2 ^ b = 2 ^ (b + 1) := by rw [Nat.pow_succ']
  have h2 : (n / 2 % 2 ^ b) + 2 ^ b * (n / 2 / 2 ^ b) = n / 2 := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod (n / 2) (2 ^ b)
  have h1 : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  -- 展开后把倍数项并入模数
  have hexp : 2 * ((n / 2 % 2 ^ b) + 2 ^ b * (n / 2 / 2 ^ b)) + n % 2
      = (2 * (n / 2 % 2 ^ b) + n % 2) + 2 ^ (b + 1) * (n / 2 / 2 ^ b) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, hpow]
    omega
  have hq : n / 2 % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have hr : n % 2 < 2 := Nat.mod_lt n (by decide)
  have hbound : 2 * (n / 2 % 2 ^ b) + n % 2 < 2 ^ (b + 1) := by
    have hq' : n / 2 % 2 ^ b ≤ 2 ^ b - 1 := by omega
    rw [← hpow]
    omega
  calc
    (n % 2) + 2 * (n / 2 % 2 ^ b)
        = 2 * (n / 2 % 2 ^ b) + n % 2 := by omega
    _ = (2 * (n / 2 % 2 ^ b) + n % 2) % 2 ^ (b + 1) :=
        (Nat.mod_eq_of_lt hbound).symm
    _ = ((2 * (n / 2 % 2 ^ b) + n % 2) + 2 ^ (b + 1) * (n / 2 / 2 ^ b))
          % 2 ^ (b + 1) := by
        rw [Nat.add_mul_mod_self_left]
    _ = (2 * ((n / 2 % 2 ^ b) + 2 ^ b * (n / 2 / 2 ^ b)) + n % 2)
          % 2 ^ (b + 1) := by
        rw [← hexp]
    _ = (2 * (n / 2) + n % 2) % 2 ^ (b + 1) := by rw [h2]
    _ = n % 2 ^ (b + 1) := by rw [h1]

/-- 解码与定宽编码互逆：`bitsToNat (bitsOfNat b n) = n % 2^b`。 -/
theorem bitsToNat_bitsOfNat (b n : Nat) :
    bitsToNat (bitsOfNat b n) = n % 2 ^ b := by
  induction b generalizing n with
  | zero => simp [bitsOfNat, bitsToNat, Nat.mod_one]
  | succ b ih =>
      simp only [bitsOfNat, bitsToNat, ih]
      rw [testBit_zero_toNat, mod_two_pow_succ]

/-- `n` 放得进 `b` 位时，编码解码还原为 `n`。 -/
theorem bitsToNat_bitsOfNat_of_lt {b n : Nat} (h : n < 2 ^ b) :
    bitsToNat (bitsOfNat b n) = n := by
  rw [bitsToNat_bitsOfNat, Nat.mod_eq_of_lt h]

/-- 第 j 个 b 位块：从下标 `i` 的二进制表示中切出第 j 块（低位块在前）。 -/
def bitsBlock (b i j : Nat) : List Bool := bitsOfNat b (i / 2 ^ (b * j))

/-- 把一串比特块逐块解码成数字。 -/
def blocksToDigits (bs : List (List Bool)) : List Nat := bs.map bitsToNat

/-- 把 `i` 切成 `T` 个 b 位块并逐块解码，得到的正是以 `2^b` 为基的
    选择序列 `seqOfIndex (2^b) T i`（第 j 位 = `i / (2^b)^j % 2^b`）。 -/
theorem blocksToDigits_bitsBlock (b T i : Nat) :
    blocksToDigits ((List.range T).map (fun j => bitsBlock b i j))
      = seqOfIndex (2 ^ b) T i := by
  rw [seqOfIndex_eq_map_range]
  unfold blocksToDigits
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  unfold bitsBlock
  rw [bitsToNat_bitsOfNat, Nat.pow_mul]

end Pnp
