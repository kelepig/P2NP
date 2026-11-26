/-
  文件：Pnp/Machine/UnaryArith.lean
  File: Pnp/Machine/UnaryArith.lean

  主题：**unary 计数的符号层算术**——`T = |w|^k + k` 的机内计算会用 unary 计数器
        （`n` 个同符号表示 `n`）。本文件把「unary 串」的初等性质与「在计数器尾部
        加常数 `k`」的写入机运行打包，供后续计数器/乘法机直接引用。
  Topic: symbol-level unary arithmetic for the in-machine computation of `T = |w|^k + k`.
  The unary encodings, their elementary identities, and the `writeStr`-based
  "add a constant to the counter" run lemma.

  约定（与 `Double.lean` 一致）：`some true` 记「1」，空白 `none` 为分隔；
  另给 `some false` 版本（`copyCells`/`expand` 系用的是 `false` 标记）。
  Conventions: `some true` counts one; a `some false` variant is provided as well.
-/

import Pnp.Machine.WriteStr
import Pnp.Machine.Double

namespace Pnp

namespace DTM

/-! ### 两种 unary 编码 -/

/-- `true` 型 unary 数：`n` 个 `some true`。 The `true`-marked unary numeral. -/
def unary (n : Nat) : List Sym := List.replicate n (some true)

/-- `false` 型 unary 数：`n` 个 `some false`（`expand`/`copyCells` 系使用）。
    The `false`-marked unary numeral. -/
def unaryF (n : Nat) : List Sym := List.replicate n (some false)

@[simp] theorem unary_zero : unary 0 = [] := rfl

@[simp] theorem unary_succ (n : Nat) : unary (n + 1) = some true :: unary n := rfl

@[simp] theorem unaryF_zero : unaryF 0 = [] := rfl

@[simp] theorem unaryF_succ (n : Nat) : unaryF (n + 1) = some false :: unaryF n := rfl

theorem unary_length (n : Nat) : (unary n).length = n := by simp [unary]

theorem unaryF_length (n : Nat) : (unaryF n).length = n := by simp [unaryF]

/-- unary 串的逆序仍是自身（写入机自左向右写后左带即原序）。
    A unary string is its own reversal. -/
theorem unary_reverse (n : Nat) : (unary n).reverse = unary n := by
  simp [unary]

theorem unaryF_reverse (n : Nat) : (unaryF n).reverse = unaryF n := by
  simp [unaryF]

/-- 长度相加 = 串拼接（`true` 型）。 Lengths add under concatenation. -/
theorem unary_append (a b : Nat) : unary (a + b) = unary a ++ unary b := by
  simp [unary]

theorem unaryF_append (a b : Nat) : unaryF (a + b) = unaryF a ++ unaryF b := by
  simp [unaryF]

/-- unary 串不含空白（可作为「非空白块」送进 `expand` 之类的机器）。
    A unary string is blank-free. -/
theorem unary_ne_none (n : Nat) : ∀ v ∈ unary n, v ≠ none := by
  intro v hv
  simp only [unary, List.mem_replicate] at hv
  obtain ⟨-, rfl⟩ := hv
  simp

theorem unaryF_ne_none (n : Nat) : ∀ v ∈ unaryF n, v ≠ none := by
  intro v hv
  simp only [unaryF, List.mem_replicate] at hv
  obtain ⟨-, rfl⟩ := hv
  simp

/-! ### 在计数器尾部加常数 -/

/-- **加常数 k**（`true` 型）：把 `k` 个 `some true` 写在头位置并右移 `k` 格。
    Adding a constant `k` to a `true`-marked counter. -/
theorem unary_add_run (k : Nat) (L R : List Sym) :
    (writeStr (unary k)).run k ⟨(writeStr (unary k)).start, Tape.mk L R⟩
      = ⟨(writeStr (unary k)).accept, Tape.mk (unary k ++ L) (R.drop k)⟩ := by
  simpa only [unary_length, unary_reverse] using writeStr_run (unary k) L R

/-- **加常数 k**（`false` 型）。 Adding a constant to a `false`-marked counter. -/
theorem unaryF_add_run (k : Nat) (L R : List Sym) :
    (writeStr (unaryF k)).run k ⟨(writeStr (unaryF k)).start, Tape.mk L R⟩
      = ⟨(writeStr (unaryF k)).accept, Tape.mk (unaryF k ++ L) (R.drop k)⟩ := by
  simpa only [unaryF_length, unaryF_reverse] using writeStr_run (unaryF k) L R

/-- **计数器接续写入**：已有 `unary a` 的计数器后追加 `k` 个 `1`，得到 `unary (a+k)`。
    Appending `k` ones to an `unary a` counter yields `unary (a + k)`. -/
theorem unary_add_counter (a k : Nat) (L R : List Sym) :
    (writeStr (unary k)).run k ⟨(writeStr (unary k)).start, Tape.mk (unary a ++ L) R⟩
      = ⟨(writeStr (unary k)).accept,
          Tape.mk (unary (a + k) ++ L) (R.drop k)⟩ := by
  rw [unary_add_run k (unary a ++ L) R]
  rw [show unary k ++ (unary a ++ L) = unary (a + k) ++ L from by
        rw [Nat.add_comm a k, unary_append, List.append_assoc]]

/-! ### 与倍增机的接口 -/

/-- **unary 倍增**：`doubleStep` 的主循环把 `unary m` 变成 `unaryF m ++ unaryF m`
    （长度翻倍，符号统一为 `some false`；随后由 `restoreTrue` 系恢复成 `some true`）。
    Doubling a unary counter via the `doubleStep` main loop. -/
theorem unary_double_loop (m : Nat) :
    doubleStep.run (doubleLoopSteps m 0)
      ⟨(0 : Fin 4), Tape.mk [none] (unary m)⟩
      = ⟨(0 : Fin 4), Tape.mk [none] (unaryF m ++ unaryF m)⟩ := by
  simpa only [unary, unaryF, Nat.zero_add, List.replicate_zero, List.nil_append,
    List.append_nil]
    using double_loop m 0

end DTM

end Pnp
