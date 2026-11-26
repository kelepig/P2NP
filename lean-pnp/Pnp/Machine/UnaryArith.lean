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
import Pnp.Machine.Restore
import Pnp.Machine.RegionBuild

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

/-- `false` 型 unary 串整体改写成 `some true` 后等于 `unary (2m)`。
    Rewriting a doubled `false`-marked counter into `some true` gives `unary (2m)`. -/
theorem unaryF_map_true (m : Nat) :
    (unaryF m ++ unaryF m).map (fun _ => some true) = unary (m + m) := by
  simp [unaryF, unary, List.replicate_append_replicate]

/-- **倍增的收尾**：对 `unaryF m ++ unaryF m`（`doubleStep` 输出的形状）运行 `restoreTrue`，
    得到 `unary (2m)` 计数器（右侧 `[none]`）。
    The restore stage after doubling: running `restoreTrue` on the doubled counter yields
    `unary (2m)`. -/
theorem unary_double_restore (m : Nat) :
    restoreTrue.run (m + m + 1)
      ⟨(0 : Fin 4), Tape.mk [none] (unaryF m ++ unaryF m)⟩
      = ⟨(2 : Fin 4), Tape.mk (unary (m + m) ++ [none]) [none]⟩ := by
  have hne : ∀ x ∈ unaryF m ++ unaryF m, x ≠ none := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact unaryF_ne_none m x h
    · exact unaryF_ne_none m x h
  have hlen : (unaryF m ++ unaryF m).length = m + m := by
    simp [unaryF_length]
  rw [show m + m + 1 = (unaryF m ++ unaryF m).length + 1 from by rw [hlen]]
  rw [restoreTrue_run' [none] (unaryF m ++ unaryF m) hne]
  simp only [unaryF_map_true, unary_reverse]

/-- **带尾空白的倍增循环**（至少一个源格）：块末尾多一个空白时，第一轮把它当作新副本
    消耗掉，其余各轮沿用 `double_loop`。结论与 `double_loop` 相同（右对齐、无尾空白）。
    The doubling loop when the block carries one trailing blank (at least one source cell):
    the first round consumes it as the new copy mark, `double_loop` handles the rest. -/
theorem double_loop_trailing (r k : Nat) :
    doubleStep.run (doubleLoopSteps (r + 1) k)
      { state := (0 : Fin 4),
        tape := { left := [none],
                  right := List.replicate k (some false) ++
                           List.replicate (r + 1) (some true) ++
                           List.replicate k (some false) ++ [none] } } =
    { state := (0 : Fin 4),
      tape := { left := [none],
                right := List.replicate (k + (r + 1)) (some false) ++
                         List.replicate (k + (r + 1)) (some false) } } := by
  -- 把输入改写成 `double_iter` 的入口形状（尾空白留在 `e` 位）
  have hshape : List.replicate k (some false) ++ List.replicate (r + 1) (some true) ++
      List.replicate k (some false) ++ [none] =
      List.replicate k (some false) ++ some true ::
        (List.replicate r (some true) ++ List.replicate k (some false) ++ [none]) := by
    simp only [List.replicate_succ', List.append_assoc, List.cons_append,
      List.nil_append]
    rw [cons_replicate_append]
  rw [hshape]
  rw [show doubleLoopSteps (r + 1) k = doubleIterSteps r k + doubleLoopSteps r (k + 1)
    from rfl]
  -- 第一轮吃掉尾空白；其后各轮无尾空白，回到 `double_loop`
  rw [DTM.run_add, double_iter r k [none] (Or.inr rfl), double_loop r (k + 1)]
  simp [Nat.add_comm, Nat.add_left_comm]

/-- `unary` 形态的带尾空白倍增循环（`m ≥ 1`，即块里至少一个源格）。
    Unary form of the trailing-blank doubling loop, for a nonempty counter. -/
theorem unary_double_trailing (m : Nat) (hm : 1 ≤ m) :
    doubleStep.run (doubleLoopSteps m 0)
      ⟨(0 : Fin 4), Tape.mk [none] (unary m ++ [none])⟩
      = ⟨(0 : Fin 4), Tape.mk [none] (unaryF m ++ unaryF m)⟩ := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  simpa only [unary, unaryF, Nat.zero_add, List.replicate_zero, List.nil_append,
    List.append_nil] using double_loop_trailing r 0

/-- **完整的 unary 倍增规格（三段）**：`⟨block + 尾空白⟩` 经「倍增循环 → 恢复 → 左移归位」
    得到「头在块首、块右侧带尾空白」的纸带，计数翻倍为 `unary (2m)`（终态为恢复机的接受态 2）。
    The full three-stage unary doubling spec: loop, restore, and walking back to the block
    start — the counter comes out doubled as `unary (2m)` (end state 2 = restore's accept). -/
theorem unary_dbl_spec (m : Nat) (hm : 1 ≤ m) :
    moveLeftN (m + m)
      ((restoreTrue.run (m + m + 1)
        ⟨(0 : Fin 4),
          ((doubleStep.run (doubleLoopSteps m 0)
            ⟨(0 : Fin 4), Tape.mk [none] (unary m ++ [none])⟩).tape)⟩).tape)
      = Tape.mk [none] (unary (m + m) ++ [none]) := by
  -- ① 倍增循环
  have h1 : (doubleStep.run (doubleLoopSteps m 0)
      ⟨(0 : Fin 4), Tape.mk [none] (unary m ++ [none])⟩).tape
      = Tape.mk [none] (unaryF m ++ unaryF m) := by
    rw [unary_double_trailing m hm]
  rw [h1]
  -- ② 恢复
  rw [unary_double_restore m]
  -- ③ 左移归位（`moveLeftN_append` + unary 自逆）
  rw [moveLeftN_append (m + m) (unary (m + m)) [none] [none]
    (by simp [unary_length])]
  -- `take`/`drop` 取满整串：展开成 `replicate` 交给 `take_replicate`/`drop_replicate`
  simp [unary, unary_reverse]

/-! ### 多轮倍增 -/

/-- 一轮倍增（三段串联）作用在纸带上（步数按当前计数 `m` 计）。
    One doubling round on a tape (step counts keyed to the current count `m`). -/
def dblRound (m : Nat) (t : Tape) : Tape :=
  moveLeftN (m + m)
    ((restoreTrue.run (m + m + 1)
      ⟨(0 : Fin 4),
        ((doubleStep.run (doubleLoopSteps m 0) ⟨(0 : Fin 4), t⟩).tape)⟩).tape)

/-- `r` 轮倍增：每轮把当前计数翻倍（参数随轮次增长）。 -/
def dblIter : Nat → Nat → Tape → Tape
  | 0, _, t => t
  | r + 1, m, t => dblIter r (m + m) (dblRound m t)

/-- **多轮倍增**：从 `unary m` 出发做 `r` 轮倍增，得到 `unary (m · 2^r)`。
    `r` doublings starting from `unary m` give `unary (m * 2^r)`. -/
theorem unary_dblIter (r m : Nat) (hm : 1 ≤ m) :
    dblIter r m (Tape.mk [none] (unary m ++ [none]))
      = Tape.mk [none] (unary (m * 2 ^ r) ++ [none]) := by
  induction r generalizing m with
  | zero => simp [dblIter]
  | succ r ih =>
      rw [dblIter, dblRound, unary_dbl_spec m hm, ih (m + m) (by omega)]
      -- 指数对齐：`(m + m) * 2^r = m * 2^(r+1)`
      have h : (m + m) * 2 ^ r = m * 2 ^ (r + 1) := by
        have hm2 : m + m = m * 2 := by omega
        rw [hm2, Nat.pow_succ]
        ac_rfl
      rw [h]

/-- 从 `1` 出发的多轮倍增：`r` 轮后得到 `unary (2^r)`——
    #192 提案里的上界计数器 `U = 2^(n*(2k+3))` 正是取 `r = n*(2k+3)`。
    Starting from `1`, `r` rounds give `unary (2^r)` — the `U` counter of the plan in #192. -/
theorem unary_dblIter_one (r : Nat) :
    dblIter r 1 (Tape.mk [none] (unary 1 ++ [none]))
      = Tape.mk [none] (unary (2 ^ r) ++ [none]) := by
  rw [unary_dblIter r 1 (by decide)]
  simp

end DTM

end Pnp
