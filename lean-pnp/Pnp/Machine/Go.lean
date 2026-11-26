/-
  文件：Pnp/Machine/Go.lean
  File: Pnp/Machine/Go.lean

  主题：**固定步数走位机** `goLeft n` / `goRight n`——状态即已走步数，走满 `n` 步就停机。
        用于「写完一段串后把读写头搬回段首」的复位腿，以及区域装配时的精确定位。
  Topic: fixed-step head movers. The state counts the steps taken; the machine halts after
  exactly `n` steps. Used to bring the head back after writing a string, and for exact
  positioning during region assembly.

  本文件给出：
    - `goStep`：方向参数化的走位转移函数；
    - `goLeft` / `goRight`：左右走位机（状态数 `n+1`，接受/拒绝态同为 `n`）；
    - `goLeft_run` / `goRight_run`：从状态 `n-k` 出发，恰好 `k` 步后纸带为
      `moveLeftN k t` / `moveRightN k t`。
  This file gives the direction-parameterised step function, the two machines, and their
  exact run lemmas.

  前提说明：左走位的「读符号原样写回」在**右带为空**时会多写一个空白格（`moveLeft`
  只看左带，写回却先往右带压了一个符号），故 `goLeft_run` 要求右带非空；右走位没有
  这一限制（右带为空时写回与右移的结果仍相同），`goRight_run` 无需假设。
  Note: the write-back differs from the identity for a left move only when the right tape
  is empty, so `goLeft_run` assumes `t.right ≠ []`; `goRight_run` needs no such hypothesis.
-/

import Pnp.Machine.RegionBuild

namespace Pnp

namespace DTM

/-- 走位转移：状态 `i < n` 时沿方向 `d` 走一步并进 `i+1`；已满 `n` 步则原地不动。
    Step transition: below `n`, take one step in direction `d` and advance to `i+1`;
    at `n`, stay. -/
def goStep (n : Nat) (d : Dir) : Fin (n + 1) → Sym → Fin (n + 1) × Sym × Dir
  | st, a =>
      if h : st.val < n then (⟨st.val + 1, by omega⟩, a, d) else (st, a, Dir.stay)

/-- **左走位机**：从状态 0 起连续左移 `n` 步，停在状态 `n`。
    Left mover: from state 0, move left `n` times and halt in state `n`. -/
def goLeft (n : Nat) : DTM (n + 1) where
  step := goStep n Dir.left
  start := ⟨0, Nat.zero_lt_succ n⟩
  accept := ⟨n, Nat.lt_succ_self n⟩
  reject := ⟨n, Nat.lt_succ_self n⟩

/-- **右走位机**：从状态 0 起连续右移 `n` 步，停在状态 `n`。
    Right mover: from state 0, move right `n` times and halt in state `n`. -/
def goRight (n : Nat) : DTM (n + 1) where
  step := goStep n Dir.right
  start := ⟨0, Nat.zero_lt_succ n⟩
  accept := ⟨n, Nat.lt_succ_self n⟩
  reject := ⟨n, Nat.lt_succ_self n⟩

/-- 把读到的符号原样写回再左移，等于直接左移（右带非空时）。
    Writing back the read symbol and then moving left equals moving left (non-empty right). -/
theorem write_read_moveLeft (t : Tape) (h : t.right ≠ []) :
    (t.write t.read).moveLeft = t.moveLeft := by
  rw [Tape.write_read t h]

/-- 把读到的符号原样写回再右移，总等于直接右移（右带为空时两边都补同一个空白）。
    Writing back the read symbol then moving right always equals moving right. -/
theorem write_read_moveRight (t : Tape) :
    (t.write t.read).moveRight = t.moveRight := by
  cases t with
  | mk l r =>
      cases r with
      | nil => rfl
      | cons x xs => rfl

/-- 一般判定：状态既不等于接受也不等于拒绝时未停机。
    A configuration is unterminated when its state is neither accept nor reject. -/
theorem halted_false_of_ne (M : DTM q) (c : Config q)
    (h1 : c.state ≠ M.accept) (h2 : c.state ≠ M.reject) : M.halted c = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2⟩

/-- 左走位机的中间状态不是终止态（`j < n` 时）。
    The left mover's intermediate state is not terminal. -/
theorem goLeft_halted_false (n j : Nat) (hj : j < n) (t : Tape) :
    (goLeft n).halted ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩ = false := by
  refine halted_false_of_ne (goLeft n) ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩ ?_ ?_
  · show (⟨j, by omega⟩ : Fin (n + 1)) ≠ (goLeft n).accept
    rw [show (goLeft n).accept = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) from rfl]
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  · show (⟨j, by omega⟩ : Fin (n + 1)) ≠ (goLeft n).reject
    rw [show (goLeft n).reject = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) from rfl]
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega

/-- 右走位机的中间状态不是终止态（`j < n` 时）。
    The right mover's intermediate state is not terminal. -/
theorem goRight_halted_false (n j : Nat) (hj : j < n) (t : Tape) :
    (goRight n).halted ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩ = false := by
  refine halted_false_of_ne (goRight n) ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩ ?_ ?_
  · show (⟨j, by omega⟩ : Fin (n + 1)) ≠ (goRight n).accept
    rw [show (goRight n).accept = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) from rfl]
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  · show (⟨j, by omega⟩ : Fin (n + 1)) ≠ (goRight n).reject
    rw [show (goRight n).reject = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) from rfl]
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega

/-- 左走位一步：状态 `j` 且 `j < n` 时，一步后状态 `j+1`、纸带左移一格。
    One left-mover step from state `j < n`. -/
theorem goLeft_step (n j : Nat) (hj : j < n) (t : Tape) (hr : t.right ≠ []) :
    (goLeft n).stepConfig ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩
      = ⟨(⟨j + 1, by omega⟩ : Fin (n + 1)), Tape.moveLeft t⟩ := by
  simp only [DTM.stepConfig, goLeft, goStep, dite_eq_left hj, Tape.move,
    write_read_moveLeft t hr]

/-- 右走位一步：状态 `j` 且 `j < n` 时，一步后状态 `j+1`、纸带右移一格。
    One right-mover step from state `j < n`. -/
theorem goRight_step (n j : Nat) (hj : j < n) (t : Tape) :
    (goRight n).stepConfig ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩
      = ⟨(⟨j + 1, by omega⟩ : Fin (n + 1)), Tape.moveRight t⟩ := by
  simp only [DTM.stepConfig, goRight, goStep, dite_eq_left hj, Tape.move,
    write_read_moveRight t]

/-- **左走位的主运行引理**：状态 `j` 出发，`k` 步后状态 `j+k`、纸带左移 `k` 次。
    Primary run lemma of the left mover: from state `j`, after `k` steps the state is
    `j+k` and the tape has moved left `k` times. -/
theorem goLeft_run_from (n k j : Nat) (t : Tape) (hjk : j + k ≤ n) (hr : t.right ≠ []) :
    (goLeft n).run k ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩
      = ⟨(⟨j + k, by omega⟩ : Fin (n + 1)), moveLeftN k t⟩ := by
  revert hr t hjk j
  induction k with
  | zero =>
      intro j t hjk hr
      rfl
  | succ k ih =>
      intro j t hjk hr
      have hj : j < n := by omega
      rw [run_succ_of_not_halted _ k _ (goLeft_halted_false n j hj t)]
      rw [goLeft_step n j hj t hr]
      -- 归纳假设（左移后右带显然非空）
      rw [ih (j + 1) (Tape.moveLeft t) (by omega) (by
        cases h : t.left with
        | nil => simp [Tape.moveLeft, h]
        | cons l ls => simp [Tape.moveLeft, h])]
      congr 1
      exact Fin.ext (by ac_rfl)

/-- **右走位的主运行引理**：状态 `j` 出发，`k` 步后状态 `j+k`、纸带右移 `k` 次。
    Primary run lemma of the right mover: from state `j`, after `k` steps the state is
    `j+k` and the tape has moved right `k` times. -/
theorem goRight_run_from (n k j : Nat) (t : Tape) (hjk : j + k ≤ n) :
    (goRight n).run k ⟨(⟨j, by omega⟩ : Fin (n + 1)), t⟩
      = ⟨(⟨j + k, by omega⟩ : Fin (n + 1)), moveRightN k t⟩ := by
  revert t hjk j
  induction k with
  | zero =>
      intro j t hjk
      rfl
  | succ k ih =>
      intro j t hjk
      have hj : j < n := by omega
      rw [run_succ_of_not_halted _ k _ (goRight_halted_false n j hj t)]
      rw [goRight_step n j hj t]
      rw [ih (j + 1) (Tape.moveRight t) (by omega)]
      congr 1
      exact Fin.ext (by ac_rfl)

/-- 左走位机走满 `n` 步：状态 `n`、纸带左移 `n` 次（从起点状态 0 出发）。
    The left mover completing all `n` steps from its start state. -/
theorem goLeft_run (n : Nat) (t : Tape) (hr : t.right ≠ []) :
    (goLeft n).run n ⟨(goLeft n).start, t⟩
      = ⟨(⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)), moveLeftN n t⟩ := by
  simpa only [goLeft, Nat.zero_add] using goLeft_run_from n n 0 t (by omega) hr

/-- 右走位机走满 `n` 步：状态 `n`、纸带右移 `n` 次（从起点状态 0 出发）。
    The right mover completing all `n` steps from its start state. -/
theorem goRight_run (n : Nat) (t : Tape) :
    (goRight n).run n ⟨(goRight n).start, t⟩
      = ⟨(⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)), moveRightN n t⟩ := by
  simpa only [goRight, Nat.zero_add] using goRight_run_from n n 0 t (by omega)

end DTM

end Pnp
