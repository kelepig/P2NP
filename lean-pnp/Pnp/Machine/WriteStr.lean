/-
  文件：Pnp/Machine/WriteStr.lean
  File: Pnp/Machine/WriteStr.lean

  主题：常量串写入机——把给定的符号串逐格写到纸带上（自左向右），作为外层枚举器
        「写入区域编码 / 写入哨兵块」的可复用原语。
  Topic: a constant-string writer, a reusable primitive that writes a given symbol list
  cell by cell (moving right), used by the outer enumerator to write region encodings.

  机制：状态 `2j` 无意义，本机原地每步「写入当前符号 + 右移一格」，状态即已写格数。
  起始格被覆盖；若右侧不足则由纸带自动补空白。终态在 `l.length`。
  Mechanism: one step writes one symbol and moves right; the state counts written cells.
  The initial cell is overwritten and blanks are supplied automatically beyond the tape.

  本文件给出：
    - `writeStr`（机器定义）与 `writeStr_run`（整段运行的确切纸带形状）；
    - `writeStr_step_succ` / `writeStr_run_succ`：把 `l'` 的机器嵌进 `b :: l'` 的机器
      （状态整体上移一格），供按串归纳使用。
  This file gives the machine, its exact run shape, and the state-shift embedding lemmas
  that make induction on the string possible.
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 转移结果的状态上移一格（`Fin.succ`），纸带动作不变；供子机嵌入使用。
    Shift a transition's next state by one, keeping the tape action. -/
def stepSucc {n : Nat} (v : Fin n × Sym × Dir) : Fin (n + 1) × Sym × Dir :=
  (Fin.succ v.1, v.2.1, v.2.2)

/-- **常量串写入机的转移函数**：按待写串递归定义。
    状态 `0` 写首符号并右移到状态 `1`；状态 `j+1` 就照抄「剩余串的机器」在状态 `j`
    的一步（状态再上移一格）。空串时原地不动。
    Transition function of the writer, by recursion on the string: state `0` writes the
    head symbol and moves right into state `1`; state `j+1` mirrors the sub-machine for
    the tail at state `j`, with states shifted by one. -/
def writeStrStep :
    (l : List Sym) → Fin (l.length + 1) → Sym → Fin (l.length + 1) × Sym × Dir
  | [], st, a => (st, a, Dir.stay)
  | b :: l', st, a =>
      if st.val = 0 then
        (⟨1, by simp⟩, b, Dir.right)
      else
        stepSucc (writeStrStep l' ⟨st.val - 1, by
          have h := st.isLt
          simp only [List.length_cons] at h
          omega⟩ a)

/-- **常量串写入机**：状态数 `l.length + 1`，从状态 0 出发，逐格写入 `l` 的符号并右移，
    走到状态 `l.length` 即停机。
    The writer has `l.length + 1` states; it starts at 0, writes `l` left to right, and
    halts at state `l.length`. -/
def writeStr (l : List Sym) : DTM (l.length + 1) where
  step := writeStrStep l
  start := ⟨0, Nat.succ_pos _⟩
  accept := ⟨l.length, Nat.lt_succ_self _⟩
  reject := ⟨l.length, Nat.lt_succ_self _⟩

/-- **一步嵌入**：`b :: l'` 的机器在状态 `j+1` 的一步，正是 `l'` 的机器在状态 `j`
    的一步（状态上移一格）。这是按串归纳的关键。
    One-step embedding: at state `j+1` the machine for `b :: l'` behaves exactly like the
    machine for `l'` at state `j`, with the next state shifted by one. -/
theorem writeStr_step_succ (b : Sym) (l' : List Sym) (j : Nat)
    (hj : j < l'.length + 1) (a : Sym) :
    writeStrStep (b :: l') ⟨j + 1, by simp only [List.length_cons]; omega⟩ a
      = stepSucc (writeStrStep l' ⟨j, hj⟩ a) := by
  -- 状态值 `j+1 ≠ 0`，故走递归分支；余下按定义即知
  simp only [writeStrStep]
  split
  · omega
  · rfl

/-- **停机判定在嵌入下不变**：状态上移一格后是否停机，与原状态一致。
    Halting is invariant under the state shift. -/
theorem writeStr_halted_succ (b : Sym) (l' : List Sym) (c : Config (l'.length + 1)) :
    (writeStr (b :: l')).halted ⟨Fin.succ c.state, c.tape⟩
      = (writeStr l').halted c := by
  -- `b :: l'` 机的接受/拒绝状态恰是 `l'` 机对应状态的 `Fin.succ`
  have hacc : (writeStr (b :: l')).accept = Fin.succ (writeStr l').accept := rfl
  have hrej : (writeStr (b :: l')).reject = Fin.succ (writeStr l').reject := rfl
  -- `Fin.succ` 保持相等性（值同时加一），故两侧比较同真同假
  have hbeq : ∀ x y : Fin (l'.length + 1),
      (Fin.succ x == Fin.succ y) = (x == y) := by
    intro x y
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.ext_iff, Fin.ext_iff,
      Fin.val_succ, Fin.val_succ, Nat.succ.injEq]
  simp only [DTM.halted, hacc, hrej, hbeq]

/-- **整段运行的搬运**：`l'` 的机器跑 `m` 步，等价于 `b :: l'` 的机器从（状态上移一格的）
    同一格局跑 `m` 步；纸带完全相同。按步数归纳，停机与否由 `writeStr_halted_succ` 对齐。
    Run transport: `m` steps of the `l'` machine equal `m` steps of the `b :: l'` machine
    from the shifted configuration, on the same tape. -/
theorem writeStr_run_succ (b : Sym) (l' : List Sym) :
    ∀ (m : Nat) (c : Config (l'.length + 1)),
      (writeStr (b :: l')).run m ⟨Fin.succ c.state, c.tape⟩
        = ⟨Fin.succ ((writeStr l').run m c).state, ((writeStr l').run m c).tape⟩ := by
  intro m
  induction m with
  | zero =>
      intro c
      rfl
  | succ m ih =>
      intro c
      have hh := writeStr_halted_succ b l' c
      by_cases hc : (writeStr l').halted c = true
      · -- 已停机：两边都原地不动
        have hc' : (writeStr (b :: l')).halted ⟨Fin.succ c.state, c.tape⟩ = true := by
          rw [hh]; exact hc
        rw [DTM.run_of_halted _ _ hc', DTM.run_of_halted _ _ hc]
      · -- 未停机：一步转移一致，再套归纳假设
        have hcf : (writeStr l').halted c = false := by
          cases h : (writeStr l').halted c <;> simp_all
        have hc' : (writeStr (b :: l')).halted ⟨Fin.succ c.state, c.tape⟩ = false := by
          rw [hh]
          exact hcf
        rw [DTM.run_succ_of_not_halted _ m _ hc',
          DTM.run_succ_of_not_halted _ m _ hcf]
        have hstep : (writeStr (b :: l')).stepConfig ⟨Fin.succ c.state, c.tape⟩
            = ⟨Fin.succ ((writeStr l').stepConfig c).state,
                ((writeStr l').stepConfig c).tape⟩ := by
          simp only [DTM.stepConfig, writeStr]
          rfl
        rw [hstep, ih]

/-- **写入机的运行结果**：从任意纸带 `(L, R)` 出发，`l.length` 步后左侧恰为
    `reverse l ++ L`（即自左向右写入 `l`），读写头停在写入区右侧一格，右侧剩 `R.drop l.length`。
    Exact run shape: `l.length` steps write `l` to the left of `L` and leave the head just
    past the written region, with the remaining right tape `R.drop l.length`. -/
theorem writeStr_run :
    ∀ (l : List Sym) (L R : List Sym),
      (writeStr l).run l.length ⟨(writeStr l).start, Tape.mk L R⟩
        = ⟨(writeStr l).accept, Tape.mk (l.reverse ++ L) (R.drop l.length)⟩
  | [], L, R => rfl
  | b :: l', L, R => by
      -- 第一步：写 `b` 到当前格并右移，落在 `l'` 机器的起始格局
      have hnh : (writeStr (b :: l')).halted ⟨(writeStr (b :: l')).start, Tape.mk L R⟩
          = false := by
        -- 起始状态 0 与接受/拒绝状态 `l'.length + 1` 不同
        have hne : (writeStr (b :: l')).start ≠ (writeStr (b :: l')).accept := by
          intro h
          have hv := congrArg Fin.val h
          simp [writeStr] at hv
        have hrej : (writeStr (b :: l')).reject = (writeStr (b :: l')).accept := rfl
        simp [DTM.halted, hne, hrej]
      have h1 : (writeStr (b :: l')).stepConfig ⟨(writeStr (b :: l')).start, Tape.mk L R⟩
          = ⟨Fin.succ (writeStr l').start, Tape.mk (b :: L) R.tail⟩ := by
        simp only [DTM.stepConfig, writeStr, writeStrStep, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]
        rfl
      -- 第一步之后，后续 `l'.length` 步交给嵌入引理与归纳假设
      -- （`(b :: l').length` 与 `l'.length + 1` 定义相等，先改写目标形态）
      show (writeStr (b :: l')).run (l'.length + 1) ⟨(writeStr (b :: l')).start, Tape.mk L R⟩
        = ⟨(writeStr (b :: l')).accept,
            Tape.mk ((b :: l').reverse ++ L) (R.drop (l'.length + 1))⟩
      rw [DTM.run_succ_of_not_halted _ l'.length _ hnh, h1]
      rw [show (writeStr (b :: l')).run l'.length ⟨Fin.succ (writeStr l').start,
            Tape.mk (b :: L) R.tail⟩
          = ⟨Fin.succ ((writeStr l').run l'.length ⟨(writeStr l').start, Tape.mk (b :: L) R.tail⟩).state,
              ((writeStr l').run l'.length ⟨(writeStr l').start, Tape.mk (b :: L) R.tail⟩).tape⟩
        from writeStr_run_succ b l' l'.length ⟨(writeStr l').start, Tape.mk (b :: L) R.tail⟩]
      rw [writeStr_run l' (b :: L) R.tail]
      -- 两边的纸带形态一致：`reverse` 与 `drop` 的简单改写
      rw [List.drop_tail]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rfl

end DTM

end Pnp
