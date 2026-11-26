/-
  文件：Pnp/Machine/WriteStrL.lean
  File: Pnp/Machine/WriteStrL.lean

  主题：左向常量串写入机——把给定符号串**自右向左**写到读写头左侧的若干格上。
  Topic: a leftward constant-string writer: writes a given symbol list into the cells to
  the left of the head, one cell per element, walking left.

  为什么需要它：区域编码写在只读输入副本的左侧（`docs/07` 布局细化 #146），
  每格编码 `[codeFst a, codeSnd a, mark]` 必须落在原位置左侧的连续格上，
  左向写入只能「先左移、再写入」交替进行（同一格写+移会把旧符号夹进写入串）。
  Why: the region encoding must be laid out to the left of the read-only input copy; a
  leftward write must alternate "move left, then write", so each symbol costs two states.

  与 `writeStr`（右向、每符号一步）对称：本机每符号两态（`2k` 左移、`2k+1` 写入），
  共 `2 * l.length + 1` 个状态，起始 0、终止 `2 * l.length`。
  Symmetric to `writeStr`: two states per symbol, `2 * l.length + 1` states in total.

  本文件给出：
    - `writeStrL`（机器定义）与三件套 `writeStrL_step_succ` / `writeStrL_halted_succ`
      / `writeStrL_run_succ`（按串归纳的状态上移两格嵌入）；
    - `writeStrL_run`：从左端有足够格子的纸带出发，`2 * l.length` 步后
      `left` 恰为剩下未用的左带、`right` 为 `l.reverse ++ R`（即自左向右读作 `l`）。
  This file gives the machine, the two-state embedding lemmas, and its exact run shape.
-/

import Pnp.Machine.WriteCodeL

namespace Pnp

namespace DTM

/-- 转移结果的状态上移两格（`Fin.succ` 两次），纸带动作不变；供子机嵌入使用。
    Shift a transition's next state by two, keeping the tape action. -/
def stepSucc2 {n : Nat} (v : Fin n × Sym × Dir) : Fin (n + 2) × Sym × Dir :=
  (Fin.succ (Fin.succ v.1), v.2.1, v.2.2)

/-- **左向常量串写入机的转移函数**：状态 `2k` 左移一格、`2k+1` 写入第 `k` 个符号。
    按待写串递归定义：状态 0/1 处理首符号，状态 ≥ 2 照抄「剩余串的机器」（状态下移两格）。
    Transition function: state `2k` moves left, state `2k+1` writes the k-th symbol;
    for the tail, states are shifted down by two. -/
def writeStrLStep :
    (l : List Sym) → Fin (2 * l.length + 1) → Sym → Fin (2 * l.length + 1) × Sym × Dir
  | [], st, a => (st, a, Dir.stay)
  | b :: l', st, a =>
      if st.val = 0 then
        (⟨1, by simp only [List.length_cons]; omega⟩, a, Dir.left)
      else if st.val = 1 then
        (⟨2, by simp only [List.length_cons]; omega⟩, b, Dir.stay)
      else
        stepSucc2 (writeStrLStep l' ⟨st.val - 2, by
          have h := st.isLt
          simp only [List.length_cons] at h
          omega⟩ a)

/-- **左向常量串写入机**：`2 * l.length + 1` 个状态，从状态 0 出发，逐格左移写入 `l`，
    走到状态 `2 * l.length` 即停机。
    The writer has `2 * l.length + 1` states; from state 0 it writes `l` cell by cell to
    the left and halts at state `2 * l.length`. -/
def writeStrL (l : List Sym) : DTM (2 * l.length + 1) where
  step := writeStrLStep l
  start := ⟨0, by omega⟩
  accept := ⟨2 * l.length, by omega⟩
  reject := ⟨2 * l.length, by omega⟩

/-- **一步嵌入**：`b :: l'` 的机器在状态 `j+2` 的一步，正是 `l'` 的机器在状态 `j`
    的一步（状态上移两格）。
    One-step embedding: at state `j+2` the machine for `b :: l'` mirrors the machine for
    `l'` at state `j`, with the next state shifted by two. -/
theorem writeStrL_step_succ (b : Sym) (l' : List Sym) (j : Nat)
    (hj : j < 2 * l'.length + 1) (a : Sym) :
    writeStrLStep (b :: l') ⟨j + 2, by simp only [List.length_cons]; omega⟩ a
      = stepSucc2 (writeStrLStep l' ⟨j, hj⟩ a) := by
  -- 状态值 `j+2` 既不是 0 也不是 1，故走递归分支
  simp only [writeStrLStep]
  split
  · omega
  · split
    · omega
    · rfl

/-- **停机判定在嵌入下不变**：状态上移两格后是否停机，与原状态一致。 -/
theorem writeStrL_halted_succ (b : Sym) (l' : List Sym) (c : Config (2 * l'.length + 1)) :
    (writeStrL (b :: l')).halted ⟨Fin.succ (Fin.succ c.state), c.tape⟩
      = (writeStrL l').halted c := by
  -- 大机的接受/拒绝状态恰是小机对应状态的 `Fin.succ (Fin.succ ·)`
  have hacc : (writeStrL (b :: l')).accept
      = Fin.succ (Fin.succ (writeStrL l').accept) := rfl
  have hrej : (writeStrL (b :: l')).reject
      = Fin.succ (Fin.succ (writeStrL l').reject) := rfl
  -- 两次 `Fin.succ` 保持相等性
  have hbeq : ∀ x y : Fin (2 * l'.length + 1),
      (Fin.succ (Fin.succ x) == Fin.succ (Fin.succ y)) = (x == y) := by
    intro x y
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.ext_iff, Fin.ext_iff,
      Fin.val_succ, Fin.val_succ, Fin.val_succ, Fin.val_succ, Nat.succ.injEq,
      Nat.succ.injEq]
  simp only [DTM.halted, hacc, hrej, hbeq]

/-- **整段运行的搬运**：`l'` 的机器跑 `m` 步，等价于 `b :: l'` 的机器从（状态上移两格的）
    同一格局跑 `m` 步；纸带完全相同。
    Run transport under the two-state shift. -/
theorem writeStrL_run_succ (b : Sym) (l' : List Sym) :
    ∀ (m : Nat) (c : Config (2 * l'.length + 1)),
      (writeStrL (b :: l')).run m ⟨Fin.succ (Fin.succ c.state), c.tape⟩
        = ⟨Fin.succ (Fin.succ ((writeStrL l').run m c).state), ((writeStrL l').run m c).tape⟩ := by
  intro m
  induction m with
  | zero =>
      intro c
      rfl
  | succ m ih =>
      intro c
      have hh := writeStrL_halted_succ b l' c
      by_cases hc : (writeStrL l').halted c = true
      · -- 已停机：两边都原地不动
        have hc' : (writeStrL (b :: l')).halted ⟨Fin.succ (Fin.succ c.state), c.tape⟩ = true := by
          rw [hh]; exact hc
        rw [DTM.run_of_halted _ _ hc', DTM.run_of_halted _ _ hc]
      · -- 未停机：一步转移一致，再套归纳假设
        have hcf : (writeStrL l').halted c = false := by
          cases h : (writeStrL l').halted c <;> simp_all
        have hc' : (writeStrL (b :: l')).halted ⟨Fin.succ (Fin.succ c.state), c.tape⟩ = false := by
          rw [hh]
          exact hcf
        rw [DTM.run_succ_of_not_halted _ m _ hc',
          DTM.run_succ_of_not_halted _ m _ hcf]
        have hstep : (writeStrL (b :: l')).stepConfig ⟨Fin.succ (Fin.succ c.state), c.tape⟩
            = ⟨Fin.succ (Fin.succ ((writeStrL l').stepConfig c).state),
                ((writeStrL l').stepConfig c).tape⟩ := by
          simp only [DTM.stepConfig, writeStrL]
          rfl
        rw [hstep, ih]

/-- **左向写入机的运行结果**：左带前段恰有 `l.length` 格可用（`ls`）时，`2 * l.length` 步后
    这些格子被从右往左写成 `l`，读写头停在写入段最左格，左带剩 `L`，右带变为
    `l.reverse ++ a :: R`（即写入段自左向右读作 `l`）。
    Exact run shape: with `ls` of the same length as `l` to the left, after `2 * l.length`
    steps those cells hold `l` (right to left), the head rests on the leftmost written cell,
    and the right tape becomes `l.reverse ++ a :: R`. -/
theorem writeStrL_run :
    ∀ (l : List Sym) (ls L R : List Sym) (a : Sym), ls.length = l.length →
      (writeStrL l).run (2 * l.length) ⟨(writeStrL l).start, Tape.mk (ls ++ L) (a :: R)⟩
        = ⟨(writeStrL l).accept, Tape.mk L (l.reverse ++ a :: R)⟩
  | [], ls, L, R, a, h => by
      -- 空串：`ls` 也为空，零步即完成
      have h0 : ls = [] := by
        cases ls with
        | nil => rfl
        | cons x xs => simp at h
      subst h0
      rfl
  | b :: l', ls, L, R, a, h => by
      -- 左带非空：拆出最靠头的一格 `x`
      obtain ⟨x, ls', hls⟩ : ∃ x ls', ls = x :: ls' := by
        cases ls with
        | nil => simp at h
        | cons x xs => exact ⟨x, xs, rfl⟩
      subst hls
      -- 第一步：左移一格（把 `x` 留给下一步写入）
      have hnh0 : (writeStrL (b :: l')).halted
          ⟨(writeStrL (b :: l')).start, Tape.mk ((x :: ls') ++ L) (a :: R)⟩ = false := by
        have hne : (writeStrL (b :: l')).start ≠ (writeStrL (b :: l')).accept := by
          intro hh
          have hv := congrArg Fin.val hh
          simp [writeStrL] at hv
        have hrej : (writeStrL (b :: l')).reject = (writeStrL (b :: l')).accept := rfl
        rw [DTM.halted, hrej, Bool.or_self, Bool.eq_false_iff]
        simpa only [ne_eq, beq_iff_eq] using hne
      show (writeStrL (b :: l')).run (2 * l'.length + 2)
          ⟨(writeStrL (b :: l')).start, Tape.mk ((x :: ls') ++ L) (a :: R)⟩
        = ⟨(writeStrL (b :: l')).accept, Tape.mk L ((b :: l').reverse ++ a :: R)⟩
      rw [DTM.run_succ_of_not_halted _ (2 * l'.length + 1) _ hnh0]
      rw [stepConfig_of_lit _ (writeStrL (b :: l')).start a ((x :: ls') ++ L) R
            (⟨1, by simp only [List.length_cons]; omega⟩ : Fin (2 * (b :: l').length + 1))
            a Dir.left (Tape.mk (ls' ++ L) (x :: a :: R)) (by rfl)
            (by rfl : ((Tape.mk ((x :: ls') ++ L) (a :: R)).write a).move Dir.left
              = Tape.mk (ls' ++ L) (x :: a :: R))]
      -- 第二步：在 `x` 处写下首符号 `b`
      have hnh1 : (writeStrL (b :: l')).halted
          ⟨(⟨1, by simp only [List.length_cons]; omega⟩ : Fin (2 * (b :: l').length + 1)),
            Tape.mk (ls' ++ L) (x :: a :: R)⟩ = false := by
        have hval : ((writeStrL (b :: l')).accept).val = 2 * (b :: l').length := rfl
        have hne : (⟨1, by simp only [List.length_cons]; omega⟩ :
              Fin (2 * (b :: l').length + 1)) ≠ (writeStrL (b :: l')).accept := by
          intro hh
          have hv := congrArg Fin.val hh
          rw [hval] at hv
          simp only [List.length_cons] at hv
          omega
        have hrej : (writeStrL (b :: l')).reject = (writeStrL (b :: l')).accept := rfl
        rw [DTM.halted, hrej, Bool.or_self, Bool.eq_false_iff]
        simpa only [ne_eq, beq_iff_eq] using hne
      rw [DTM.run_succ_of_not_halted _ (2 * l'.length) _ hnh1]
      rw [stepConfig_of_lit _ _ x (ls' ++ L) (a :: R)
            (⟨2, by simp only [List.length_cons]; omega⟩ : Fin (2 * (b :: l').length + 1))
            b Dir.stay (Tape.mk (ls' ++ L) (b :: a :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls' ++ L) (x :: a :: R)).write b).move Dir.stay
              = Tape.mk (ls' ++ L) (b :: a :: R))]
      -- 子机从状态 `2` 出发，正好是「状态 0 上移两格」
      rw [show (⟨2, by simp only [List.length_cons]; omega⟩ : Fin (2 * (b :: l').length + 1))
            = Fin.succ (Fin.succ ((writeStrL l').start)) from rfl]
      rw [writeStrL_run_succ b l' (2 * l'.length)
        ⟨(writeStrL l').start, Tape.mk (ls' ++ L) (b :: a :: R)⟩]
      rw [writeStrL_run l' ls' L (a :: R) b (by simp only [List.length_cons] at h; omega)]
      -- 终态：大机的接受态恰是小机接受态上移两格
      rw [show (writeStrL (b :: l')).accept
            = Fin.succ (Fin.succ (writeStrL l').accept) from rfl]
      -- 两边纸带形态一致
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

end DTM

end Pnp
