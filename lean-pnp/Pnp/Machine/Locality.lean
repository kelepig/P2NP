/-
  文件：Pnp/Machine/Locality.lean
  File: Pnp/Machine/Locality.lean

  主题：图灵机的**局部性原理**——前 `K` 步内读写头最多离开原位 `K` 格，因此只要两张纸带
        在「距读写头 `K` 格以内」逐格一致，前 `K` 步的运行状态就完全相同（纸带也保持一致
        到剩余距离）。这是 E 机把「实际纸带（右侧还挂着输入副本）」与「理想纸带
        （`obsStart` 形态）」对上的基础工具。
  Topic: locality of computation — within `K` steps only the `K` cells around the head matter,
  so two tapes that agree near the head up to distance `K` yield identical runs for `K` steps.
  This lets E relate its real tape to the idealized `obsStart` tape.

  本文件给出（#227）：
    - `Tape.atR` / `Tape.atL`：从当前位置向右/向左第 `i` 格（越界视为空白）；
    - `Tape.AgreeNear`：距离 `n` 以内逐格一致；
    - 单步保持 `Tape.agreeNear_write` / `Tape.agreeNear_move`、`DTM.step_agree`；
    - 主定理 `DTM.run_agree_near` 与状态推论 `DTM.run_state_agree` / `DTM.accepts_at_agree`。
  Position-indexed tape agreement and its preservation through runs.
-/

import Pnp.Classes

namespace Pnp

namespace Tape

/-- 从当前位置向右第 `i` 格（越界视为空白）。 Cell `i` to the right of the head. -/
def atR (t : Tape) (i : Nat) : Sym := t.right.getD i none

/-- 从当前位置向左第 `i` 格（越界视为空白）。 Cell `i` to the left of the head. -/
def atL (t : Tape) (i : Nat) : Sym := t.left.getD i none

/-- 两张纸带在「距读写头 `n` 格以内」逐格一致。
    Two tapes agree on every cell within distance `n` of the head. -/
def AgreeNear (n : Nat) (t1 t2 : Tape) : Prop :=
  (∀ i, i < n → t1.atR i = t2.atR i) ∧
  (∀ i, i < n → t1.atL i = t2.atL i)

/-- 当前格就是向右第 0 格。 The current cell is the right cell at index 0. -/
theorem read_eq_atR (t : Tape) : t.read = t.atR 0 := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [read, atR]
      | cons x xs => simp [read, atR]

/-- 写入后当前格是新符号。 Writing puts `s` at the head. -/
theorem atR_write_zero (t : Tape) (s : Sym) : (t.write s).atR 0 = s := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [write, atR]
      | cons x xs => simp [write, atR]

/-- 写入后第 `i+1` 格不变。 Writing leaves the other cells in place. -/
theorem atR_write_succ (t : Tape) (s : Sym) (i : Nat) :
    (t.write s).atR (i + 1) = t.atR (i + 1) := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [write, atR]
      | cons x xs => simp [write, atR, List.getD_cons_succ]

/-- 写入不影响左侧。 Writing leaves the left side untouched. -/
theorem atL_write (t : Tape) (s : Sym) (i : Nat) : (t.write s).atL i = t.atL i := rfl

/-- 左移后左侧第 `i` 格是原来的第 `i+1` 格。 Shifting left drops one left cell. -/
theorem atL_moveLeft (t : Tape) (i : Nat) : t.moveLeft.atL i = t.atL (i + 1) := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft, atL]
      | cons x xs => simp [moveLeft, atL, List.getD_cons_succ]

/-- 左移后当前格是原来的左侧第 0 格。 After a left move the head cell was the nearest left cell. -/
theorem atR_moveLeft_zero (t : Tape) : t.moveLeft.atR 0 = t.atL 0 := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft, atR, atL]
      | cons x xs => simp [moveLeft, atR, atL]

/-- 左移后第 `i+1` 格是原来的第 `i` 格。 Left/right cells shift by one. -/
theorem atR_moveLeft_succ (t : Tape) (i : Nat) : t.moveLeft.atR (i + 1) = t.atR i := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft, atR]
      | cons x xs => simp [moveLeft, atR]

/-- 右移后左侧第 0 格是原来的当前格。 After a right move the nearest left cell was the head cell. -/
theorem atL_moveRight_zero (t : Tape) : t.moveRight.atL 0 = t.atR 0 := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight, atR, atL]
      | cons x xs => simp [moveRight, atR, atL]

/-- 右移后左侧第 `i+1` 格是原来的第 `i` 格。 Left cells shift by one. -/
theorem atL_moveRight_succ (t : Tape) (i : Nat) :
    t.moveRight.atL (i + 1) = t.atL i := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight, atL]
      | cons x xs => simp [moveRight, atL]

/-- 右移后右侧第 `i` 格是原来的第 `i+1` 格。 Right cells shift by one. -/
theorem atR_moveRight (t : Tape) (i : Nat) : t.moveRight.atR i = t.atR (i + 1) := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight, atR]
      | cons x xs => simp [moveRight, atR, List.getD_cons_succ]

/-- 一致性可弱化：范围更大的一致性蕴含范围更小的。 Agreement weakens with the radius. -/
theorem agreeNear_mono {m n : Nat} (h : m ≤ n) {t1 t2 : Tape} (hA : AgreeNear n t1 t2) :
    AgreeNear m t1 t2 :=
  ⟨fun i hi => hA.1 i (by omega), fun i hi => hA.2 i (by omega)⟩

/-- 半径 ≥ 1 的一致性给出读数一致。 Nonzero agreement fixes the read symbol. -/
theorem agreeNear_read {n : Nat} {t1 t2 : Tape} (hA : AgreeNear (n + 1) t1 t2) :
    t1.read = t2.read := by
  rw [read_eq_atR, read_eq_atR]
  exact hA.1 0 (by omega)

/-- 同符号写入不改变一致性半径（只改动当前格，读头不动）。
    Writing the same symbol preserves the agreement radius (the head does not move). -/
theorem agreeNear_write {n : Nat} {t1 t2 : Tape} (hA : AgreeNear n t1 t2)
    (s : Sym) : AgreeNear n (t1.write s) (t2.write s) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    cases i with
    | zero => rw [atR_write_zero, atR_write_zero]
    | succ j =>
        rw [atR_write_succ, atR_write_succ]
        exact hA.1 (j + 1) (by omega)
  · intro i hi
    rw [atL_write, atL_write]
    exact hA.2 i hi

/-- 同方向移动把半径 `n+1` 的一致性降到半径 `n`。
    Moving the same way drops the agreement radius by one. -/
theorem agreeNear_move {n : Nat} {t1 t2 : Tape} (hA : AgreeNear (n + 1) t1 t2)
    (d : Dir) : AgreeNear n (t1.move d) (t2.move d) := by
  cases d with
  | left =>
      show AgreeNear n t1.moveLeft t2.moveLeft
      refine ⟨?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            rw [atR_moveLeft_zero, atR_moveLeft_zero]
            exact hA.2 0 (by omega)
        | succ j =>
            rw [atR_moveLeft_succ, atR_moveLeft_succ]
            exact hA.1 j (by omega)
      · intro i hi
        rw [atL_moveLeft, atL_moveLeft]
        exact hA.2 (i + 1) (by omega)
  | right =>
      show AgreeNear n t1.moveRight t2.moveRight
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [atR_moveRight, atR_moveRight]
        exact hA.1 (i + 1) (by omega)
      · intro i hi
        cases i with
        | zero =>
            rw [atL_moveRight_zero, atL_moveRight_zero]
            exact hA.1 0 (by omega)
        | succ j =>
            rw [atL_moveRight_succ, atL_moveRight_succ]
            exact hA.2 j (by omega)
  | stay =>
      show AgreeNear n t1 t2
      exact agreeNear_mono (by omega) hA

end Tape

namespace DTM

variable {q : Nat}

/-- 状态相同 + 半径 `n+1` 的纸带一致性 ⇒ 一步之后状态仍相同、半径 `n` 的纸带仍一致。
    One step preserves state equality and degrades near-agreement by one. -/
theorem step_agree (M : DTM q) {n : Nat} {c1 c2 : Config q}
    (hs : c1.state = c2.state) (hA : Tape.AgreeNear (n + 1) c1.tape c2.tape) :
    (M.stepConfig c1).state = (M.stepConfig c2).state ∧
      Tape.AgreeNear n (M.stepConfig c1).tape (M.stepConfig c2).tape := by
  have hr : c1.tape.read = c2.tape.read := Tape.agreeNear_read hA
  have hstep : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, hr]
  refine ⟨?_, ?_⟩
  · rw [stepConfig_state, stepConfig_state, hstep]
  · unfold DTM.stepConfig
    rw [hstep]
    exact Tape.agreeNear_move (Tape.agreeNear_write hA _) _

/-- **局部性主定理**：两张纸带在半径 `n+k` 内一致、状态相同 ⇒ 运行 `k` 步后状态相同，
    纸带在半径 `n` 内仍一致。
    Locality: agreement within radius `n+k` gives equal states after `k` steps and agreement
    within radius `n`. -/
theorem run_agree_near (M : DTM q) (k : Nat) :
    ∀ (n : Nat) (c1 c2 : Config q), c1.state = c2.state →
      Tape.AgreeNear (n + k) c1.tape c2.tape →
      (M.run k c1).state = (M.run k c2).state ∧
        Tape.AgreeNear n (M.run k c1).tape (M.run k c2).tape := by
  induction k with
  | zero =>
      intro n c1 c2 hs hA
      rw [Nat.add_zero] at hA
      exact ⟨hs, hA⟩
  | succ k ih =>
      intro n c1 c2 hs hA
      rw [show n + (k + 1) = (n + k) + 1 from by omega] at hA
      have hh : M.halted c1 = M.halted c2 := by unfold DTM.halted; rw [hs]
      by_cases hc : M.halted c1 = true
      · -- 已停机：两边都冻结在原格局
        have hc2 : M.halted c2 = true := by rw [← hh]; exact hc
        rw [run_of_halted M c1 hc (k + 1), run_of_halted M c2 hc2 (k + 1)]
        exact ⟨hs, Tape.agreeNear_mono (by omega) hA⟩
      · -- 未停机：两边各走一步，再用归纳假设
        have hc0 : M.halted c1 = false := by
          cases h : M.halted c1 with
          | false => rfl
          | true => exact absurd h hc
        have hc2 : M.halted c2 = false := by rw [← hh]; exact hc0
        rw [run_succ_of_not_halted M k c1 hc0, run_succ_of_not_halted M k c2 hc2]
        obtain ⟨hst, hAg⟩ := step_agree M hs hA
        exact ih n (M.stepConfig c1) (M.stepConfig c2) hst hAg

/-- **状态级推论**：半径 `K` 内一致 ⇒ 前 `K` 步（任意 `k ≤ K`）状态相同。
    State-level corollary: agreement within radius `K` gives equal states after `k ≤ K` steps. -/
theorem run_state_agree (M : DTM q) (K k : Nat) (hK : k ≤ K) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hA : Tape.AgreeNear K c1.tape c2.tape) :
    (M.run k c1).state = (M.run k c2).state := by
  have h := (run_agree_near M k (K - k) c1 c2 hs (by
    rw [Nat.sub_add_cancel hK]
    exact hA)).1
  exact h

/-- **判定级推论**：半径 `K` 内一致 ⇒ 跑满 `K` 步后接受与否相同。
    Verdict-level corollary: agreement within radius `K` preserves acceptance after `K` steps. -/
theorem run_accept_agree (M : DTM q) (K : Nat) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hA : Tape.AgreeNear K c1.tape c2.tape) :
    ((M.run K c1).state = M.accept ↔ (M.run K c2).state = M.accept) := by
  have h := run_state_agree M K K (Nat.le_refl K) c1 c2 hs hA
  rw [h]

end DTM

end Pnp
