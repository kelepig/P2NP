/-
  文件：Pnp/Machine/ReadDigit.lean
  主题：把一段 **unary 数字**（`d` 个 1 后跟一个 0）读进状态的小机 `readUnary`。

  动机：B5 的搜索驱动需要「每轮从纸带取一个选择编号」。选择编号小于常数 B，
  因而可以 unary 编码；机器用状态 `0..B` 计数，读到 0 时状态恰好等于数字 d。

  本文件给出：
    - `readUnary B`：B+1 个状态（0..B-1 计数，状态 B 为终止/未使用）；
    - 单步规格 `readUnary_step_one` / `readUnary_step_zero`；
    - 未停机判定 `readUnary_halted_false`；
    - 主规格 `readUnary_run`：从块首出发 `d+1` 步后，状态 = d，
      读写头停在 0 上，左侧累积读过的 1。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 读 unary 数字的计数机：状态 = 已读到的 1 的个数（`0..B`）。 -/
def readUnary (B : Nat) : DTM (B + 1) where
  step := fun st a =>
    if h : st.val < B then
      match a with
      | some true => (⟨st.val + 1, by omega⟩, a, Dir.right)
      | _ => (st, a, Dir.stay)
    else (st, a, Dir.stay)
  start := 0
  accept := ⟨B, Nat.lt_succ_self B⟩
  reject := ⟨B, Nat.lt_succ_self B⟩

/-- unary 串的拼接：`replicate d a ++ (a :: L) = a :: (replicate d a ++ L)`。 -/
theorem replicate_append_cons {α : Type} (d : Nat) (a : α) (L : List α) :
    List.replicate d a ++ (a :: L) = a :: (List.replicate d a ++ L) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [ih]

/-- 在计数状态 `s < B` 读到 1：计数加一，右移一格。 -/
theorem readUnary_step_one (B s : Nat) (hs : s < B) (L R : List Sym) :
    (readUnary B).stepConfig
      (Config.mk (⟨s, by omega⟩ : Fin (B + 1)) (Tape.mk L (some true :: R))) =
    Config.mk (⟨s + 1, by omega⟩ : Fin (B + 1)) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, readUnary, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [dif_pos hs]

/-- 在计数状态 `s < B` 读到 0：原地不动（数字读完）。 -/
theorem readUnary_step_zero (B s : Nat) (hs : s < B) (L R : List Sym) :
    (readUnary B).stepConfig
      (Config.mk (⟨s, by omega⟩ : Fin (B + 1)) (Tape.mk L (some false :: R))) =
    Config.mk (⟨s, by omega⟩ : Fin (B + 1)) (Tape.mk L (some false :: R)) := by
  simp only [DTM.stepConfig, readUnary, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [dif_pos hs]

/-- 计数状态 `s < B` 未停机。 -/
theorem readUnary_halted_false (B s : Nat) (hs : s < B) (t : Tape) :
    (readUnary B).halted (Config.mk (⟨s, by omega⟩ : Fin (B + 1)) t) = false := by
  have hne : (⟨s, by omega⟩ : Fin (B + 1)) ≠ (⟨B, Nat.lt_succ_self B⟩ : Fin (B + 1)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  unfold DTM.halted readUnary
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 从计数状态 `s` 出发，读 `d` 个 1（`s + d < B`）：状态变为 `s + d`，
    读写头右移 `d` 格，左侧累积读过的 1。 -/
theorem readUnary_run_aux (B s d : Nat) :
    ∀ (h : s + d < B) (L R : List Sym),
      (readUnary B).run d
        (Config.mk (⟨s, by omega⟩ : Fin (B + 1))
          (Tape.mk L (List.replicate d (some true) ++ some false :: R))) =
      Config.mk (⟨s + d, by omega⟩ : Fin (B + 1))
        (Tape.mk (List.replicate d (some true) ++ L) (some false :: R)) := by
  induction d generalizing s with
  | zero =>
      intro h L R
      rfl
  | succ d ih =>
      intro h L R
      have hs : s < B := by omega
      have hprev : s + 1 + d < B := by omega
      have hstep := readUnary_step_one B s hs L (List.replicate d (some true) ++ some false :: R)
      have hhalt := readUnary_halted_false B s hs
        (Tape.mk L (List.replicate (d + 1) (some true) ++ some false :: R))
      rw [DTM.run_succ_of_not_halted _ d _ hhalt]
      simp only [List.replicate_succ, List.cons_append]
      rw [hstep]
      rw [ih (s + 1) hprev (some true :: L) R]
      rw [replicate_append_cons]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 主规格：从块首（计数状态 0）读 unary 数字 `d < B`，`d + 1` 步后状态为 `d`，
    读写头停在 0 上。 -/
theorem readUnary_run (B d : Nat) (hd : d < B) (L R : List Sym) :
    (readUnary B).run (d + 1)
      (Config.mk (⟨0, by omega⟩ : Fin (B + 1))
        (Tape.mk L (List.replicate d (some true) ++ some false :: R))) =
    Config.mk (⟨d, by omega⟩ : Fin (B + 1))
      (Tape.mk (List.replicate d (some true) ++ L) (some false :: R)) := by
  have haux := readUnary_run_aux B 0 d (by omega) L R
  rw [DTM.run_add, haux]
  simp only [Nat.zero_add]
  -- 最后一步：读到 0，原地不动
  have hhalt := readUnary_halted_false B d hd
    (Tape.mk (List.replicate d (some true) ++ L) (some false :: R))
  change (readUnary B).run (0 + 1) _ = _
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt]
  rw [readUnary_step_zero B d hd]
  rfl

/-- 读一段 unary 数字并右移一格进入**下一段**（状态仍为数字本身）。 -/
def readDigitNext (B : Nat) : DTM (B + 1) where
  step := fun st a =>
    if h : st.val < B then
      match a with
      | some true => (⟨st.val + 1, by omega⟩, a, Dir.right)
      | _ => (st, a, Dir.right)
    else (st, a, Dir.stay)
  start := 0
  accept := ⟨B, Nat.lt_succ_self B⟩
  reject := ⟨B, Nat.lt_succ_self B⟩

/-- `readDigitNext` 在计数状态 `s < B` 读到 1：计数加一，右移。 -/
theorem readDigitNext_step_one (B s : Nat) (hs : s < B) (L R : List Sym) :
    (readDigitNext B).stepConfig
      (Config.mk (⟨s, by omega⟩ : Fin (B + 1)) (Tape.mk L (some true :: R))) =
    Config.mk (⟨s + 1, by omega⟩ : Fin (B + 1)) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, readDigitNext, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [dif_pos hs]

/-- `readDigitNext` 在计数状态 `s < B` 读到 0：右移进入下一段。 -/
theorem readDigitNext_step_zero (B s : Nat) (hs : s < B) (L R : List Sym) :
    (readDigitNext B).stepConfig
      (Config.mk (⟨s, by omega⟩ : Fin (B + 1)) (Tape.mk L (some false :: R))) =
    Config.mk (⟨s, by omega⟩ : Fin (B + 1)) (Tape.mk (some false :: L) R) := by
  simp only [DTM.stepConfig, readDigitNext, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [dif_pos hs]

/-- `readDigitNext` 的计数状态未停机。 -/
theorem readDigitNext_halted_false (B s : Nat) (hs : s < B) (t : Tape) :
    (readDigitNext B).halted (Config.mk (⟨s, by omega⟩ : Fin (B + 1)) t) = false := by
  have hne : (⟨s, by omega⟩ : Fin (B + 1)) ≠ (⟨B, Nat.lt_succ_self B⟩ : Fin (B + 1)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  unfold DTM.halted readDigitNext
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 计数引理：从状态 `s` 读 `d` 个 1（`s + d < B`）。 -/
theorem readDigitNext_run_aux (B s d : Nat) :
    ∀ (h : s + d < B) (L R : List Sym),
      (readDigitNext B).run d
        (Config.mk (⟨s, by omega⟩ : Fin (B + 1))
          (Tape.mk L (List.replicate d (some true) ++ some false :: R))) =
      Config.mk (⟨s + d, by omega⟩ : Fin (B + 1))
        (Tape.mk (List.replicate d (some true) ++ L) (some false :: R)) := by
  induction d generalizing s with
  | zero =>
      intro h L R
      rfl
  | succ d ih =>
      intro h L R
      have hs : s < B := by omega
      have hprev : s + 1 + d < B := by omega
      have hstep := readDigitNext_step_one B s hs L (List.replicate d (some true) ++ some false :: R)
      have hhalt := readDigitNext_halted_false B s hs
        (Tape.mk L (List.replicate (d + 1) (some true) ++ some false :: R))
      rw [DTM.run_succ_of_not_halted _ d _ hhalt]
      simp only [List.replicate_succ, List.cons_append]
      rw [hstep]
      rw [ih (s + 1) hprev (some true :: L) R]
      rw [replicate_append_cons]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 主规格：`d+1` 步后状态 = `d`，读写头位于**下一段的首格**（`d < B`）。 -/
theorem readDigitNext_run (B d : Nat) (hd : d < B) (L R : List Sym) :
    (readDigitNext B).run (d + 1)
      (Config.mk (⟨0, by omega⟩ : Fin (B + 1))
        (Tape.mk L (List.replicate d (some true) ++ some false :: R))) =
    Config.mk (⟨d, by omega⟩ : Fin (B + 1))
      (Tape.mk (some false :: List.replicate d (some true) ++ L) R) := by
  have haux := readDigitNext_run_aux B 0 d (by omega) L R
  rw [DTM.run_add, haux]
  simp only [Nat.zero_add]
  have hhalt := readDigitNext_halted_false B d hd
    (Tape.mk (List.replicate d (some true) ++ L) (some false :: R))
  change (readDigitNext B).run (0 + 1) _ = _
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt]
  rw [readDigitNext_step_zero B d hd]
  rfl

end DTM

end Pnp
