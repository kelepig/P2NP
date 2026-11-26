/-
  文件：Pnp/Machine/DigitBack.lean
  File: Pnp/Machine/DigitBack.lean

  主题：从数字区的**右端向左**读一个块值的小机 `readDigitBack`（状态 = 已读的真格数）。
  Topic: a machine that reads one block value **backwards** from the right end of the digit area.

  用途（B5 外层枚举 E）：E 的 B 进制计数器在数字区右端做「加一 / 进位 / 溢出」，
  进位链自右向左推进，因此每轮先要取得**最右块**的值。块编码 `blockCode d = 0 1^(d+2)`，
  故「值 = 真格数 − 2」。
  Purpose (E): the carry chain of E's base-`B` counter runs right to left, so each round
  needs the value of the rightmost block; `blockCode d = 0 1^(d+2)` gives `value = trues - 2`.
-/

import Pnp.Machine.DigitShape

namespace Pnp

namespace DTM

/-- 反向读块值的计数机：状态 0 = 起始（在区尾空白上，左移一格），
    状态 `1..B+1` = 已读到的真格数加一，状态 `B+2` = 终止（未使用）。
    Backwards block reader: state 0 starts on the trailing blank, states `1..B+1` count
    the true cells, state `B+2` is the unused halting state. -/
def readDigitBack (B : Nat) : DTM (B + 3) where
  step := fun st a =>
    if st.val = 0 then (⟨1, by omega⟩, a, Dir.left)
    else if h : st.val < B + 2 then
      match a with
      | some true => (⟨st.val + 1, by omega⟩, a, Dir.left)
      | _ => (st, a, Dir.stay)
    else (st, a, Dir.stay)
  start := 0
  accept := ⟨B + 2, by omega⟩
  reject := ⟨B + 2, by omega⟩

/-- 起始步：状态 0 一律左移一格（从区尾空白移到最右块的真格上）。
    First step: state 0 always moves left, off the trailing blank. -/
theorem readDigitBack_step_start (B : Nat) (a : Sym) (X R : List Sym) :
    (readDigitBack B).stepConfig
        (Config.mk (⟨0, by omega⟩ : Fin (B + 3)) (Tape.mk (a :: X) (none :: R))) =
      Config.mk (⟨1, by omega⟩ : Fin (B + 3)) (Tape.mk X (a :: none :: R)) := by
  simp only [DTM.stepConfig, readDigitBack, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  simp

/-- 计数步：状态 `s ≠ 0`（且 `s < B+2`）读到真格就左移一格、状态加一。
    Counting step: a non-start state on a true cell moves left and increments. -/
theorem readDigitBack_step_true (B s : Nat) (hs0 : s ≠ 0) (hs : s < B + 2)
    (a : Sym) (X R : List Sym) :
    (readDigitBack B).stepConfig
        (Config.mk (⟨s, by omega⟩ : Fin (B + 3)) (Tape.mk (a :: X) (some true :: R))) =
      Config.mk (⟨s + 1, by omega⟩ : Fin (B + 3)) (Tape.mk X (a :: some true :: R)) := by
  simp only [DTM.stepConfig, readDigitBack, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg hs0, dif_pos hs]

/-- 计数状态未停机（`s < B+2`）。A counting state never halts. -/
theorem readDigitBack_halted_false (B s : Nat) (hs : s < B + 2) (t : Tape) :
    (readDigitBack B).halted
      (Config.mk (⟨s, Nat.lt_succ_of_lt hs⟩ : Fin (B + 3)) t) = false := by
  have hne : (⟨s, Nat.lt_succ_of_lt hs⟩ : Fin (B + 3))
      ≠ (⟨B + 2, Nat.lt_succ_self (B + 2)⟩ : Fin (B + 3)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  unfold DTM.halted readDigitBack
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 连续读 `m` 个真格：状态 `s` 变 `s + m`，左侧的真格逐个搬到右侧。
    Reading `m` true cells: the state advances by `m` and the cells move to the right. -/
theorem readDigitBack_count (B : Nat) :
    ∀ (m s : Nat), (hs0 : s ≠ 0) → (hs : s + m < B + 2) → ∀ (X R : List Sym),
      (readDigitBack B).run m
        (Config.mk (⟨s, by omega⟩ : Fin (B + 3))
          (Tape.mk (List.replicate m (some true) ++ X) (some true :: R))) =
      Config.mk (⟨s + m, by omega⟩ : Fin (B + 3))
        (Tape.mk X (List.replicate m (some true) ++ some true :: R)) := by
  intro m
  induction m with
  | zero =>
      intro s _ _ X R
      rfl
  | succ m ih =>
      intro s hs0 hs X R
      have hs2 : s < B + 2 := by omega
      have hhalt : (readDigitBack B).halted
          (Config.mk (⟨s, by omega⟩ : Fin (B + 3))
            (Tape.mk (some true :: (List.replicate m (some true) ++ X)) (some true :: R)))
          = false := readDigitBack_halted_false B s hs2 _
      rw [show List.replicate (m + 1) (some true) ++ X
          = some true :: (List.replicate m (some true) ++ X) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt]
      rw [readDigitBack_step_true B s hs0 hs2 (some true) (List.replicate m (some true) ++ X) R]
      rw [ih (s + 1) (by omega) (by omega) X (some true :: R)]
      rw [replicate_append_cons]
      rw [List.replicate_succ, List.cons_append]
      simp only [Nat.add_comm, Nat.add_left_comm]

/-- **反向读完一个块**：从区尾空白出发，`d+3` 步后状态为 `d+3`，读写头停在块的
    首格 `some false` 上（块整体搬到头部右侧，左侧上下文不变）。
    Reading one block backwards: after `d + 3` steps the state is `d + 3` and the head
    sits on the block's leading `some false` cell. -/
theorem readDigitBack_run (B d : Nat) (hd : d < B) (L R : List Sym) :
    (readDigitBack B).run (d + 3)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 3))
          (Tape.mk (List.replicate (d + 2) (some true) ++ some false :: L) (none :: R))) =
      Config.mk (⟨d + 3, by omega⟩ : Fin (B + 3))
        (Tape.mk L (blockCode d ++ none :: R)) := by
  -- 先把块的真格段拆成「一个真格 + 其余」，便于逐步走位
  rw [show List.replicate (d + 2) (some true) ++ some false :: L
      = some true :: (List.replicate (d + 1) (some true) ++ some false :: L) from by
    rw [show d + 2 = d + 1 + 1 from by omega, List.replicate_succ, List.cons_append]]
  -- 第一步：离开区尾空白，落在最右真格上
  have hhalt0 : (readDigitBack B).halted
      (Config.mk (⟨0, by omega⟩ : Fin (B + 3))
        (Tape.mk (some true :: (List.replicate (d + 1) (some true) ++ some false :: L))
          (none :: R)))
      = false := by
    have hne : (⟨0, by omega⟩ : Fin (B + 3))
        ≠ (⟨B + 2, Nat.lt_succ_self (B + 2)⟩ : Fin (B + 3)) := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_mk] at hv
      omega
    unfold DTM.halted readDigitBack
    rw [beq_eq_false_iff_ne.mpr hne]
    rfl
  rw [DTM.run_succ_of_not_halted _ (d + 2) _ hhalt0]
  rw [readDigitBack_step_start B (some true)
    (List.replicate (d + 1) (some true) ++ some false :: L) R]
  -- 中间 `d+1` 步：读完 `d+1` 个真格
  have haux := readDigitBack_count B (d + 1) 1 (by omega) (by omega)
    (some false :: L) (none :: R)
  have hhalt1 : (readDigitBack B).halted
      ((readDigitBack B).run (d + 1)
        (Config.mk (⟨1, by omega⟩ : Fin (B + 3))
          (Tape.mk (List.replicate (d + 1) (some true) ++ some false :: L)
            (some true :: none :: R)))) = false := by
    rw [haux]
    exact readDigitBack_halted_false B (1 + (d + 1)) (by omega) _
  rw [DTM.run_succ_last _ (d + 1) _ hhalt1]
  rw [haux]
  -- 最后一步：把块首的 `some false` 带回头部
  rw [show List.replicate (d + 1) (some true) ++ some true :: none :: R
      = some true :: (List.replicate d (some true) ++ some true :: none :: R) from by
    rw [List.replicate_succ, List.cons_append]]
  rw [readDigitBack_step_true B (1 + (d + 1)) (by omega) (by omega) (some false) L
    (List.replicate d (some true) ++ some true :: none :: R)]
  -- 形态对齐：两侧都化成「两个真格 + 其余」的形式
  rw [replicate_append_cons]
  simp only [blockCode, show d + 2 = d + 1 + 1 from by omega, List.replicate_succ,
    List.cons_append, List.append_assoc]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end DTM

end Pnp
