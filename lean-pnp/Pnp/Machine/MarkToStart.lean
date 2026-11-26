/-
  文件：Pnp/Machine/MarkToStart.lean
  主题：从模拟区任意位置回到模拟区起点（左端的第一个格）。

  单带模拟器的每一轮循环是：

      （轮首）回到模拟区起点 → `seekMark` 找头标记 → `readCell` 读符号
      → `writeCell` 改写并移动标记 → 下一轮

  其中 `seekMark` 要求读写头正好停在模拟区起点。`markToStart` 负责这件事：

    - 模拟区所有格编码都非空白（`codeCells_ne_none`），区域左端是一个空白分隔符；
    - 因此只要一路左移，遇到空白就说明到了区域左边界，再右移一格即回到起点。

  已证 `markToStart_run`：从区域内任意一格出发，`|左部符号数| + 2` 步后
  回到区域起点，左侧恰好是那一个空白分隔符。

  与 `scanLeft` 的区别：`scanLeft` 停在空白上（状态 2），本机器停在起点（状态 1）。
-/

import Pnp.Machine.ReadCell

namespace Pnp

namespace DTM

/-- 回到模拟区起点：0 = 左移找空白，1 = 接受（已回到起点），2 = 保留不用。 -/
def markToStart : DTM 3 where
  step := fun _ a => if a = none then (1, a, Dir.right) else (0, a, Dir.left)
  start := 0
  accept := 1
  reject := 2

/-- 回到区域起点：左侧 `l` 全非空白、当前格 `a` 非空白时，
    `|l| + 2` 步回到起点（左侧为一个空白分隔符）。 -/
theorem markToStart_run (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      markToStart.run (l.length + 2)
        (Config.mk (0 : Fin 3) (Tape.mk l (a :: r))) =
      Config.mk (1 : Fin 3) (Tape.mk [none] (l.reverse ++ a :: r))
  | [], _ => by
      -- 已在起点：左移补空白，读到空白后右移一格
      have hhalt : markToStart.halted
          (Config.mk (0 : Fin 3) (Tape.mk ([] : List Sym) (a :: r))) = false := by
        simp [DTM.halted, markToStart]
      have hstep : markToStart.stepConfig
          (Config.mk (0 : Fin 3) (Tape.mk ([] : List Sym) (a :: r)))
          = Config.mk (0 : Fin 3) (Tape.mk ([] : List Sym) (none :: a :: r)) := by
        simp [DTM.stepConfig, markToStart, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : markToStart.halted
          (Config.mk (0 : Fin 3) (Tape.mk ([] : List Sym) (none :: a :: r))) = false := by
        simp [DTM.halted, markToStart]
      have hstep2 : markToStart.stepConfig
          (Config.mk (0 : Fin 3) (Tape.mk ([] : List Sym) (none :: a :: r)))
          = Config.mk (1 : Fin 3) (Tape.mk [none] (a :: r)) := by
        simp [DTM.stepConfig, markToStart, Tape.read, Tape.write, Tape.move,
          Tape.moveRight]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2, hstep2]
      simp [DTM.run]
  | x :: xs, hne => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      -- 一步左移，把 `x` 推到右侧
      have hhalt : markToStart.halted
          (Config.mk (0 : Fin 3) (Tape.mk (x :: xs) (a :: r))) = false := by
        simp [DTM.halted, markToStart]
      have hstep : markToStart.stepConfig
          (Config.mk (0 : Fin 3) (Tape.mk (x :: xs) (a :: r)))
          = Config.mk (0 : Fin 3) (Tape.mk xs (x :: a :: r)) := by
        simp [DTM.stepConfig, markToStart, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ (xs.length + 2) _ hhalt, hstep,
        markToStart_run x (a :: r) hx xs hxs]
      -- 右侧拼接次序修正
      simp [List.reverse_cons, List.append_assoc]

end DTM

end Pnp
