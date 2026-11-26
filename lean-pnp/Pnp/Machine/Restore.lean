/-
  文件：Pnp/Machine/Restore.lean
  主题：把一段非空白数据统一恢复成同一种记号。

  复制机器会用 `some false` 标记「已处理」的源格，最后需要把它们
  统一改回 `some true`。本文件给出这个收尾组件：

    - `restoreTrue`：4 状态机器，右扫时把每格都写成 `some true`，遇空白接受；
    - `restoreTrue_run`：对一段非空白数据 xs，`|xs|+1` 步完成，
      纸带右侧只剩一个空白，左侧是「全 true 块 + 原有左内容」。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 4 状态恢复机：状态 0 右扫并把每格写成 `some true`，遇空白接受。 -/
def restoreTrue : DTM 4 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then (2, a, Dir.stay) else (0, some true, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 3

/-- 对非空白块 xs（右侧紧跟一个空白），`restoreTrue` 在 `|xs|+1` 步内
    把所有格改写成 `some true` 并接受。 -/
theorem restoreTrue_run (l : List Sym) (xs : List Sym)
    (hne : ∀ x ∈ xs, x ≠ none) :
    restoreTrue.run (xs.length + 1)
      { state := (0 : Fin 4), tape := { left := l, right := xs ++ [none] } } =
    { state := (2 : Fin 4),
      tape := { left := (xs.map (fun _ => some true)).reverse ++ l, right := [none] } } := by
  induction xs generalizing l with
  | nil =>
      -- 一步：读到空白直接接受，纸带不动
      have hhalt : restoreTrue.halted
          { state := (0 : Fin 4),
            tape := { left := l, right := ([] : List Sym) ++ [none] } } = false := by
        simp [DTM.halted, restoreTrue]
      rw [show ([].length + 1) = 0 + 1 by rfl, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false]
      simp [DTM.run, DTM.stepConfig, restoreTrue, Tape.read, Tape.write, Tape.move]
  | cons x xs ih =>
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      -- 第一步：读到非空白 x，写 some true 并右移
      have hhalt : restoreTrue.halted
          { state := (0 : Fin 4), tape := { left := l, right := (x :: xs) ++ [none] } } = false := by
        simp [DTM.halted, restoreTrue]
      have hstep : restoreTrue.stepConfig
          { state := (0 : Fin 4), tape := { left := l, right := (x :: xs) ++ [none] } }
          = { state := (0 : Fin 4),
              tape := { left := some true :: l, right := xs ++ [none] } } := by
        simp [DTM.stepConfig, restoreTrue, Tape.read, Tape.write, Tape.move, Tape.moveRight, hx]
      rw [show (x :: xs).length + 1 = xs.length + 1 + 1 by simp, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      rw [ih (some true :: l) hxs]
      simp [List.reverse_cons, List.append_assoc]

end DTM

end Pnp
