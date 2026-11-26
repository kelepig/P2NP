/-
  文件：Pnp/Machine/Clear.lean
  主题：区域清空机 `clearRight` 与「全 1 检查」机 `allOnesCheck`。

  单带模拟器采用「空白分隔的多区域」布局：

      [计数器块] ␣ [游标块] ␣ [左栈] ␣ [右栈] ␣ …

  其中非空白块之间的空白格是分隔符。每轮模拟结束后需要：

    - `clearRight`：把光标右侧的非空白块整块写成空白（清空栈区/游标区）；
    - `allOnesCheck`：检查一块 0/1（游标块的「已消费」标志、或计数器块）
      是否全是 1（全消费/全 1），以便决定本分支是否还有剩余步数。

  两台机器都约定：光标停在一个空白分隔符上，块在右侧、之后还有一个空白；
  运行步数分别是 `|块|+1`。
-/

import Pnp.Classes
import Pnp.Machine.Double

namespace Pnp

namespace DTM

/-- 清空机：0 = 扫描并写空白，1 = 接受（读到右侧空白），2 = 拒绝（不使用）。 -/
def clearRight : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then (1, a, Dir.stay) else (0, none, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-- 清空机：从块首出发（块全非空白、其后有一个空白），`|块|+1` 步把整块写成空白，
    停在块末尾的空白上；左侧累积写入的空白数。 -/
theorem clearRight_run : ∀ (B : List Sym), (∀ x ∈ B, x ≠ none) →
    ∀ (L R : List Sym),
      clearRight.run (B.length + 1)
        { state := (0 : Fin 3), tape := { left := L, right := B ++ none :: R } } =
      { state := (1 : Fin 3),
        tape := { left := List.replicate B.length none ++ L, right := none :: R } }
  | [], _, L, R => by
      -- 块为空：一步读到空白即接受
      have hhalt : clearRight.halted
          { state := (0 : Fin 3), tape := { left := L, right := ([] : List Sym) ++ none :: R } } = false := by
        simp [DTM.halted, clearRight]
      have hstep : clearRight.stepConfig
          { state := (0 : Fin 3), tape := { left := L, right := ([] : List Sym) ++ none :: R } }
          = { state := (1 : Fin 3), tape := { left := L, right := ([] : List Sym) ++ none :: R } } := by
        simp [DTM.stepConfig, clearRight, Tape.read, Tape.write, Tape.move]
      rw [show ([].length + 1) = 0 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
      simp [DTM.run]
  | x :: xs, hne, L, R => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      -- 一步：把块首写成空白并右移
      have hhalt : clearRight.halted
          { state := (0 : Fin 3), tape := { left := L, right := x :: xs ++ none :: R } } = false := by
        simp [DTM.halted, clearRight]
      have hstep : clearRight.stepConfig
          { state := (0 : Fin 3), tape := { left := L, right := x :: xs ++ none :: R } }
          = { state := (0 : Fin 3), tape := { left := none :: L, right := xs ++ none :: R } } := by
        simp [DTM.stepConfig, clearRight, Tape.read, Tape.write, Tape.move, Tape.moveRight, hx]
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp,
        DTM.run_succ_of_not_halted _ (xs.length + 1) _ hhalt, hstep,
        clearRight_run xs hxs (none :: L) R]
      simp [List.length_cons, List.replicate_succ]
      exact (cons_replicate_append none xs.length L).symm

/-- 全 1 检查机：0 = 向右扫描，1 = 接受（块全 1），2 = 拒绝（遇到 0）。 -/
def allOnesCheck : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then (0, a, Dir.right)
      else if a = some false then (2, a, Dir.stay)
      else (1, a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-- 全 1 检查：块全为 1（其后一个空白）时，`|块|+1` 步后接受。 -/
theorem allOnesCheck_run : ∀ (B : List Sym), (∀ x ∈ B, x = some true) →
    ∀ (L R : List Sym),
      allOnesCheck.run (B.length + 1)
        { state := (0 : Fin 3), tape := { left := L, right := B ++ none :: R } } =
      { state := (1 : Fin 3),
        tape := { left := List.replicate B.length (some true) ++ L, right := none :: R } }
  | [], _, L, R => by
      have hhalt : allOnesCheck.halted
          { state := (0 : Fin 3), tape := { left := L, right := ([] : List Sym) ++ none :: R } } = false := by
        simp [DTM.halted, allOnesCheck]
      have hstep : allOnesCheck.stepConfig
          { state := (0 : Fin 3), tape := { left := L, right := ([] : List Sym) ++ none :: R } }
          = { state := (1 : Fin 3), tape := { left := L, right := ([] : List Sym) ++ none :: R } } := by
        simp [DTM.stepConfig, allOnesCheck, Tape.read, Tape.write, Tape.move]
      rw [show ([].length + 1) = 0 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
      simp [DTM.run]
  | x :: xs, hone, L, R => by
      have hx : x = some true := hone x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y = some true :=
        fun y hy => hone y (List.mem_cons_of_mem _ hy)
      have hhalt : allOnesCheck.halted
          { state := (0 : Fin 3), tape := { left := L, right := x :: xs ++ none :: R } } = false := by
        simp [DTM.halted, allOnesCheck]
      have hstep : allOnesCheck.stepConfig
          { state := (0 : Fin 3), tape := { left := L, right := x :: xs ++ none :: R } }
          = { state := (0 : Fin 3), tape := { left := some true :: L, right := xs ++ none :: R } } := by
        simp [DTM.stepConfig, allOnesCheck, Tape.read, Tape.write, Tape.move, Tape.moveRight, hx]
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp,
        DTM.run_succ_of_not_halted _ (xs.length + 1) _ hhalt, hstep,
        allOnesCheck_run xs hxs (some true :: L) R]
      simp [List.length_cons, List.replicate_succ]
      exact (cons_replicate_append (some true) xs.length L).symm

end DTM

end Pnp
