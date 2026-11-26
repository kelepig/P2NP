/-
  文件：Pnp/Machine/Inc.lean
  主题：二进制计数器「加一」的单带机器。

  计数器约定：一段连续的非空白块表示二进制数，**低位在左**，
    - `some false` 表示 0；
    - `some true`  表示 1。
  读写头初始指向最低位（块的第一格）。

  「加一」规则（从低位向高位进位）：
    - 读到 1：把它写成 0，继续向高位走；
    - 读到 0：把它写成 1，停止（不再进位）；
    - 读到空白（块尾，说明所有位都是 1）：在块尾追加一个 1，停止。
  结束状态为 1（接受）。

  本文件给出三条运行时引理：
    - `binInc_zero`：最低位是 0，一步完成；
    - `binInc_ones_then_zero`：前 `k` 位是 1、第 `k+1` 位是 0，`k+1` 步完成；
    - `binInc_overflow`：前 `k` 位全是 1，`k+1` 步完成并在末尾长出一位。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- `replicate (n+1) a` 展开成头部元素加剩余（定义上即相等）。 -/
theorem replicate_succ_cons {α : Type} (n : Nat) (a : α) :
    List.replicate (n + 1) a = a :: List.replicate n a := rfl

/-- 3 状态二进制加一机：0 进位扫描，1 完成（接受），2 拒绝。 -/
def binInc : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then (0, some false, Dir.right)
      else if a = some false then (1, some true, Dir.right)
      else (1, some true, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-- 最低位是 0：一步把它写成 1 并停止。 -/
theorem binInc_zero (L : List Sym) (rest : List Sym) :
    binInc.run 1
      { state := (0 : Fin 3), tape := { left := L, right := some false :: rest } } =
    { state := (1 : Fin 3), tape := { left := some true :: L, right := rest } } := by
  have hhalt : binInc.halted
      { state := (0 : Fin 3), tape := { left := L, right := some false :: rest } } = false := by
    simp [DTM.halted, binInc]
  have hstep : binInc.stepConfig
      { state := (0 : Fin 3), tape := { left := L, right := some false :: rest } }
      = { state := (1 : Fin 3), tape := { left := some true :: L, right := rest } } := by
    simp [DTM.stepConfig, binInc, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [DTM.run_succ_of_not_halted binInc 0 _ hhalt, hstep]
  simp [DTM.run]

/-- 前 `k` 位是 1、下一位是 0：`k+1` 步完成（把 1 们清零，把 0 写成 1）。 -/
theorem binInc_ones_then_zero (L : List Sym) (k : Nat) (rest : List Sym) :
    binInc.run (k + 1)
      { state := (0 : Fin 3),
        tape := { left := L,
                  right := List.replicate k (some true) ++ some false :: rest } } =
    { state := (1 : Fin 3),
      tape := { left := some true :: (List.replicate k (some false) ++ L), right := rest } } := by
  induction k generalizing L with
  | zero =>
      have hhalt : binInc.halted
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate 0 (some true) ++ some false :: rest } } = false := by
        simp [DTM.halted, binInc]
      have hstep : binInc.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate 0 (some true) ++ some false :: rest } }
          = { state := (1 : Fin 3), tape := { left := some true :: L, right := rest } } := by
        simp [DTM.stepConfig, binInc, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate]
      rw [DTM.run_succ_of_not_halted binInc 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      have hhalt : binInc.halted
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate (k + 1) (some true) ++ some false :: rest } } = false := by
        simp [DTM.halted, binInc]
      have hstep : binInc.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate (k + 1) (some true) ++ some false :: rest } }
          = { state := (0 : Fin 3),
              tape := { left := some false :: L,
                        right := List.replicate k (some true) ++ some false :: rest } } := by
        simp [DTM.stepConfig, binInc, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          replicate_succ_cons]
      rw [DTM.run_succ_of_not_halted binInc (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 前 `k` 位全是 1（之后是纸带末端 `e`，可为空或一个空白）：
    `k+1` 步完成，并在块尾长出一位 1。 -/
theorem binInc_overflow (L : List Sym) (k : Nat) (e : List Sym)
    (he : e = [] ∨ e = [none]) :
    binInc.run (k + 1)
      { state := (0 : Fin 3),
        tape := { left := L, right := List.replicate k (some true) ++ e } } =
    { state := (1 : Fin 3),
      tape := { left := some true :: (List.replicate k (some false) ++ L), right := [] } } := by
  induction k generalizing L with
  | zero =>
      have hhalt : binInc.halted
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate 0 (some true) ++ e } } = false := by
        simp [DTM.halted, binInc]
      have hstep : binInc.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate 0 (some true) ++ e } }
          = { state := (1 : Fin 3), tape := { left := some true :: L, right := [] } } := by
        rcases he with rfl | rfl <;>
          simp [DTM.stepConfig, binInc, Tape.read, Tape.write, Tape.move, Tape.moveRight,
            List.replicate]
      rw [DTM.run_succ_of_not_halted binInc 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      have hhalt : binInc.halted
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate (k + 1) (some true) ++ e } } = false := by
        simp [DTM.halted, binInc]
      have hstep : binInc.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate (k + 1) (some true) ++ e } }
          = { state := (0 : Fin 3),
              tape := { left := some false :: L,
                        right := List.replicate k (some true) ++ e } } := by
        simp [DTM.stepConfig, binInc, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          replicate_succ_cons]
      rw [DTM.run_succ_of_not_halted binInc (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

end DTM

end Pnp
