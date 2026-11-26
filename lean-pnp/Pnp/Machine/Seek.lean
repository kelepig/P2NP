/-
  文件：Pnp/Machine/Seek.lean
  主题：寻找「第一个未处理的源格」，为 unary 倍增机器做准备。

  倍增机器的数据区用两种记号：
    - `some true`：尚未处理的源格；
    - `some false`：已处理的源格或已写出的副本。
  本文件的 `seekTrue` 从数据区左端出发向右扫：
    - 遇到 `some false` 继续右移；
    - 遇到第一个 `some true`：把它改写成 `some false`，进入「找到」状态（1）；
    - 遇到空白：说明源格已全部处理，进入「结束」状态（3）。

  给出的引理：
    - `seekTrue_block_run`：`false^k ++ true :: rest` 上 `k+1` 步找到并标记；
    - `seekTrue_end`：`false^m ++ [none]` 上 `m+1` 步进入结束状态。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 4 状态寻找机：0 向右找 true，1 已找到（非终止），3 源已耗尽（非终止）。 -/
def seekTrue : DTM 4 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then (1, some false, Dir.right)
      else if a = some false then (0, a, Dir.right)
      else (3, a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 3

/-- 从数据区最左格出发，`k` 个已处理格之后遇到第一个未处理格：
    `k+1` 步把它改成已处理并进入状态 1。 -/
theorem seekTrue_block_run (L : List Sym) (k : Nat) (rest : List Sym) :
    seekTrue.run (k + 1)
      { state := (0 : Fin 4),
        tape := { left := L,
                  right := List.replicate k (some false) ++ some true :: rest } } =
    { state := (1 : Fin 4),
      tape := { left := List.replicate (k + 1) (some false) ++ L, right := rest } } := by
  induction k generalizing L with
  | zero =>
      -- 直接遇到 true：一步改写并右移
      have hhalt : seekTrue.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate 0 (some false) ++ some true :: rest } } = false := by
        simp [DTM.halted, seekTrue]
      have hstep : seekTrue.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate 0 (some false) ++ some true :: rest } }
          = { state := (1 : Fin 4), tape := { left := some false :: L, right := rest } } := by
        rfl
      rw [DTM.run_succ_of_not_halted seekTrue 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      -- 先跨过一个 false，再递归
      have hhalt : seekTrue.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (k + 1) (some false) ++ some true :: rest } } = false := by
        simp [DTM.halted, seekTrue]
      have hstep : seekTrue.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (k + 1) (some false) ++ some true :: rest } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate k (some false) ++ some true :: rest } } := by
        rfl
      rw [DTM.run_succ_of_not_halted seekTrue (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 源格已全部处理（只剩 false 和结尾空白）：`m+1` 步进入结束状态 3。 -/
theorem seekTrue_end (L : List Sym) (m : Nat) :
    seekTrue.run (m + 1)
      { state := (0 : Fin 4),
        tape := { left := L,
                  right := List.replicate m (some false) ++ [none] } } =
    { state := (3 : Fin 4),
      tape := { left := List.replicate m (some false) ++ L, right := [none] } } := by
  induction m generalizing L with
  | zero =>
      -- 直接是空白：进入结束状态，纸带不动
      have hhalt : seekTrue.halted
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate 0 (some false) ++ [none] } } = false := by
        simp [DTM.halted, seekTrue]
      rw [DTM.run_succ_of_not_halted seekTrue 0 _ hhalt]
      simp [DTM.run, DTM.stepConfig, seekTrue, Tape.read, Tape.write, Tape.move, List.replicate]
  | succ m ih =>
      have hhalt : seekTrue.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (m + 1) (some false) ++ [none] } } = false := by
        simp [DTM.halted, seekTrue]
      have hstep : seekTrue.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (m + 1) (some false) ++ [none] } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate m (some false) ++ [none] } } := by
        rfl
      rw [DTM.run_succ_of_not_halted seekTrue (m + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

end DTM

end Pnp
