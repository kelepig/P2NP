/-
  文件：Pnp/Machine/ZeroCheck.lean
  主题：检查二进制计数器块是否全为 0（枚举循环的停机条件）。

  计数器块约定同 `Machine/Inc.lean`：`some false` = 0，`some true` = 1，低位在左。
  本机器的 `binZeroCheck` 从块首向右扫：
    - 遇到 0 继续；
    - 遇到 1 进入拒绝状态 2（不是全 0）；
    - 遇到空白（块尾）进入接受状态 1（全 0）。

  用途：计数器加一后若整块回到全 0，说明 `2^位数` 个值已枚举完，循环应停止。
-/

import Pnp.Machine.Inc

namespace Pnp

namespace DTM

/-- 3 状态全零检查机：0 扫描，1 全零（接受），2 发现 1（拒绝）。 -/
def binZeroCheck : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = some false then (0, a, Dir.right)
      else if a = some true then (2, a, Dir.stay)
      else (1, a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-- 整块都是 0（之后是纸带末端 `e`，可为空或一个空白）：
    `m+1` 步后进入接受状态 1，纸带右侧统一为 `[none]`。 -/
theorem binZeroCheck_all (L : List Sym) (m : Nat) (e : List Sym)
    (he : e = [] ∨ e = [none]) :
    binZeroCheck.run (m + 1)
      { state := (0 : Fin 3),
        tape := { left := L, right := List.replicate m (some false) ++ e } } =
    { state := (1 : Fin 3),
      tape := { left := List.replicate m (some false) ++ L, right := [none] } } := by
  induction m generalizing L with
  | zero =>
      have hhalt : binZeroCheck.halted
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate 0 (some false) ++ e } } = false := by
        simp [DTM.halted, binZeroCheck]
      have hstep : binZeroCheck.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate 0 (some false) ++ e } }
          = { state := (1 : Fin 3), tape := { left := L, right := [none] } } := by
        rcases he with rfl | rfl <;>
          simp [DTM.stepConfig, binZeroCheck, Tape.read, Tape.write, Tape.move, List.replicate]
      rw [DTM.run_succ_of_not_halted binZeroCheck 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ m ih =>
      have hhalt : binZeroCheck.halted
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate (m + 1) (some false) ++ e } } = false := by
        simp [DTM.halted, binZeroCheck]
      have hstep : binZeroCheck.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L, right := List.replicate (m + 1) (some false) ++ e } }
          = { state := (0 : Fin 3),
              tape := { left := some false :: L,
                        right := List.replicate m (some false) ++ e } } := by
        simp [DTM.stepConfig, binZeroCheck, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          replicate_succ_cons]
      rw [DTM.run_succ_of_not_halted binZeroCheck (m + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 前 `k` 个 0 之后遇到 1：`k+1` 步进入拒绝状态 2（块不是全 0）。 -/
theorem binZeroCheck_found (L : List Sym) (k : Nat) (rest : List Sym) :
    binZeroCheck.run (k + 1)
      { state := (0 : Fin 3),
        tape := { left := L,
                  right := List.replicate k (some false) ++ some true :: rest } } =
    { state := (2 : Fin 3),
      tape := { left := List.replicate k (some false) ++ L, right := some true :: rest } } := by
  induction k generalizing L with
  | zero =>
      have hhalt : binZeroCheck.halted
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate 0 (some false) ++ some true :: rest } } = false := by
        simp [DTM.halted, binZeroCheck]
      have hstep : binZeroCheck.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate 0 (some false) ++ some true :: rest } }
          = { state := (2 : Fin 3),
              tape := { left := L, right := some true :: rest } } := by
        simp [DTM.stepConfig, binZeroCheck, Tape.read, Tape.write, Tape.move, List.replicate]
      rw [DTM.run_succ_of_not_halted binZeroCheck 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      have hhalt : binZeroCheck.halted
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate (k + 1) (some false) ++ some true :: rest } } = false := by
        simp [DTM.halted, binZeroCheck]
      have hstep : binZeroCheck.stepConfig
          { state := (0 : Fin 3),
            tape := { left := L,
                      right := List.replicate (k + 1) (some false) ++ some true :: rest } }
          = { state := (0 : Fin 3),
              tape := { left := some false :: L,
                        right := List.replicate k (some false) ++ some true :: rest } } := by
        simp [DTM.stepConfig, binZeroCheck, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          replicate_succ_cons]
      rw [DTM.run_succ_of_not_halted binZeroCheck (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

end DTM

end Pnp
