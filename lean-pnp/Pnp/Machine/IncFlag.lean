/-
  文件：Pnp/Machine/IncFlag.lean
  主题：带「溢出标志」的二进制加一机 `binIncFlag`。

  与 `binInc` 的唯一区别：块尾全是 1 时不再把结束状态与「正常加一」混在一起，
  而是进入**独立的中间状态 2**。枚举循环据此分支：
    - 状态 1（接受）：「加一成功、未溢出」，回到块首继续下一轮；
    - 状态 2（中间）：「整块溢出」，转入清零机，随后停机——这正是模 `2^T` 回绕。

  状态约定沿用 `Machine/Inc.lean`：`some false` = 0，`some true` = 1，低位在左。
-/

import Pnp.Machine.Inc
import Pnp.Machine.Double

namespace Pnp

namespace DTM

/-- 4 状态加一机：0 进位扫描，1 完成（接受），2 溢出（中间态），3 拒绝（不使用）。 -/
def binIncFlag : DTM 4 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then (0, some false, Dir.right)
      else if a = some false then (1, some true, Dir.right)
      else (2, some true, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 3

/-- 最低位是 0：一步把它写成 1 并停止。 -/
theorem binIncFlag_zero (L : List Sym) (rest : List Sym) :
    binIncFlag.run 1
      { state := (0 : Fin 4), tape := { left := L, right := some false :: rest } } =
    { state := (1 : Fin 4), tape := { left := some true :: L, right := rest } } := by
  have hhalt : binIncFlag.halted
      { state := (0 : Fin 4), tape := { left := L, right := some false :: rest } } = false := by
    simp [DTM.halted, binIncFlag]
  have hstep : binIncFlag.stepConfig
      { state := (0 : Fin 4), tape := { left := L, right := some false :: rest } }
      = { state := (1 : Fin 4), tape := { left := some true :: L, right := rest } } := by
    simp [DTM.stepConfig, binIncFlag, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  rw [DTM.run_succ_of_not_halted binIncFlag 0 _ hhalt, hstep]
  simp [DTM.run]

/-- 前 `k` 位是 1、下一位是 0：`k+1` 步完成（把 1 们清零，把 0 写成 1）。 -/
theorem binIncFlag_ones_then_zero (L : List Sym) (k : Nat) (rest : List Sym) :
    binIncFlag.run (k + 1)
      { state := (0 : Fin 4),
        tape := { left := L,
                  right := List.replicate k (some true) ++ some false :: rest } } =
    { state := (1 : Fin 4),
      tape := { left := some true :: (List.replicate k (some false) ++ L), right := rest } } := by
  induction k generalizing L with
  | zero =>
      have hhalt : binIncFlag.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate 0 (some true) ++ some false :: rest } } = false := by
        simp [DTM.halted, binIncFlag]
      have hstep : binIncFlag.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate 0 (some true) ++ some false :: rest } }
          = { state := (1 : Fin 4), tape := { left := some true :: L, right := rest } } := by
        simp [DTM.stepConfig, binIncFlag, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate]
      rw [DTM.run_succ_of_not_halted binIncFlag 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      have hhalt : binIncFlag.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (k + 1) (some true) ++ some false :: rest } } = false := by
        simp [DTM.halted, binIncFlag]
      have hstep : binIncFlag.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (k + 1) (some true) ++ some false :: rest } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate k (some true) ++ some false :: rest } } := by
        simp [DTM.stepConfig, binIncFlag, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          replicate_succ_cons]
      rw [DTM.run_succ_of_not_halted binIncFlag (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 前 `k` 位全是 1（之后是纸带末端 `e`，可为空或一个空白）：
    `k+1` 步完成，并在块尾长出一位 1。 -/
theorem binIncFlag_overflow (L : List Sym) (k : Nat) (e : List Sym)
    (he : e = [] ∨ e = [none]) :
    binIncFlag.run (k + 1)
      { state := (0 : Fin 4),
        tape := { left := L, right := List.replicate k (some true) ++ e } } =
    { state := (2 : Fin 4),
      tape := { left := some true :: (List.replicate k (some false) ++ L), right := [] } } := by
  induction k generalizing L with
  | zero =>
      have hhalt : binIncFlag.halted
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate 0 (some true) ++ e } } = false := by
        simp [DTM.halted, binIncFlag]
      have hstep : binIncFlag.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate 0 (some true) ++ e } }
          = { state := (2 : Fin 4), tape := { left := some true :: L, right := [] } } := by
        rcases he with rfl | rfl <;>
          simp [DTM.stepConfig, binIncFlag, Tape.read, Tape.write, Tape.move, Tape.moveRight,
            List.replicate]
      rw [DTM.run_succ_of_not_halted binIncFlag 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      have hhalt : binIncFlag.halted
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate (k + 1) (some true) ++ e } } = false := by
        simp [DTM.halted, binIncFlag]
      have hstep : binIncFlag.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate (k + 1) (some true) ++ e } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate k (some true) ++ e } } := by
        simp [DTM.stepConfig, binIncFlag, Tape.read, Tape.write, Tape.move, Tape.moveRight,
          replicate_succ_cons]
      rw [DTM.run_succ_of_not_halted binIncFlag (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 进位扫描阶段的前缀格局：前 `m` 位都是 1（`m ≤ k`）时，
    `m` 步后仍在状态 0，前 `m` 位已被改写成 0，剩余 `k-m` 位仍是 1。
    块尾之后的内容 `tail` 不参与扫描，可任意。 -/
theorem binIncFlag_scan_ones (L : List Sym) (k m : Nat) (hm : m ≤ k)
    (tail : List Sym) :
    binIncFlag.run m
      { state := (0 : Fin 4),
        tape := { left := L, right := List.replicate k (some true) ++ tail } } =
    { state := (0 : Fin 4),
      tape := { left := List.replicate m (some false) ++ L,
                right := List.replicate (k - m) (some true) ++ tail } } := by
  induction m generalizing k L with
  | zero => simp [DTM.run]
  | succ m ih =>
      -- `m + 1 ≤ k` 说明还有至少一位 1 可以清掉
      have hmk : m < k := hm
      have hk1 : 1 ≤ k := by omega
      have hhalt : binIncFlag.halted
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate k (some true) ++ tail } } = false := by
        simp [DTM.halted, binIncFlag]
      -- 把 `replicate k` 拆成「一位 1 + 剩余 k-1 位」
      have hsplit : List.replicate k (some true)
          = some true :: List.replicate (k - 1) (some true) := by
        rw [show k = (k - 1) + 1 by omega]
        exact replicate_succ_cons (k - 1) (some true)
      have hstep : binIncFlag.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate k (some true) ++ tail } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate (k - 1) (some true) ++ tail } } := by
        rw [hsplit]
        simp [DTM.stepConfig, binIncFlag, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep,
        ih (k := k - 1) (L := some false :: L) (hm := by omega)]
      -- 拼回位数与左半区
      rw [show k - (m + 1) = k - 1 - m by omega]
      simp [replicate_succ_cons, List.cons_append, cons_replicate_append]

end DTM

end Pnp
