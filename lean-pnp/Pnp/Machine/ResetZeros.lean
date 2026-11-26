/-
  文件：Pnp/Machine/ResetZeros.lean
  主题：溢出后的「整块清零」机 `resetZeros`。

  用途：枚举计数器溢出时（`binIncFlag` 进入状态 2），把整块数据重新写成 0，
  以模拟「模 `2^T` 回绕」，随后停机接受。

  约定与 `Machine/Inc.lean` 一致：`some false` = 0，`some true` = 1。

  运行方式：
    - 状态 0：当前格是块右侧空白，先把它写成 0 并向左跨入数据区；
    - 状态 1：一路向左，把每格都写成 0，直到读到左侧空白；
    - 状态 2：接受（读完空白后右移一格，头停在块首）。
-/

import Pnp.Classes
import Pnp.Machine.Inc
import Pnp.Machine.Double

namespace Pnp

namespace DTM

/-- 4 状态清零机：0 从右侧空白跨入，1 向左覆写为 0，2 接受，3 拒绝（不使用）。 -/
def resetZeros : DTM 4 where
  step := fun s a =>
    if s.val = 0 then (1, some false, Dir.left)
    else if s.val = 1 then
      if a = none then (2, a, Dir.right) else (1, some false, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 3

/-- 扫描阶段：从块内任意非空白格出发，向左把 `l` 与当前格全部写成 0，
    `|l|+2` 步后接受，头停在块首（左侧只剩一个空白）。 -/
theorem resetZeros_scan (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      resetZeros.run (l.length + 2)
        { state := (1 : Fin 4), tape := { left := l, right := a :: r } } =
    { state := (2 : Fin 4),
      tape := { left := [none],
                right := List.replicate (l.length + 1) (some false) ++ r } }
  | [], _ => by
      -- 当前格写成 0 并向左，边界补空白；再读到空白转入接受
      have hhalt : resetZeros.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := a :: r } } = false := by
        simp [DTM.halted, resetZeros]
      have hstep : resetZeros.stepConfig
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := ([] : List Sym), right := none :: some false :: r } } := by
        simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : resetZeros.halted
          { state := (1 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: some false :: r } } = false := by
        simp [DTM.halted, resetZeros]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2]
      simp [DTM.run, DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  | x :: xs, hne => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : resetZeros.halted
          { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } } = false := by
        simp [DTM.halted, resetZeros]
      have hstep : resetZeros.stepConfig
          { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := xs, right := x :: some false :: r } } := by
        simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ _ _ hhalt, hstep,
        resetZeros_scan x (some false :: r) hx xs hxs]
      simp [List.replicate_succ', List.append_assoc]

/-- 整机：从溢出结束格局（头在块右侧空白、左侧是「1 后面跟 `k` 个 0」）出发，
    `k+3` 步后整块清零并接受，头停在块首。 -/
theorem resetZeros_run (k : Nat) (e : List Sym) (he : e = [] ∨ e = [none]) :
    resetZeros.run (k + 3)
      { state := (0 : Fin 4),
        tape := { left := some true :: List.replicate k (some false), right := e } } =
    { state := (2 : Fin 4),
      tape := { left := [none], right := List.replicate (k + 2) (some false) } } := by
  have hhalt : resetZeros.halted
      { state := (0 : Fin 4),
        tape := { left := some true :: List.replicate k (some false), right := e } } = false := by
    simp [DTM.halted, resetZeros]
  have hstep : resetZeros.stepConfig
      { state := (0 : Fin 4),
        tape := { left := some true :: List.replicate k (some false), right := e } }
      = { state := (1 : Fin 4),
          tape := { left := List.replicate k (some false),
                    right := some true :: some false :: [] } } := by
    rcases he with rfl | rfl <;>
      simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [show k + 3 = ((List.replicate k (some false)).length + 2) + 1 by simp,
    DTM.run_succ_of_not_halted _ ((List.replicate k (some false)).length + 2) _ hhalt, hstep,
    resetZeros_scan (some true) [some false] (by decide) (List.replicate k (some false))
      (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)]
  simp [List.replicate_succ']

/-- 扫描阶段的状态不变式：`|l|+2` 步以内始终停在状态 1（不会提前停机）。 -/
theorem resetZeros_scan_state (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      ∀ m : Nat, m < l.length + 2 →
        (resetZeros.run m
          { state := (1 : Fin 4), tape := { left := l, right := a :: r } }).state = 1
  | [], _, m, hm => by
      simp only [List.length_nil] at hm
      have hm2 : m = 0 ∨ m = 1 := by omega
      rcases hm2 with rfl | rfl
      · rfl
      · have hhalt : resetZeros.halted
            { state := (1 : Fin 4),
              tape := { left := ([] : List Sym), right := a :: r } } = false := by
          simp [DTM.halted, resetZeros]
        rw [show 1 = 0 + 1 by rfl, DTM.run_succ_of_not_halted _ 0 _ hhalt]
        simp [DTM.run, DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
  | x :: xs, hne, m, hm => by
      rcases m with _ | m
      · rfl
      · have hx : x ≠ none := hne x List.mem_cons_self
        have hxs : ∀ y ∈ xs, y ≠ none :=
          fun y hy => hne y (List.mem_cons_of_mem _ hy)
        have hhalt : resetZeros.halted
            { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } } = false := by
          simp [DTM.halted, resetZeros]
        have hstep : resetZeros.stepConfig
            { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } }
            = { state := (1 : Fin 4),
                tape := { left := xs, right := x :: some false :: r } } := by
          simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, ha]
        rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
        exact resetZeros_scan_state x (some false :: r) hx xs hxs m (by
          simp only [List.length_cons] at hm
          omega)

/-- 整机的非停机前缀：`k+3` 步以内都不会停机。 -/
theorem resetZeros_run_nonhalt (k : Nat) (e : List Sym) (he : e = [] ∨ e = [none]) :
    ∀ m : Nat, m < k + 3 →
      resetZeros.halted
        (resetZeros.run m
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := e } }) = false
  | 0, _ => by simp [DTM.run, DTM.halted, resetZeros]
  | m + 1, hm => by
      have hhalt : resetZeros.halted
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := e } } = false := by
        simp [DTM.halted, resetZeros]
      have hstep : resetZeros.stepConfig
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := e } }
          = { state := (1 : Fin 4),
              tape := { left := List.replicate k (some false),
                        right := some true :: some false :: [] } } := by
        rcases he with rfl | rfl <;>
          simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
      have hstate := resetZeros_scan_state (some true) [some false] (by decide)
        (List.replicate k (some false))
        (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)
        m (by simp only [List.length_replicate]; omega)
      rw [DTM.halted, hstate]
      decide


/-- 扫描阶段（左侧多一个空白）：`l` 全非空白、其左侧再加一个空白，
    `|l|+2` 步后接受并读到那个空白，全部数据写成 0。 -/
theorem resetZeros_scan_blank (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      resetZeros.run (l.length + 2)
        { state := (1 : Fin 4),
          tape := { left := l ++ [none], right := a :: r } } =
      { state := (2 : Fin 4),
        tape := { left := [none], right := List.replicate (l.length + 1) (some false) ++ r } }
  | [], _ => by
      have hhalt : resetZeros.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym) ++ [none], right := a :: r } } = false := by
        simp [DTM.halted, resetZeros]
      have hstep : resetZeros.stepConfig
          { state := (1 : Fin 4), tape := { left := ([] : List Sym) ++ [none], right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := ([] : List Sym), right := none :: some false :: r } } := by
        simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : resetZeros.halted
          { state := (1 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: some false :: r } } = false := by
        simp [DTM.halted, resetZeros]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2]
      simp [DTM.run, DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  | x :: xs, hne => by
      simp only [List.cons_append]
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : resetZeros.halted
          { state := (1 : Fin 4),
            tape := { left := x :: (xs ++ [none]), right := a :: r } } = false := by
        simp [DTM.halted, resetZeros]
      have hstep : resetZeros.stepConfig
          { state := (1 : Fin 4),
            tape := { left := x :: (xs ++ [none]), right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := xs ++ [none], right := x :: some false :: r } } := by
        simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ _ _ hhalt, hstep,
        resetZeros_scan_blank x (some false :: r) hx xs hxs]
      simp [List.replicate_succ, cons_replicate_append, List.cons_append]

/-- 扫描阶段（左侧多一个空白）的状态不变式：`|l|+2` 步以内始终停在状态 1。 -/
theorem resetZeros_scan_blank_state (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      ∀ m : Nat, m < l.length + 2 →
        (resetZeros.run m
          { state := (1 : Fin 4),
            tape := { left := l ++ [none], right := a :: r } }).state = 1
  | [], _, m, hm => by
      simp only [List.length_nil] at hm
      have hm2 : m = 0 ∨ m = 1 := by omega
      rcases hm2 with rfl | rfl
      · rfl
      · have hhalt : resetZeros.halted
            { state := (1 : Fin 4),
              tape := { left := ([] : List Sym) ++ [none], right := a :: r } } = false := by
          simp [DTM.halted, resetZeros]
        rw [show 1 = 0 + 1 by rfl, DTM.run_succ_of_not_halted _ 0 _ hhalt]
        simp [DTM.run, DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
  | x :: xs, hne, m, hm => by
      rcases m with _ | m
      · rfl
      · simp only [List.cons_append]
        have hx : x ≠ none := hne x List.mem_cons_self
        have hxs : ∀ y ∈ xs, y ≠ none :=
          fun y hy => hne y (List.mem_cons_of_mem _ hy)
        have hhalt : resetZeros.halted
            { state := (1 : Fin 4),
              tape := { left := x :: (xs ++ [none]), right := a :: r } } = false := by
          simp [DTM.halted, resetZeros]
        have hstep : resetZeros.stepConfig
            { state := (1 : Fin 4),
              tape := { left := x :: (xs ++ [none]), right := a :: r } }
            = { state := (1 : Fin 4),
                tape := { left := xs ++ [none], right := x :: some false :: r } } := by
          simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
        rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
        exact resetZeros_scan_blank_state x (some false :: r) hx xs hxs m (by
          simp only [List.length_cons] at hm
          omega)

/-- 两个 0 的短块与任意 0 块的拼接切换（供步数收尾用）。 -/
theorem replicate_two_cons (k : Nat) (f : Sym) :
    List.replicate k f ++ [f, f] = f :: f :: List.replicate k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, ih]

/-- 第二轮起的清零整机：左侧已有一个空白，`k+3` 步后整块清零并接受。 -/
theorem resetZeros_run1 (k : Nat) :
    resetZeros.run (k + 3)
      { state := (0 : Fin 4),
        tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } } =
    { state := (2 : Fin 4),
      tape := { left := [none], right := List.replicate (k + 2) (some false) } } := by
  have hhalt : resetZeros.halted
      { state := (0 : Fin 4),
        tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } } = false := by
    simp [DTM.halted, resetZeros]
  have hstep : resetZeros.stepConfig
      { state := (0 : Fin 4),
        tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } }
      = { state := (1 : Fin 4),
          tape := { left := List.replicate k (some false) ++ [none],
                    right := some true :: some false :: [] } } := by
    simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [show k + 3 = ((List.replicate k (some false)).length + 2) + 1 by simp,
    DTM.run_succ_of_not_halted _ ((List.replicate k (some false)).length + 2) _ hhalt, hstep,
    resetZeros_scan_blank (some true) [some false] (by decide) (List.replicate k (some false))
      (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)]
  rw [List.length_replicate]
  rw [replicate_succ_cons k (some false), List.cons_append, cons_replicate_append,
    replicate_two_cons,
    show k + 2 = (k + 1) + 1 by omega, replicate_succ_cons, replicate_succ_cons]

/-- 第二轮起的清零整机：`k+3` 步以内不停机。 -/
theorem resetZeros_run1_nonhalt (k : Nat) :
    ∀ m : Nat, m < k + 3 →
      resetZeros.halted
        (resetZeros.run m
          { state := (0 : Fin 4),
            tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                      right := [none] } }) = false := by
  intro m hm
  cases m with
  | zero => simp [DTM.run, DTM.halted, resetZeros]
  | succ m =>
      have hhalt : resetZeros.halted
          { state := (0 : Fin 4),
            tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } } = false := by
        simp [DTM.halted, resetZeros]
      have hstep : resetZeros.stepConfig
          { state := (0 : Fin 4),
            tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } }
          = { state := (1 : Fin 4),
              tape := { left := List.replicate k (some false) ++ [none],
                        right := some true :: some false :: [] } } := by
        simp [DTM.stepConfig, resetZeros, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
      have hstate := resetZeros_scan_blank_state (some true) [some false] (by decide)
        (List.replicate k (some false))
        (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)
        m (by simp only [List.length_replicate]; omega)
      rw [DTM.halted, hstate]
      decide

end DTM

end Pnp
