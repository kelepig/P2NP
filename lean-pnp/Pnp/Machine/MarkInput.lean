/-
  文件：Pnp/Machine/MarkInput.lean
  主题：把整条输入重写成统一记号，并回到纸带左端。

  后续算术（n、n^k 的 unary 表示）希望输入块里所有符号完全一样，
  这样复制机器只需处理「同一种非空白记号」。本文件给出：

    - `markInput`：4 状态机器。第一阶段边读边把每格写成 `some true` 并右移；
      读到空白后转入第二阶段，一路左移，回到最左端的人工空白后接受。
    - `markPhase`：第一阶段恰好 `|w|` 步，纸带左侧累积记号、右侧清空。
    - `rewindFrom_gen`：从任意工作位置左移，弹出全部数据，`|xs|+2` 步后接受。
    - `rewindPhase`：从第一阶段结束的位置继续，`|L|+2` 步后到达左端。
    - `markInput_run`：整机 `2|w|+2` 步完成，终态接受，
      纸带为「一个空白 + 全部输入变成 `some true`」。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 4 状态「标记输入」机器：
    状态 0 向右写记号，状态 1 向左回扫，状态 2 接受，状态 3 拒绝。 -/
def markInput : DTM 4 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then (1, a, Dir.left) else (0, some true, Dir.right)
    else if s.val = 1 then
      if a = none then (2, a, Dir.stay) else (1, a, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 3

/-- 第一阶段：从状态 0、左侧 l、右侧 w 出发，
    恰好 `|w|` 步把 w 全部改写成 `some true` 并右移，最终停在右端空白。 -/
theorem markPhase (l : List Sym) (w : List Bool) :
    markInput.run w.length
      { state := (0 : Fin 4), tape := { left := l, right := w.map some } } =
    { state := (0 : Fin 4),
      tape := { left := (w.map (fun _ => some true)).reverse ++ l, right := [] } } := by
  induction w generalizing l with
  | nil => rfl
  | cons b bs ih =>
      -- 第一步：读到 some b，写 some true 并右移
      have hhalt : markInput.halted
          { state := (0 : Fin 4),
            tape := { left := l, right := (b :: bs).map some } } = false := by
        simp [DTM.halted, markInput]
      have hstep : markInput.stepConfig
          { state := (0 : Fin 4),
            tape := { left := l, right := (b :: bs).map some } }
          = { state := (0 : Fin 4),
              tape := { left := some true :: l, right := bs.map some } } := by
        simp [DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [show (b :: bs).length = bs.length + 1 by simp, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      rw [ih (some true :: l)]
      simp [List.reverse_cons, List.append_assoc]

/-- 第二阶段（通用版）：状态 1、左侧 xs 全非空白、当前格 a 非空白，
    向左弹出全部 xs，`|xs|+2` 步后到达左端人工空白并接受。 -/
theorem rewindFrom_gen (xs : List Sym) (a : Sym) (r : List Sym)
    (ha : a ≠ none) (hne : ∀ x ∈ xs, x ≠ none) :
    markInput.run (xs.length + 2)
      { state := (1 : Fin 4), tape := { left := xs, right := a :: r } } =
    { state := (2 : Fin 4),
      tape := { left := [], right := none :: (xs.reverse ++ (a :: r)) } } := by
  induction xs generalizing a r with
  | nil =>
      -- 第一步：当前格非空白，左移一格到达人工空白
      have hhalt : markInput.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := a :: r } } = false := by
        simp [DTM.halted, markInput]
      have hstep : markInput.stepConfig
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := a :: r } }
          = { state := (1 : Fin 4), tape := { left := [], right := none :: (a :: r) } } := by
        simp [DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show ([].length + 2) = 0 + 1 + 1 by rfl, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      -- 第二步：读到空白，接受
      have hhalt2 : markInput.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := none :: (a :: r) } } = false := by
        simp [DTM.halted, markInput]
      rw [show (1 : Nat) = 0 + 1 by rfl, DTM.run]
      simp only [hhalt2, Bool.false_eq_true, ite_false]
      simp [DTM.run, DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move]
  | cons x xs ih =>
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      -- 第一步：当前格 a 非空白，左移，把 x 弹到右侧
      have hhalt : markInput.halted
          { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } } = false := by
        simp [DTM.halted, markInput]
      have hstep : markInput.stepConfig
          { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } }
          = { state := (1 : Fin 4), tape := { left := xs, right := x :: a :: r } } := by
        simp [DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      rw [ih x (a :: r) hx hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- 第二阶段（左端版）：从第一阶段结束的「状态 0、右侧为空」出发，
    `|L|+2` 步后到达最左端人工空白并接受；L 为累积的记号列表。 -/
theorem rewindPhase (L : List Sym) (hne : ∀ x ∈ L, x ≠ none) :
    markInput.run (L.length + 2)
      { state := (0 : Fin 4), tape := { left := L, right := [] } } =
    { state := (2 : Fin 4), tape := { left := [], right := none :: (L.reverse ++ [none]) } } := by
  cases L with
  | nil =>
      -- 右侧为空：第一步读到空白，左移补出人工空白；第二步接受
      have hhalt : markInput.halted
          { state := (0 : Fin 4), tape := { left := ([] : List Sym), right := [] } } = false := by
        simp [DTM.halted, markInput]
      have hstep : markInput.stepConfig
          { state := (0 : Fin 4), tape := { left := ([] : List Sym), right := [] } }
          = { state := (1 : Fin 4), tape := { left := [], right := [none, none] } } := by
        simp [DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [show ([].length + 2) = 0 + 1 + 1 by rfl, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      have hhalt2 : markInput.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := [none, none] } } = false := by
        simp [DTM.halted, markInput]
      rw [show (1 : Nat) = 0 + 1 by rfl, DTM.run]
      simp only [hhalt2, Bool.false_eq_true, ite_false]
      simp [DTM.run, DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move]
  | cons x xs =>
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      -- 第一步：读到空白，左移，把 x 弹到右侧
      have hhalt : markInput.halted
          { state := (0 : Fin 4), tape := { left := x :: xs, right := [] } } = false := by
        simp [DTM.halted, markInput]
      have hstep : markInput.stepConfig
          { state := (0 : Fin 4), tape := { left := x :: xs, right := [] } }
          = { state := (1 : Fin 4), tape := { left := xs, right := x :: [none] } } := by
        simp [DTM.stepConfig, markInput, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      rw [rewindFrom_gen xs x [none] hx hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- 整机：`markInput` 在 `2|w|+2` 步内接受，终态纸带左侧为空，
    右侧为「一个空白 + 全部输入改写成 `some true`」。 -/
theorem markInput_run (w : List Bool) :
    markInput.run (2 * w.length + 2) (markInput.init w) =
    { state := markInput.accept,
      tape := { left := [], right := none :: (w.map (fun _ => some true) ++ [none]) } } := by
  have h1' : markInput.run w.length (markInput.init w) =
      { state := (0 : Fin 4),
        tape := { left := (w.map (fun _ => some true)).reverse ++ [], right := [] } } := by
    simpa [markInput, DTM.init, Tape.ofInput] using markPhase [] w
  have hne : ∀ x ∈ (w.map (fun _ => some true)).reverse, x ≠ none := by
    intro x hx
    rw [List.mem_reverse] at hx
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hx
    rw [← hb]
    simp
  have h2 := rewindPhase ((w.map (fun _ => some true)).reverse) hne
  have h2' : markInput.run
      (((w.map (fun _ => some true)).reverse).length + 2)
      { state := (0 : Fin 4),
        tape := { left := (w.map (fun _ => some true)).reverse ++ [], right := [] } } =
      { state := (2 : Fin 4),
        tape := { left := [],
                  right := none :: ((w.map (fun _ => some true)).reverse.reverse ++ [none]) } } := by
    simpa using h2
  rw [show 2 * w.length + 2 =
      w.length + (((w.map (fun _ => some true)).reverse).length + 2) by
    simp [List.length_reverse]; omega]
  rw [DTM.run_add, h1', h2']
  simp [markInput, List.reverse_reverse]

end DTM

end Pnp
