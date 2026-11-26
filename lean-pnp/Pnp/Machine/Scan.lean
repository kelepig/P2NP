/-
  文件：Pnp/Machine/Scan.lean
  主题：最基础的确定性图灵机组件——「扫到右端空白」。

  这台机器从读写头当前位置出发一路向右，遇到空白就停机进入接受状态。
  它是后续「测量输入长度」「复制纸带」等组件的积木：

    - `scanToEnd`：4 状态机器（start / 工作 / accept / reject）；
    - `scanToEnd_run_aux`：从任意非终止状态、任意左侧内容出发，
      `|w| + 1` 步后一定到达接受状态（w 为剩余输入）；
    - `scanToEnd_accepts`：从初始格局出发的特例。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 4 状态扫描机：读到空白转入接受，否则保持工作状态右移。 -/
def scanToEnd : DTM 4 where
  step := fun _ a =>
    if a = none then (2, a, Dir.stay) else (1, a, Dir.right)
  start := 0
  accept := 2
  reject := 3

/-- 从任意非终止状态 s、任意左侧内容 l 出发，扫过剩余输入 w 后接受。
    起始时读写头指向 w 的第一个符号（右侧列表为 `w.map some`）。 -/
theorem scanToEnd_run_aux (w : List Bool) (l : List Sym) (s : Fin 4)
    (h2 : s ≠ 2) (h3 : s ≠ 3) :
    (scanToEnd.run (w.length + 1)
      { state := s, tape := { left := l, right := w.map some } }).state = 2 := by
  induction w generalizing l s with
  | nil =>
      -- 一步：读到空白转入接受状态
      have hhalt : scanToEnd.halted
          { state := s, tape := { left := l, right := ([] : List Bool).map some } } = false := by
        simp [DTM.halted, scanToEnd, h2, h3]
      rw [show ([].length + 1) = 0 + 1 by rfl, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false]
      simp [DTM.run, DTM.stepConfig, scanToEnd, Tape.read, Tape.write, Tape.move]
  | cons b bs ih =>
      -- 第一步读到 some b，右移一格，状态变为工作状态 1
      have hhalt : scanToEnd.halted
          { state := s, tape := { left := l, right := (b :: bs).map some } } = false := by
        simp [DTM.halted, scanToEnd, h2, h3]
      have hstep : scanToEnd.stepConfig
          { state := s, tape := { left := l, right := (b :: bs).map some } }
          = { state := 1, tape := { left := some b :: l, right := bs.map some } } := by
        simp [DTM.stepConfig, scanToEnd, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      exact ih (some b :: l) 1 (by decide) (by decide)

/-- 从初始格局出发，扫描全部输入后接受。 -/
theorem scanToEnd_accepts (w : List Bool) :
    (scanToEnd.run (w.length + 1) (scanToEnd.init w)).state = scanToEnd.accept := by
  have h := scanToEnd_run_aux w [] 0 (by decide) (by decide)
  simpa [DTM.init, Tape.ofInput, scanToEnd] using h

/-- 4 状态回扫机：读到空白转入接受，否则保持工作状态左移。
    要求回扫路径上没有空白（数据区用非空白编码），否则会提前停下。 -/
def scanLeft : DTM 4 where
  step := fun _ a =>
    if a = none then (2, a, Dir.stay) else (1, a, Dir.left)
  start := 0
  accept := 2
  reject := 3

/-- 从任意非终止状态出发，左侧数据全非空白、当前格非空白，
    则 `|l| + 2` 步后到达接受状态（先回扫，再多走一步进入人工空白）。 -/
theorem scanLeft_run_aux (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym) (s : Fin 4), (∀ x ∈ l, x ≠ none) →
      s ≠ 2 → s ≠ 3 →
      (scanLeft.run (l.length + 2)
        { state := s, tape := { left := l, right := a :: r } }).state = 2
  | [], s, _, h2, h3 => by
      have hhalt : scanLeft.halted
          { state := s, tape := { left := ([] : List Sym), right := a :: r } } = false := by
        simp [DTM.halted, scanLeft, h2, h3]
      have hstep : scanLeft.stepConfig
          { state := s, tape := { left := ([] : List Sym), right := a :: r } }
          = { state := 1, tape := { left := [], right := none :: a :: r } } := by
        simp [DTM.stepConfig, scanLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show ([].length + 2) = (0 + 1) + 1 by rfl, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      simp [DTM.run, DTM.halted, DTM.stepConfig, scanLeft, Tape.read, Tape.write, Tape.move]
  | x :: xs, s, hne, h2, h3 => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : scanLeft.halted
          { state := s, tape := { left := x :: xs, right := a :: r } } = false := by
        simp [DTM.halted, scanLeft, h2, h3]
      have hstep : scanLeft.stepConfig
          { state := s, tape := { left := x :: xs, right := a :: r } }
          = { state := 1, tape := { left := xs, right := x :: a :: r } } := by
        simp [DTM.stepConfig, scanLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp, DTM.run]
      simp only [hhalt, Bool.false_eq_true, ite_false, hstep]
      exact scanLeft_run_aux x (a :: r) hx xs 1 hxs (by decide) (by decide)

/-- 回扫的整纸带版本：左侧数据全非空白、当前格非空白时，
    `|l| + 2` 步后到达接受状态，且纸带被精确描述为
    `left = []`、`right = none :: (l.reverse ++ a :: r)`。 -/
theorem scanLeft_run_all (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym) (s : Fin 4), (∀ x ∈ l, x ≠ none) → s ≠ 2 → s ≠ 3 →
      scanLeft.run (l.length + 2)
        { state := s, tape := { left := l, right := a :: r } }
      = { state := 2, tape := { left := [], right := none :: (l.reverse ++ a :: r) } }
  | [], s, _, h2, h3 => by
      have hhalt : scanLeft.halted
          { state := s, tape := { left := ([] : List Sym), right := a :: r } } = false := by
        simp [DTM.halted, scanLeft, h2, h3]
      have hstep : scanLeft.stepConfig
          { state := s, tape := { left := ([] : List Sym), right := a :: r } }
          = { state := 1, tape := { left := ([] : List Sym), right := none :: a :: r } } := by
        simp [DTM.stepConfig, scanLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : scanLeft.halted
          { state := (1 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: a :: r } } = false := by
        simp [DTM.halted, scanLeft]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2]
      simp [DTM.run, DTM.stepConfig, scanLeft, Tape.read, Tape.write, Tape.move]
  | x :: xs, s, hne, h2, h3 => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : scanLeft.halted
          { state := s, tape := { left := x :: xs, right := a :: r } } = false := by
        simp [DTM.halted, scanLeft, h2, h3]
      have hstep : scanLeft.stepConfig
          { state := s, tape := { left := x :: xs, right := a :: r } }
          = { state := 1, tape := { left := xs, right := x :: a :: r } } := by
        simp [DTM.stepConfig, scanLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ _ _ hhalt, hstep,
        scanLeft_run_all x (a :: r) hx xs 1 hxs (by decide) (by decide)]
      simp [List.reverse_cons, List.append_assoc]

/-- 回到块首机：数据区全部非空白时向左回扫，遇到左侧空白后右移一格，
    读写头正好停在块的最左格（最低位）。 -/
def rewindToHead : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then (2, a, Dir.right) else (0, a, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 1

/-- 整纸带运行引理：从块内任意位置出发，`|l| + 2` 步后头停在块首，
    左侧只剩一个空白（`left = [none]`），右侧是原左半区的逆序接上当前格之后的内容。 -/
theorem rewindToHead_run (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      rewindToHead.run (l.length + 2)
        { state := 0, tape := { left := l, right := a :: r } }
      = { state := 2, tape := { left := [none], right := l.reverse ++ a :: r } }
  | [], _ => by
      have hhalt : rewindToHead.halted
          { state := (0 : Fin 3), tape := { left := ([] : List Sym), right := a :: r } } = false := by
        simp [DTM.halted, rewindToHead]
      have hstep : rewindToHead.stepConfig
          { state := (0 : Fin 3), tape := { left := ([] : List Sym), right := a :: r } }
          = { state := (0 : Fin 3),
              tape := { left := ([] : List Sym), right := none :: a :: r } } := by
        simp [DTM.stepConfig, rewindToHead, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : rewindToHead.halted
          { state := (0 : Fin 3),
            tape := { left := ([] : List Sym), right := none :: a :: r } } = false := by
        simp [DTM.halted, rewindToHead]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2]
      simp [DTM.run, DTM.stepConfig, rewindToHead, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | x :: xs, hne => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : rewindToHead.halted
          { state := (0 : Fin 3), tape := { left := x :: xs, right := a :: r } } = false := by
        simp [DTM.halted, rewindToHead]
      have hstep : rewindToHead.stepConfig
          { state := (0 : Fin 3), tape := { left := x :: xs, right := a :: r } }
          = { state := (0 : Fin 3), tape := { left := xs, right := x :: a :: r } } := by
        simp [DTM.stepConfig, rewindToHead, Tape.read, Tape.write, Tape.move, Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ _ _ hhalt, hstep,
        rewindToHead_run x (a :: r) hx xs hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- 跨入数据区再回到块首：第一步无条件左移（从块右侧空白跨入块内），
    之后一路左扫到边界，再右移一格停在块首。 -/
def rewindIntoBlock : DTM 4 where
  step := fun s a =>
    if s.val = 0 then (1, a, Dir.left)
    else if s.val = 1 then
      if a = none then (2, a, Dir.right) else (1, a, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 3

/-- 扫描阶段：从块内任意非空白格出发，`|l|+2` 步后回到块首（左侧只剩一个空白）。 -/
theorem rewindIntoBlock_scan (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      rewindIntoBlock.run (l.length + 2)
        { state := (1 : Fin 4), tape := { left := l, right := a :: r } } =
    { state := (2 : Fin 4), tape := { left := [none], right := l.reverse ++ a :: r } }
  | [], _ => by
      have hhalt : rewindIntoBlock.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := a :: r } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      have hstep : rewindIntoBlock.stepConfig
          { state := (1 : Fin 4), tape := { left := ([] : List Sym), right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := ([] : List Sym), right := none :: a :: r } } := by
        simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : rewindIntoBlock.halted
          { state := (1 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: a :: r } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2]
      simp [DTM.run, DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  | x :: xs, hne => by
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : rewindIntoBlock.halted
          { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      have hstep : rewindIntoBlock.stepConfig
          { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } }
          = { state := (1 : Fin 4), tape := { left := xs, right := x :: a :: r } } := by
        simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ _ _ hhalt, hstep,
        rewindIntoBlock_scan x (a :: r) hx xs hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- 整机：从「加一结束」的格局（头在最低位右边、左侧块为 `1` 后跟 `k` 个 0，
    右侧非空）出发，`k+3` 步后头回到块首。 -/
theorem rewindIntoBlock_run (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    rewindIntoBlock.run (k + 3)
      { state := (0 : Fin 4),
        tape := { left := some true :: List.replicate k (some false), right := rest } } =
    { state := (2 : Fin 4),
      tape := { left := [none],
                right := List.replicate k (some false) ++ some true :: rest } } := by
  have hhalt : rewindIntoBlock.halted
      { state := (0 : Fin 4),
        tape := { left := some true :: List.replicate k (some false), right := rest } } = false := by
    simp [DTM.halted, rewindIntoBlock]
  have hstep : rewindIntoBlock.stepConfig
      { state := (0 : Fin 4),
        tape := { left := some true :: List.replicate k (some false), right := rest } }
      = { state := (1 : Fin 4),
          tape := { left := List.replicate k (some false),
                    right := some true :: rest } } := by
    rcases rest with _ | ⟨x, xs⟩
    · exact absurd rfl hrest
    · simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [show k + 3 = ((List.replicate k (some false)).length + 2) + 1 by simp,
    DTM.run_succ_of_not_halted _ ((List.replicate k (some false)).length + 2) _ hhalt, hstep,
    rewindIntoBlock_scan (some true) rest (by decide) (List.replicate k (some false))
      (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)]
  simp [List.reverse_replicate]

/-- 扫描阶段的状态不变式：`|l|+2` 步以内始终停在状态 1（因此不会提前停机）。 -/
theorem rewindIntoBlock_scan_state (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      ∀ m : Nat, m < l.length + 2 →
        (rewindIntoBlock.run m
          { state := (1 : Fin 4), tape := { left := l, right := a :: r } }).state = 1
  | [], _, m, hm => by
      simp only [List.length_nil] at hm
      have hm2 : m = 0 ∨ m = 1 := by omega
      rcases hm2 with rfl | rfl
      · rfl
      · have hhalt : rewindIntoBlock.halted
            { state := (1 : Fin 4),
              tape := { left := ([] : List Sym), right := a :: r } } = false := by
          simp [DTM.halted, rewindIntoBlock]
        rw [show 1 = 0 + 1 by rfl, DTM.run_succ_of_not_halted _ 0 _ hhalt]
        simp [DTM.run, DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
  | x :: xs, hne, m, hm => by
      rcases m with _ | m
      · rfl
      · have hx : x ≠ none := hne x List.mem_cons_self
        have hxs : ∀ y ∈ xs, y ≠ none :=
          fun y hy => hne y (List.mem_cons_of_mem _ hy)
        have hhalt : rewindIntoBlock.halted
            { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } } = false := by
          simp [DTM.halted, rewindIntoBlock]
        have hstep : rewindIntoBlock.stepConfig
            { state := (1 : Fin 4), tape := { left := x :: xs, right := a :: r } }
            = { state := (1 : Fin 4), tape := { left := xs, right := x :: a :: r } } := by
          simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, ha]
        rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
        exact rewindIntoBlock_scan_state x (a :: r) hx xs hxs m (by
          simp only [List.length_cons] at hm
          omega)

/-- 整机的非停机前缀：从加一结束格局出发，`k+3` 步以内都不会停机。 -/
theorem rewindIntoBlock_run_nonhalt (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    ∀ m : Nat, m < k + 3 →
      rewindIntoBlock.halted
        (rewindIntoBlock.run m
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := rest } }) = false
  | 0, _ => by simp [DTM.run, DTM.halted, rewindIntoBlock]
  | m + 1, hm => by
      have hhalt : rewindIntoBlock.halted
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := rest } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      have hstep : rewindIntoBlock.stepConfig
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := rest } }
          = { state := (1 : Fin 4),
              tape := { left := List.replicate k (some false),
                        right := some true :: rest } } := by
        rcases rest with _ | ⟨x, xs⟩
        · exact absurd rfl hrest
        · simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
      have hstate := rewindIntoBlock_scan_state (some true) rest (by decide)
        (List.replicate k (some false))
        (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)
        m (by simp only [List.length_replicate]; omega)
      rw [DTM.halted, hstate]
      decide

/-- 扫描阶段（左侧多一个空白）：`l` 全非空白、其左侧再加一个空白，
    `|l|+2` 步后接受，头停在块首（左侧仍只有一个空白）。 -/
theorem rewindIntoBlock_scan_blank (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      rewindIntoBlock.run (l.length + 2)
        { state := (1 : Fin 4),
          tape := { left := l ++ [none], right := a :: r } } =
      { state := (2 : Fin 4),
        tape := { left := [none], right := l.reverse ++ a :: r } }
  | [], _ => by
      -- 左侧只有一个空白：两步读空白后接受
      have hhalt : rewindIntoBlock.halted
          { state := (1 : Fin 4), tape := { left := ([] : List Sym) ++ [none], right := a :: r } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      have hstep : rewindIntoBlock.stepConfig
          { state := (1 : Fin 4), tape := { left := ([] : List Sym) ++ [none], right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := ([] : List Sym), right := none :: a :: r } } := by
        simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
      rw [show ([].length + 2) = 1 + 1 by rfl,
        DTM.run_succ_of_not_halted _ 1 _ hhalt, hstep]
      have hhalt2 : rewindIntoBlock.halted
          { state := (1 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: a :: r } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      rw [DTM.run_succ_of_not_halted _ 0 _ hhalt2]
      simp [DTM.run, DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  | x :: xs, hne => by
      simp only [List.cons_append]
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : rewindIntoBlock.halted
          { state := (1 : Fin 4),
            tape := { left := x :: (xs ++ [none]), right := a :: r } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      have hstep : rewindIntoBlock.stepConfig
          { state := (1 : Fin 4),
            tape := { left := x :: (xs ++ [none]), right := a :: r } }
          = { state := (1 : Fin 4),
              tape := { left := xs ++ [none], right := x :: a :: r } } := by
        simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 by simp,
        DTM.run_succ_of_not_halted _ _ _ hhalt, hstep,
        rewindIntoBlock_scan_blank x (a :: r) hx xs hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- 扫描阶段（左侧多一个空白）的状态不变式：`|l|+2` 步以内始终停在状态 1。 -/
theorem rewindIntoBlock_scan_blank_state (a : Sym) (r : List Sym) (ha : a ≠ none) :
    ∀ (l : List Sym), (∀ x ∈ l, x ≠ none) →
      ∀ m : Nat, m < l.length + 2 →
        (rewindIntoBlock.run m
          { state := (1 : Fin 4),
            tape := { left := l ++ [none], right := a :: r } }).state = 1
  | [], _, m, hm => by
      simp only [List.length_nil] at hm
      have hm2 : m = 0 ∨ m = 1 := by omega
      rcases hm2 with rfl | rfl
      · rfl
      · have hhalt : rewindIntoBlock.halted
            { state := (1 : Fin 4),
              tape := { left := ([] : List Sym) ++ [none], right := a :: r } } = false := by
          simp [DTM.halted, rewindIntoBlock]
        rw [show 1 = 0 + 1 by rfl, DTM.run_succ_of_not_halted _ 0 _ hhalt]
        simp [DTM.run, DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, ha]
  | x :: xs, hne, m, hm => by
      rcases m with _ | m
      · rfl
      · simp only [List.cons_append]
        have hx : x ≠ none := hne x List.mem_cons_self
        have hxs : ∀ y ∈ xs, y ≠ none :=
          fun y hy => hne y (List.mem_cons_of_mem _ hy)
        have hhalt : rewindIntoBlock.halted
            { state := (1 : Fin 4),
              tape := { left := x :: (xs ++ [none]), right := a :: r } } = false := by
          simp [DTM.halted, rewindIntoBlock]
        have hstep : rewindIntoBlock.stepConfig
            { state := (1 : Fin 4),
              tape := { left := x :: (xs ++ [none]), right := a :: r } }
            = { state := (1 : Fin 4),
                tape := { left := xs ++ [none], right := x :: a :: r } } := by
          simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, ha]
        rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
        exact rewindIntoBlock_scan_blank_state x (a :: r) hx xs hxs m (by
          simp only [List.length_cons] at hm
          omega)

/-- 循环第二轮起的回块首：左侧已有一个空白，`k+3` 步后回到块首（空白数不变）。 -/
theorem rewindIntoBlock_run1 (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    rewindIntoBlock.run (k + 3)
      { state := (0 : Fin 4),
        tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                  right := rest } } =
    { state := (2 : Fin 4),
      tape := { left := [none],
                right := List.replicate k (some false) ++ some true :: rest } } := by
  have hhalt : rewindIntoBlock.halted
      { state := (0 : Fin 4),
        tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                  right := rest } } = false := by
    simp [DTM.halted, rewindIntoBlock]
  have hstep : rewindIntoBlock.stepConfig
      { state := (0 : Fin 4),
        tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                  right := rest } }
      = { state := (1 : Fin 4),
          tape := { left := List.replicate k (some false) ++ [none], right := some true :: rest } } := by
    rcases rest with _ | ⟨x, xs⟩
    · exact absurd rfl hrest
    · simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  rw [show k + 3 = ((List.replicate k (some false)).length + 2) + 1 by simp,
    DTM.run_succ_of_not_halted _ ((List.replicate k (some false)).length + 2) _ hhalt, hstep,
    rewindIntoBlock_scan_blank (some true) rest (by decide) (List.replicate k (some false))
      (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)]
  simp [List.reverse_replicate]

/-- 循环第二轮起的回块首：`k+3` 步以内不停机。 -/
theorem rewindIntoBlock_run1_nonhalt (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    ∀ m : Nat, m < k + 3 →
      rewindIntoBlock.halted
        (rewindIntoBlock.run m
          { state := (0 : Fin 4),
            tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                      right := rest } }) = false := by
  intro m hm
  cases m with
  | zero => simp [DTM.run, DTM.halted, rewindIntoBlock]
  | succ m =>
      have hhalt : rewindIntoBlock.halted
          { state := (0 : Fin 4),
            tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                      right := rest } } = false := by
        simp [DTM.halted, rewindIntoBlock]
      have hstep : rewindIntoBlock.stepConfig
          { state := (0 : Fin 4),
            tape := { left := some true :: (List.replicate k (some false) ++ [none]),
                      right := rest } }
          = { state := (1 : Fin 4),
              tape := { left := List.replicate k (some false) ++ [none],
                        right := some true :: rest } } := by
        rcases rest with _ | ⟨x, xs⟩
        · exact absurd rfl hrest
        · simp [DTM.stepConfig, rewindIntoBlock, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt, hstep]
      -- 状态 1，左侧 `false^k ++ [none]`：仍处于扫描阶段
      have hstate : (rewindIntoBlock.run m
          { state := (1 : Fin 4),
            tape := { left := List.replicate k (some false) ++ [none],
                      right := some true :: rest } }).state = 1 :=
        rewindIntoBlock_scan_blank_state (some true) rest (by decide)
          (List.replicate k (some false))
          (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; decide)
          m (by simp only [List.length_replicate]; omega)
      rw [DTM.halted, hstate]
      decide

end DTM

end Pnp
