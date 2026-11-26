/-
  文件：Pnp/Machine/DblOnce.lean
  File: Pnp/Machine/DblOnce.lean

  主题：**单机版 unary 倍增**——把「倍增循环 + 恢复」合并成一台顺序组合机，
        使倍增可以由控制器逐轮驱动（不再需要三台机器的人工串接）。
  Topic: a single-machine unary doubling (loop + restore as one `seqComp` machine).

  设计（#196）：
    - `doubleStep` 在源格耗尽后继续右扫过整块 `some false`，读到空白即进入接受态 3，
      此时头在块**右侧**、块在左带上；
    - 新增恢复机 `restoreLeft`：从右端向左扫，把每格改写成 `some true`，
      遇空白接受并右移一格——终态恰为「头在块首、块左侧一个空白、块右侧带尾空白」；
    - `dblOnce := seqComp doubleStep restoreLeft` 只需一次 `seqComp`。
  Design: `doubleStep` already accepts (state 3) after scanning past the block; a new
  leftward restore machine `restoreLeft` finishes the round with the established shape.
-/

import Pnp.Machine.UnaryArith
import Pnp.Machine.SeqComp

namespace Pnp

namespace DTM

/-! ### 左向恢复机 -/

/-- 左向恢复机：状态 0 从空白起步；状态 1 向左扫并逐格写 `some true`；
    遇空白右移一格进入接受态 2。
    Leftward restore: state 0 starts on the blank, state 1 writes `some true` while
    walking left, and a blank ends the scan, with one right step into accept state 2. -/
def restoreLeft : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then (0, a, Dir.left) else (1, some true, Dir.left)
    else if s.val = 1 then
      if a = none then (2, a, Dir.right) else (1, some true, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 2

/-- **左向恢复（主体）**：状态 1、当前符号为非空白、左侧 `k` 个待改写的非空白格，
    左端是人工空白 + 远端内容 `L`。`k+2` 步后全部改写成 `some true` 并接受。
    The main leftward restore run: `k` unprocessed cells plus a far context `L`. -/
theorem restoreLeft_run1 (k : Nat) (L tail : List Sym) :
    restoreLeft.run (k + 2)
      { state := (1 : Fin 3),
        tape := { left := List.replicate k (some false) ++ ([none] ++ L),
                  right := some false :: tail } } =
    { state := (2 : Fin 3),
      tape := { left := [none] ++ L,
                right := List.replicate (k + 1) (some true) ++ tail } } := by
  induction k generalizing L tail with
  | zero =>
      -- 把 `replicate 0` 归约成 `[]`，与下面写好的转移引理对齐
      rw [show (List.replicate 0 (some false) : List Sym) = [] from rfl]
      have h0 : restoreLeft.halted
          { state := (1 : Fin 3),
            tape := { left := ([] : List Sym) ++ ([none] ++ L), right := some false :: tail } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep1 : restoreLeft.stepConfig
          { state := (1 : Fin 3),
            tape := { left := ([] : List Sym) ++ ([none] ++ L), right := some false :: tail } }
          = { state := (1 : Fin 3),
              tape := { left := L, right := none :: some true :: tail } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft]
      have h1 : restoreLeft.halted
          { state := (1 : Fin 3),
            tape := { left := L, right := none :: some true :: tail } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep2 : restoreLeft.stepConfig
          { state := (1 : Fin 3),
            tape := { left := L, right := none :: some true :: tail } }
          = { state := (2 : Fin 3),
              tape := { left := [none] ++ L, right := some true :: tail } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
      change restoreLeft.run ((0 + 1) + 1) _ = _
      rw [DTM.run_succ_of_not_halted restoreLeft (0 + 1) _ h0, hstep1,
          DTM.run_succ_of_not_halted restoreLeft 0 _ h1, hstep2]
      simp [DTM.run, List.replicate_succ']
  | succ k ih =>
      -- 把左带首格拆出来
      have hsh : List.replicate (k + 1) (some false) ++ ([none] ++ L) =
          some false :: (List.replicate k (some false) ++ ([none] ++ L)) := by
        rw [List.replicate_succ, List.cons_append]
      rw [hsh]
      have h0 : restoreLeft.halted
          { state := (1 : Fin 3),
            tape := { left := some false :: (List.replicate k (some false) ++ ([none] ++ L)),
                      right := some false :: tail } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep1 : restoreLeft.stepConfig
          { state := (1 : Fin 3),
            tape := { left := some false :: (List.replicate k (some false) ++ ([none] ++ L)),
                      right := some false :: tail } }
          = { state := (1 : Fin 3),
              tape := { left := List.replicate k (some false) ++ ([none] ++ L),
                        right := some false :: some true :: tail } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft]
      change restoreLeft.run ((k + 1) + 1 + 1) _ = _
      rw [DTM.run_succ_of_not_halted restoreLeft ((k + 1) + 1) _ h0, hstep1]
      change restoreLeft.run (k + 2) _ = _
      rw [ih L (some true :: tail)]
      simp [List.replicate_succ', List.append_assoc]

/-- **左向恢复（核心）**：状态 0、当前符号为非空白（首格已暴露）时的主体运行。
    The core run: state 0 with a non-blank current cell. -/
theorem restoreLeft_core (k : Nat) (L : List Sym) :
    restoreLeft.run (k + 2)
      { state := (0 : Fin 3),
        tape := { left := List.replicate k (some false) ++ ([none] ++ L),
                  right := some false :: [none] } } =
    { state := (2 : Fin 3),
      tape := { left := [none] ++ L,
                right := List.replicate (k + 1) (some true) ++ [none] } } := by
  cases k with
  | zero =>
      -- 左带没有待改写格：写一步、收尾一步
      rw [show (List.replicate 0 (some false) : List Sym) = [] from rfl]
      have h0 : restoreLeft.halted
          { state := (0 : Fin 3),
            tape := { left := ([] : List Sym) ++ ([none] ++ L), right := some false :: [none] } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep1 : restoreLeft.stepConfig
          { state := (0 : Fin 3),
            tape := { left := ([] : List Sym) ++ ([none] ++ L), right := some false :: [none] } }
          = { state := (1 : Fin 3),
              tape := { left := L, right := none :: some true :: [none] } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      have h1 : restoreLeft.halted
          { state := (1 : Fin 3),
            tape := { left := L, right := none :: some true :: [none] } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep2 : restoreLeft.stepConfig
          { state := (1 : Fin 3),
            tape := { left := L, right := none :: some true :: [none] } }
          = { state := (2 : Fin 3),
              tape := { left := [none] ++ L, right := some true :: [none] } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      change restoreLeft.run (0 + 1 + 1) _ = _
      rw [DTM.run_succ_of_not_halted restoreLeft (0 + 1) _ h0, hstep1,
          DTM.run_succ_of_not_halted restoreLeft 0 _ h1, hstep2]
      simp [DTM.run, List.replicate_succ]
  | succ k =>
      -- 展开左带首格，写下当前格后回到 `restoreLeft_run1`
      rw [show List.replicate (k + 1) (some false) ++ ([none] ++ L)
            = some false :: (List.replicate k (some false) ++ ([none] ++ L))
          from by rw [List.replicate_succ, List.cons_append]]
      have h0 : restoreLeft.halted
          { state := (0 : Fin 3),
            tape := { left := some false :: (List.replicate k (some false) ++ ([none] ++ L)),
                      right := some false :: [none] } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep : restoreLeft.stepConfig
          { state := (0 : Fin 3),
            tape := { left := some false :: (List.replicate k (some false) ++ ([none] ++ L)),
                      right := some false :: [none] } }
          = { state := (1 : Fin 3),
              tape := { left := List.replicate k (some false) ++ ([none] ++ L),
                        right := some false :: some true :: [none] } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [DTM.run_succ_of_not_halted restoreLeft (k + 1 + 1) _ h0, hstep]
      rw [restoreLeft_run1 k L (some true :: [none])]
      -- 三个重复段相加的对齐：`replicate k ++ [true] = replicate (k+1)`
      have hkey : ∀ j : Nat, List.replicate j (some true) ++ [some true, none]
          = some true :: (List.replicate j (some true) ++ [none]) := by
        intro j
        rw [show ([some true, none] : List Sym) = [some true] ++ [none] from rfl,
          ← List.append_assoc,
          show List.replicate j (some true) ++ [some true]
              = List.replicate (j + 1) (some true) from by simp [List.replicate_succ'],
          List.replicate_succ]
        simp [List.cons_append]
      rw [hkey (k + 1)]
      simp only [List.replicate_succ, List.cons_append]

/-- **左向恢复（入口）**：从块右侧的空白起步（`r` 为空或一个空白），
    `k ≥ 1` 个 `some false` 格全部改写成 `some true`。
    The entry form, starting on the blank at the block's right end. -/
theorem restoreLeft_run0 (k : Nat) (hk : 1 ≤ k) (L : List Sym) (r : List Sym)
    (hr : r = [] ∨ r = [none]) :
    restoreLeft.run (k + 2)
      { state := (0 : Fin 3),
        tape := { left := List.replicate k (some false) ++ ([none] ++ L), right := r } } =
    { state := (2 : Fin 3),
      tape := { left := [none] ++ L,
                right := List.replicate k (some true) ++ [none] } } := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- 首步：读到空白、左移一格（两种初始右侧都归一为 `[none]`）
  have h0 : restoreLeft.halted
      { state := (0 : Fin 3),
        tape := { left := List.replicate (k' + 1) (some false) ++ ([none] ++ L), right := r } } = false := by
    simp [DTM.halted, restoreLeft]
  have hstep : restoreLeft.stepConfig
      { state := (0 : Fin 3),
        tape := { left := List.replicate (k' + 1) (some false) ++ ([none] ++ L), right := r } }
      = { state := (0 : Fin 3),
          tape := { left := List.replicate k' (some false) ++ ([none] ++ L),
                    right := some false :: [none] } } := by
    rw [show List.replicate (k' + 1) (some false) ++ ([none] ++ L)
          = some false :: (List.replicate k' (some false) ++ ([none] ++ L))
        from by rw [List.replicate_succ, List.cons_append]]
    rcases hr with rfl | rfl
    · simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
    · simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  change restoreLeft.run ((k' + 1) + 1 + 1) _ = _
  rw [DTM.run_succ_of_not_halted restoreLeft ((k' + 1) + 1) _ h0, hstep]
  change restoreLeft.run (k' + 2) _ = _
  rw [restoreLeft_core k' L]

/-- **左向恢复（中段）**：状态 1、左带紧邻 `k` 个待改写格，走 `k+1` 步后
    仍停在状态 1（尚未读到人工空白，因而不接受），左侧内容变为 `L`。
    The mid-walk of the leftward restore (state 1, stops before the artificial blank). -/
theorem restoreLeft_walk1 (k : Nat) (L : List Sym) (tail : List Sym) :
    restoreLeft.run (k + 1)
      { state := (1 : Fin 3),
        tape := { left := List.replicate k (some false) ++ ([none] ++ L),
                  right := some false :: tail } } =
    { state := (1 : Fin 3),
      tape := { left := L, right := none :: List.replicate (k + 1) (some true) ++ tail } } := by
  induction k generalizing L tail with
  | zero =>
      -- 左带没有待改写格：一步写完、左移，停在人工空白上
      rw [show (List.replicate 0 (some false) : List Sym) = [] from rfl]
      have h0 : restoreLeft.halted
          { state := (1 : Fin 3),
            tape := { left := ([] : List Sym) ++ ([none] ++ L), right := some false :: tail } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep : restoreLeft.stepConfig
          { state := (1 : Fin 3),
            tape := { left := ([] : List Sym) ++ ([none] ++ L), right := some false :: tail } }
          = { state := (1 : Fin 3),
              tape := { left := L, right := none :: some true :: tail } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      change restoreLeft.run (0 + 1) _ = _
      rw [DTM.run_succ_of_not_halted restoreLeft 0 _ h0, hstep]
      simp [DTM.run, List.replicate_succ]
  | succ k ih =>
      -- 拆出左带首格，走一步后回到归纳假设
      rw [show List.replicate (k + 1) (some false) ++ ([none] ++ L)
            = some false :: (List.replicate k (some false) ++ ([none] ++ L)) from by
        rw [List.replicate_succ, List.cons_append]]
      have h0 : restoreLeft.halted
          { state := (1 : Fin 3),
            tape := { left := some false :: (List.replicate k (some false) ++ ([none] ++ L)),
                      right := some false :: tail } } = false := by
        simp [DTM.halted, restoreLeft]
      have hstep : restoreLeft.stepConfig
          { state := (1 : Fin 3),
            tape := { left := some false :: (List.replicate k (some false) ++ ([none] ++ L)),
                      right := some false :: tail } }
          = { state := (1 : Fin 3),
              tape := { left := List.replicate k (some false) ++ ([none] ++ L),
                        right := some false :: some true :: tail } } := by
        simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      change restoreLeft.run ((k + 1) + 1) _ = _
      rw [DTM.run_succ_of_not_halted restoreLeft (k + 1) _ h0, hstep]
      change restoreLeft.run (k + 1) _ = _
      rw [ih L (some true :: tail)]
      simp [List.replicate_succ', List.append_assoc]

/-- **左向恢复（入口中段）**：从块右侧的空白起步，走 `k+1` 步后停在状态 1
    （`k ≥ 1` 个格已改写），左侧内容为 `L`；再走一步即接受。
    The entry walk right before the accepting step. -/
theorem restoreLeft_pre (k : Nat) (hk : 1 ≤ k) (L : List Sym) :
    restoreLeft.run (k + 1)
      { state := (0 : Fin 3),
        tape := { left := List.replicate k (some false) ++ ([none] ++ L), right := [none] } } =
    { state := (1 : Fin 3),
      tape := { left := L, right := none :: List.replicate k (some true) ++ [none] } } := by
  cases k with
  | zero => omega
  | succ j =>
      cases j with
      | zero =>
          -- `k = 1`：两步（空转一格 + 改写唯一的格）
          rw [show (List.replicate 1 (some false) : List Sym) = [some false] from rfl,
            show ([some false] : List Sym) ++ ([none] ++ L) = some false :: ([none] ++ L) from rfl,
            show (List.replicate 1 (some true) : List Sym) = [some true] from rfl]
          have h0 : restoreLeft.halted
              { state := (0 : Fin 3),
                tape := { left := some false :: ([none] ++ L), right := [none] } } = false := by
            simp [DTM.halted, restoreLeft]
          have hstep1 : restoreLeft.stepConfig
              { state := (0 : Fin 3),
                tape := { left := some false :: ([none] ++ L), right := [none] } }
              = { state := (0 : Fin 3),
                  tape := { left := [none] ++ L, right := some false :: [none] } } := by
            simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
          have h1 : restoreLeft.halted
              { state := (0 : Fin 3),
                tape := { left := [none] ++ L, right := some false :: [none] } } = false := by
            simp [DTM.halted, restoreLeft]
          have hstep2 : restoreLeft.stepConfig
              { state := (0 : Fin 3),
                tape := { left := [none] ++ L, right := some false :: [none] } }
              = { state := (1 : Fin 3),
                  tape := { left := L, right := none :: some true :: [none] } } := by
            simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
          change restoreLeft.run (0 + 1 + 1) _ = _
          rw [DTM.run_succ_of_not_halted restoreLeft (0 + 1) _ h0, hstep1,
            DTM.run_succ_of_not_halted restoreLeft 0 _ h1, hstep2]
          simp [DTM.run]
      | succ j =>
          -- `k = j + 2`：两步后进入状态 1，再交给 `restoreLeft_walk1`
          rw [show List.replicate (j + 1 + 1) (some false) ++ ([none] ++ L)
                = some false :: (List.replicate (j + 1) (some false) ++ ([none] ++ L)) from by
              rw [List.replicate_succ, List.cons_append]]
          have h0 : restoreLeft.halted
              { state := (0 : Fin 3),
                tape := { left := some false :: (List.replicate (j + 1) (some false) ++ ([none] ++ L)),
                          right := [none] } } = false := by
            simp [DTM.halted, restoreLeft]
          have hstep1 : restoreLeft.stepConfig
              { state := (0 : Fin 3),
                tape := { left := some false :: (List.replicate (j + 1) (some false) ++ ([none] ++ L)),
                          right := [none] } }
              = { state := (0 : Fin 3),
                  tape := { left := List.replicate (j + 1) (some false) ++ ([none] ++ L),
                            right := some false :: [none] } } := by
            simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
          have h1 : restoreLeft.halted
              { state := (0 : Fin 3),
                tape := { left := List.replicate (j + 1) (some false) ++ ([none] ++ L),
                          right := some false :: [none] } } = false := by
            simp [DTM.halted, restoreLeft]
          have hstep2 : restoreLeft.stepConfig
              { state := (0 : Fin 3),
                tape := { left := List.replicate (j + 1) (some false) ++ ([none] ++ L),
                          right := some false :: [none] } }
              = { state := (1 : Fin 3),
                  tape := { left := List.replicate j (some false) ++ ([none] ++ L),
                            right := some false :: some true :: [none] } } := by
            rw [show List.replicate (j + 1) (some false) ++ ([none] ++ L)
                  = some false :: (List.replicate j (some false) ++ ([none] ++ L)) from by
                rw [List.replicate_succ, List.cons_append]]
            simp [DTM.stepConfig, restoreLeft, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
          change restoreLeft.run ((j + 1 + 1) + 1) _ = _
          rw [DTM.run_succ_of_not_halted restoreLeft ((j + 1) + 1) _ h0, hstep1,
            DTM.run_succ_of_not_halted restoreLeft (j + 1) _ h1, hstep2]
          change restoreLeft.run (j + 1) _ = _
          rw [restoreLeft_walk1 j L (some true :: [none])]
          simp [List.replicate_succ']

/-! ### 循环终止后的右扫段 -/

/-- **右扫段**：`doubleStep` 在源格耗尽后继续右扫整块 `some false`（`m + m` 格），
    读到空白进入接受态 3；头停在块右侧（右带只剩一个显式空白）。直接引用
    `double_seek_end`（`e = []`）。
    The post-loop scan: `doubleStep` skips the whole `some false` block and accepts.
    This is `double_seek_end` with an empty right end. -/
theorem double_scan_past (m : Nat) (L : List Sym) :
    doubleStep.run (m + m + 1)
      { state := (0 : Fin 4),
        tape := { left := [none] ++ L, right := List.replicate (m + m) (some false) } } =
    { state := (3 : Fin 4),
      tape := { left := List.replicate (m + m) (some false) ++ ([none] ++ L),
                right := [none] } } := by
  simpa only [List.append_nil] using double_seek_end ([none] ++ L) (m + m) [] (Or.inl rfl)

/-- **右扫整块（不含收尾一步）**：状态 0 右扫 `m` 个 `some false` 格，读到空白时
    仍停在状态 0（尚未执行「读空白即接受」的那一步）。末端 `e` 为空表或单个空白。
    Scanning the whole `some false` block in state 0, stopping just before the blank. -/
theorem double_scan_block (m : Nat) (L : List Sym) (e : List Sym)
    (_he : e = [] ∨ e = [none]) :
    doubleStep.run m
      { state := (0 : Fin 4),
        tape := { left := L, right := List.replicate m (some false) ++ e } } =
    { state := (0 : Fin 4),
      tape := { left := List.replicate m (some false) ++ L, right := e } } := by
  induction m generalizing L with
  | zero =>
      simp [DTM.run]
  | succ m ih =>
      -- 首格是 `some false`：原样写回、右移一格
      rw [show List.replicate (m + 1) (some false) ++ e
            = some false :: (List.replicate m (some false) ++ e) from by
        rw [List.replicate_succ, List.cons_append]]
      have h0 : doubleStep.halted
          { state := (0 : Fin 4),
            tape := { left := L, right := some false :: (List.replicate m (some false) ++ e) } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L, right := some false :: (List.replicate m (some false) ++ e) } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L, right := List.replicate m (some false) ++ e } } := by
        simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [DTM.run_succ_of_not_halted doubleStep m _ h0, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-! ### 单机倍增：`doubleStep` + `restoreLeft` -/

/-- 单机版倍增：先跑 `doubleStep`（倍增循环 + 右扫 + 接受），
    再由 `seqComp` 原地转入左向恢复机 `restoreLeft`。
    Single-machine doubling: the loop machine, then the leftward restore. -/
def dblOnce : DTM (4 + 3) := seqComp doubleStep restoreLeft

-- 起止状态的化简引理（供组合运行的 `simp` 使用）
@[simp] theorem restoreLeft_start : restoreLeft.start = (0 : Fin 3) := rfl
@[simp] theorem restoreLeft_accept : restoreLeft.accept = (2 : Fin 3) := rfl
@[simp] theorem dblOnce_start : dblOnce.start = (0 : Fin (4 + 3)) := rfl

/-- 单机倍增「除收尾步外」的步数：倍增循环 + 右扫整块 + 接受步 + 切换步 + 左向恢复中段。
    Step count of `dblOnce` without the final accepting step. -/
def dblOncePreSteps (m : Nat) : Nat :=
  doubleLoopSteps m 0 + (m + m) + 1 + 1 + (m + m + 1)

/-- 单机倍增的步数：`dblOncePreSteps` 再走一步（恢复收尾、进入接受态）。
    Step count of `dblOnce` (the pre-part plus the final accepting step). -/
def dblOnceSteps (m : Nat) : Nat := dblOncePreSteps m + 1

/-- **单机倍增（收尾步之前）**：`dblOnce` 跑完倍增循环、右扫、切换与恢复中段后，
    停在状态 `natAdd 4 1`（左向恢复的走位态，尚未接受），纸带已是 `unary (2m)` 但
    头还没回到块首。
    `dblOnce` up to (but excluding) the final accepting step. -/
theorem dblOnce_run_pre (m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    dblOnce.run (dblOncePreSteps m)
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨Fin.natAdd 4 (1 : Fin 3),
      Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ := by
  -- 起点纸带 / 各阶段纸带
  have h_loop := unary_double_trailing_ctx m hm L
  -- ① 倍增循环段
  have hA1 : dblOnce.run (doubleLoopSteps m 0)
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨Fin.castAdd 3 (0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩ := by
    have hnh : ∀ k, k < doubleLoopSteps m 0 →
        doubleStep.halted
          (doubleStep.run k ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unary m ++ [none])⟩) = false := by
      apply halted_false_before doubleStep (doubleLoopSteps m 0)
        ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unary m ++ [none])⟩
      · -- 终点状态 0 不是接受态
        intro h
        have hst : (doubleStep.run (doubleLoopSteps m 0)
            ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unary m ++ [none])⟩).state = (0 : Fin 4) := by
          simpa using congrArg (fun c => c.state) h_loop
        rw [hst] at h
        exact absurd h (by decide)
      · intro h
        have hst : (doubleStep.run (doubleLoopSteps m 0)
            ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unary m ++ [none])⟩).state = (0 : Fin 4) := by
          simpa using congrArg (fun c => c.state) h_loop
        rw [hst] at h
        exact absurd h (by decide)
    have hemb := seqComp_embed_left doubleStep restoreLeft (doubleLoopSteps m 0)
      ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unary m ++ [none])⟩ hnh
    rw [h_loop] at hemb
    exact hemb
  -- ② 右扫整块（状态仍为 0）
  have hscan : doubleStep.run (m + m)
      ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩ =
      ⟨(0 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ := by
    have hblock := double_scan_block (m + m) ([none] ++ L) [] (Or.inl rfl)
    rw [show unaryF m ++ unaryF m = List.replicate (m + m) (some false) from by
      simp [unaryF, List.replicate_append_replicate]]
    rw [show List.replicate (m + m) (some false) ++ ([] : List Sym)
          = List.replicate (m + m) (some false) from by simp] at hblock
    exact hblock
  have hA2 : dblOnce.run (m + m)
      ⟨Fin.castAdd 3 (0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩ =
      ⟨Fin.castAdd 3 (0 : Fin 4),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ := by
    have hnh : ∀ k, k < m + m →
        doubleStep.halted
          (doubleStep.run k ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩) = false := by
      apply halted_false_before doubleStep (m + m)
        ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩
      · intro h
        have hst : (doubleStep.run (m + m)
            ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩).state = (0 : Fin 4) := by
          simpa using congrArg (fun c => c.state) hscan
        rw [hst] at h
        exact absurd h (by decide)
      · intro h
        have hst : (doubleStep.run (m + m)
            ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩).state = (0 : Fin 4) := by
          simpa using congrArg (fun c => c.state) hscan
        rw [hst] at h
        exact absurd h (by decide)
    have hemb := seqComp_embed_left doubleStep restoreLeft (m + m)
      ⟨(0 : Fin 4), Tape.mk ([none] ++ L) (unaryF m ++ unaryF m)⟩ hnh
    rw [hscan] at hemb
    exact hemb
  -- ③ 读空白、进入接受态（`doubleStep` 露出接受态 3）
  have hA3 : dblOnce.run 1
      ⟨Fin.castAdd 3 (0 : Fin 4),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ =
      ⟨Fin.castAdd 3 (3 : Fin 4),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ := by
    have hstep : doubleStep.run 1
        ⟨(0 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ =
        ⟨(3 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ := by
      have h0 : doubleStep.halted
          ⟨(0 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ = false := by
        simp [DTM.halted, doubleStep]
      rw [DTM.run_succ_of_not_halted doubleStep 0 _ h0]
      simp [DTM.run, DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move]
    have hnh : ∀ k, k < 1 →
        doubleStep.halted (doubleStep.run k
          ⟨(0 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩) = false := by
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      simpa [DTM.run] using (show doubleStep.halted
        ⟨(0 : Fin 4),
          Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ = false from by
        simp [DTM.halted, doubleStep])
    have hemb := seqComp_embed_left doubleStep restoreLeft 1
      ⟨(0 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ hnh
    rw [hstep] at hemb
    exact hemb
  -- ④ 切换步：`doubleStep` 接受后原地转入 `restoreLeft`
  have hSW : dblOnce.run 1
      ⟨Fin.castAdd 3 (3 : Fin 4),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ =
      ⟨Fin.natAdd 4 (0 : Fin 3),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ := by
    have hsw := seqComp_switch doubleStep restoreLeft
      ⟨(3 : Fin 4), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ rfl
    -- 写回当前符号（空白）再原地不动 = 原纸带
    have ht : (((Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]).write
          (Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]).read).move
            Dir.stay)
        = Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none] := by
      rw [Tape.write_read _ (by simp), Tape.move]
    rw [ht] at hsw
    exact hsw
  -- ⑤ 左向恢复中段（状态 1，尚未接受）
  have hpre := restoreLeft_pre (m + m) (by omega) L
  have hB1 : dblOnce.run (m + m + 1)
      ⟨Fin.natAdd 4 (0 : Fin 3),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ =
      ⟨Fin.natAdd 4 (1 : Fin 3),
        Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ := by
    have hnh : ∀ k, k < m + m + 1 →
        restoreLeft.halted (restoreLeft.run k
          ⟨(0 : Fin 3), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩) = false := by
      apply halted_false_before restoreLeft (m + m + 1)
        ⟨(0 : Fin 3), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩
      · intro h
        have hst : (restoreLeft.run (m + m + 1)
            ⟨(0 : Fin 3),
              Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩).state = (1 : Fin 3) := by
          simpa using congrArg (fun c => c.state) hpre
        rw [hst] at h
        exact absurd h (by decide)
      · intro h
        have hst : (restoreLeft.run (m + m + 1)
            ⟨(0 : Fin 3),
              Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩).state = (1 : Fin 3) := by
          simpa using congrArg (fun c => c.state) hpre
        rw [hst] at h
        exact absurd h (by decide)
    have hemb := seqComp_embed_right doubleStep restoreLeft (m + m + 1)
      ⟨(0 : Fin 3), Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ hnh
    rw [hpre] at hemb
    exact hemb
  -- 拼装：按左结合的段序逐段剥离
  have h12 : dblOnce.run (doubleLoopSteps m 0 + (m + m))
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨Fin.castAdd 3 (0 : Fin 4),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) []⟩ := by
    rw [DTM.run_add dblOnce (doubleLoopSteps m 0) (m + m), hA1, hA2]
  have h123 : dblOnce.run (doubleLoopSteps m 0 + (m + m) + 1)
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨Fin.castAdd 3 (3 : Fin 4),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ := by
    rw [DTM.run_add dblOnce (doubleLoopSteps m 0 + (m + m)) 1, h12, hA3]
  have h1234 : dblOnce.run (doubleLoopSteps m 0 + (m + m) + 1 + 1)
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨Fin.natAdd 4 (0 : Fin 3),
        Tape.mk (List.replicate (m + m) (some false) ++ ([none] ++ L)) [none]⟩ := by
    rw [DTM.run_add dblOnce (doubleLoopSteps m 0 + (m + m) + 1) 1, h123, hSW]
  have hall : dblOnce.run (doubleLoopSteps m 0 + (m + m) + 1 + 1 + (m + m + 1))
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨Fin.natAdd 4 (1 : Fin 3),
        Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ := by
    rw [DTM.run_add dblOnce (doubleLoopSteps m 0 + (m + m) + 1 + 1) (m + m + 1),
      h1234, hB1]
  rw [show dblOncePreSteps m
        = doubleLoopSteps m 0 + (m + m) + 1 + 1 + (m + m + 1) from rfl]
  exact hall


/-! ### 多轮倍增（轮间自动重启） -/

/-- 恢复中段终点（状态 `natAdd 4 1`）不是终止态。
    The mid-point configuration of `dblOnce` is not terminal. -/
theorem dblOnce_mid_halted (m : Nat) (L : List Sym) :
    dblOnce.halted
      ⟨Fin.natAdd 4 (1 : Fin 3),
        Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    have hv2 : dblOnce.accept.val = 4 + 2 := rfl
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    have hv2 : dblOnce.reject.val = 4 + 2 := rfl
    omega

/-- 单机倍增的收尾一步（读人工空白、右移进入接受态）。
    The final accepting step of `dblOnce`. -/
theorem dblOnce_last (m : Nat) (L : List Sym) :
    dblOnce.run 1
      ⟨Fin.natAdd 4 (1 : Fin 3),
        Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ =
      ⟨dblOnce.accept, Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ := by
  have hnh := dblOnce_mid_halted m L
  have hstep : dblOnce.stepConfig
      ⟨Fin.natAdd 4 (1 : Fin 3),
        Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ =
      ⟨dblOnce.accept, Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ := by
    show (seqComp doubleStep restoreLeft).stepConfig
      ⟨Fin.natAdd 4 (1 : Fin 3),
        Tape.mk L (none :: List.replicate (m + m) (some true) ++ [none])⟩ = _
    rw [DTM.stepConfig, seqComp_step_natAdd]
    rfl
  rw [DTM.run_succ_of_not_halted dblOnce 0 _ hnh]
  simpa [DTM.run] using hstep

/-- **单机倍增主定理**：`dblOnce` 把 `⟨[none] ++ L, unary m ++ [none]⟩` 变成
    `⟨[none] ++ L, unary (2m) ++ [none]⟩`（`m ≥ 1`），共 `dblOnceSteps m` 步，
    终态为接受态。输入输出形状相同 ⇒ 可逐轮驱动（同 `unary_dbl_spec`）。
    The single-machine doubling: same input/output shape, so it can be driven round
    after round. -/
theorem dblOnce_run (m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    dblOnce.run (dblOnceSteps m)
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨dblOnce.accept, Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ := by
  rw [show dblOnceSteps m = dblOncePreSteps m + 1 from rfl,
    DTM.run_add dblOnce (dblOncePreSteps m) 1, dblOnce_run_pre m hm L, dblOnce_last m L]

/-- **整轮不停机**：`dblOnce` 在 `dblOnceSteps m` 步内从未停机（唯一终止在最后一步）。
    `dblOnce` never halts before its last step. -/
theorem dblOnce_no_halt (m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    ∀ k, k < dblOnceSteps m →
      dblOnce.halted
        (dblOnce.run k ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩) = false := by
  intro k hk
  by_cases hk' : k < dblOncePreSteps m
  · refine halted_false_before dblOnce (dblOncePreSteps m)
      ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ ?_ ?_ k hk'
    · intro h
      rw [show (dblOnce.run (dblOncePreSteps m)
            ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩).state
          = Fin.natAdd 4 (1 : Fin 3) from by rw [dblOnce_run_pre m hm L]] at h
      exact absurd h (by decide)
    · intro h
      rw [show (dblOnce.run (dblOncePreSteps m)
            ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩).state
          = Fin.natAdd 4 (1 : Fin 3) from by rw [dblOnce_run_pre m hm L]] at h
      exact absurd h (by decide)
  · have hs : dblOnceSteps m = dblOncePreSteps m + 1 := rfl
    have hk1 : k = dblOncePreSteps m := by omega
    subst hk1
    rw [dblOnce_run_pre m hm L]
    exact dblOnce_mid_halted m L

/-- 轮间自动重启的倍增机：状态 `0..6` 与 `dblOnce` 相同，但 `dblOnce` 的接受态 6
    被改写成「原地回到起始态 0」（不写、不动），因而每轮结束后立刻开始下一轮；
    机器本身**永不接受**（接受/拒绝占位态 7 不可达）。
    The chained doubling machine: `dblOnce`'s accept state is redirected back to the start,
    so rounds follow each other automatically; the machine never halts. -/
def dblChained : DTM (4 + 3 + 1) where
  step := fun s a =>
    if s.val = 6 then ((⟨0, by omega⟩ : Fin (4 + 3 + 1)), a, Dir.stay)
    else if h : s.val < 7 then
      let r := dblOnce.step ⟨s.val, h⟩ a
      (Fin.castLE (by omega) r.1, r.2)
    else (s, a, Dir.stay)
  start := 0
  accept := 7
  reject := 7

/-- 链式机在 `dblOnce` 接受态上的转移：原地回到起始态（写回读到的符号、不动）。
    The chained transition at `dblOnce`'s accept state: back to the start, tape untouched. -/
theorem dblChained_step_accept (a : Sym) :
    dblChained.step (Fin.castLE (by omega) dblOnce.accept) a
      = ((⟨0, by omega⟩ : Fin (4 + 3 + 1)), a, Dir.stay) := by
  have hval : dblOnce.accept.val = 6 := rfl
  simp only [dblChained, Fin.val_castLE]
  rw [if_pos hval]

/-- 链式机的转移在 `dblOnce` 的非接受状态上照抄 `dblOnce`。
    The chained machine copies `dblOnce`'s transitions away from its accept state. -/
theorem dblChained_step_castLE (s : Fin 7) (a : Sym) (hne : s ≠ dblOnce.accept) :
    dblChained.step (Fin.castLE (by omega) s) a
      = (Fin.castLE (by omega) (dblOnce.step s a).1, (dblOnce.step s a).2) := by
  have hv : s.val ≠ 6 := by
    intro h
    apply hne
    have hacc : dblOnce.accept = (⟨6, by omega⟩ : Fin 7) := rfl
    rw [hacc]
    exact Fin.ext h
  have hlt : s.val < 7 := s.isLt
  simp only [dblChained, Fin.val_castLE]
  rw [if_neg (by simpa using hv)]
  rw [dif_pos hlt]

/-- 链式机的接受/拒绝占位态不会与左侧状态重合（左侧状态的值 < 7）。
    The placeholder terminal state never coincides with a `dblOnce`-side state. -/
theorem dblChained_halt_castLE (s : Fin 7) :
    dblChained.accept ≠ Fin.castLE (by omega) s
      ∧ dblChained.reject ≠ Fin.castLE (by omega) s := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_castLE] at hv
    have h2 : dblChained.accept.val = 7 := rfl
    rw [h2] at hv
    have h3 := s.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_castLE] at hv
    have h2 : dblChained.reject.val = 7 := rfl
    rw [h2] at hv
    have h3 := s.isLt
    omega

/-- 链式机照搬 `dblOnce` 的任意一段运行（`dblOnce` 在这段内不停机）。
    Chained runs mirror `dblOnce` runs as long as `dblOnce` does not halt. -/
theorem dblChained_run_embed (n : Nat) (c : Config 7)
    (hnh : ∀ k, k < n → dblOnce.halted (dblOnce.run k c) = false) :
    dblChained.run n ⟨Fin.castLE (by omega) c.state, c.tape⟩ =
      ⟨Fin.castLE (by omega) (dblOnce.run n c).state, (dblOnce.run n c).tape⟩ :=
  run_embed dblOnce dblChained (Fin.castLE (by omega))
    (fun s a ha _ => dblChained_step_castLE s a ha)
    (fun s _ _ => dblChained_halt_castLE s) n c hnh

/-- **链式一轮**：跑完一轮倍增后**自动回到起始态**，纸带已是 `unary (2m)`，
    共 `dblOnceSteps m + 1` 步。
    One chained round: same tape effect as `dblOnce`, but back in the start state. -/
theorem dblChained_round (m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    dblChained.run (dblOnceSteps m + 1)
      ⟨dblChained.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨dblChained.start, Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ := by
  -- 起点换成 `run_embed` 输出的嵌入形态（`Fin.castLE` 版本，与起始态 0 只是 defeq）
  show dblChained.run (dblOnceSteps m + 1)
      ⟨Fin.castLE (by omega) dblOnce.start,
        Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨dblChained.start, Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩
  -- 前段照搬 `dblOnce` 的整轮
  have hemb := dblChained_run_embed (dblOnceSteps m)
    ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ (dblOnce_no_halt m hm L)
  rw [dblOnce_run m hm L] at hemb
  -- 整理投影/结构字面量的形态（与目标同形）
  have hemb' : dblChained.run (dblOnceSteps m)
      ⟨Fin.castLE (by omega) dblOnce.start,
        Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨Fin.castLE (by omega) dblOnce.accept,
        Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ := by
    simpa using hemb
  -- 收尾步：接受态 6 → 起始态 0（原地、纸带不变）
  have hnh2 : dblChained.halted
      ⟨Fin.castLE (by omega) dblOnce.accept,
        Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ = false := by
    rw [DTM.halted, Bool.or_eq_false_iff]
    refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castLE] at hv
      have h2 : dblOnce.accept.val = 6 := rfl
      rw [h2] at hv
      have h3 : dblChained.accept.val = 7 := rfl
      rw [h3] at hv
      exact absurd hv (by decide)
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castLE] at hv
      have h2 : dblOnce.accept.val = 6 := rfl
      rw [h2] at hv
      have h3 : dblChained.reject.val = 7 := rfl
      rw [h3] at hv
      exact absurd hv (by decide)
  have hstep : dblChained.stepConfig
      ⟨Fin.castLE (by omega) dblOnce.accept,
        Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ =
      ⟨(⟨0, by omega⟩ : Fin (4 + 3 + 1)),
        Tape.mk ([none] ++ L) (unary (m + m) ++ [none])⟩ := by
    rw [DTM.stepConfig, dblChained_step_accept]
    simp [Tape.write_read, Tape.move]
  rw [DTM.run_add dblChained (dblOnceSteps m) 1, hemb']
  rw [DTM.run_succ_of_not_halted dblChained 0 _ hnh2]
  simpa [DTM.run, dblChained] using hstep

/-- `r` 轮链式倍增的总步数（每轮长度随计数翻倍而不同）。
    Total step count of `r` chained doubling rounds. -/
def dblChainSteps : Nat → Nat → Nat
  | 0, _ => 0
  | r + 1, m => dblChainSteps r m + (dblOnceSteps (m * 2 ^ r) + 1)

/-- **多轮链式倍增**：`dblChained` 自动连跑 `r` 轮，计数 `m ↦ m·2^r`，
    纸带形状 `⟨[none] ++ L, unary _ ++ [none]⟩` 全程不变、机器全程不停机。
    `r` chained rounds: `m ↦ m * 2^r` with the tape shape preserved. -/
theorem dblChained_rounds (r m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    dblChained.run (dblChainSteps r m)
      ⟨dblChained.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨dblChained.start, Tape.mk ([none] ++ L) (unary (m * 2 ^ r) ++ [none])⟩ := by
  induction r generalizing m with
  | zero => simp [dblChainSteps, DTM.run]
  | succ r ih =>
      rw [dblChainSteps,
        DTM.run_add dblChained (dblChainSteps r m) (dblOnceSteps (m * 2 ^ r) + 1),
        ih m hm,
        dblChained_round (m * 2 ^ r)
          (show 1 ≤ m * 2 ^ r from
            Nat.mul_pos (by omega) (Nat.pow_pos (by decide : 0 < 2))) L]
      -- 指数对齐：`m·2^r + m·2^r = m·2^(r+1)`
      have h : m * 2 ^ r + (m * 2 ^ r) = m * 2 ^ (r + 1) := by
        rw [Nat.pow_succ, ← Nat.mul_add m (2 ^ r) (2 ^ r),
          show 2 ^ r + 2 ^ r = 2 ^ r * 2 from by omega]
      rw [h]

/-- **多轮倍增可拼接**：先跑 `r` 轮、再跑 `r'` 轮，等于跑 `r + r'` 轮（步数相加）。
    Two batches of chained doubling rounds concatenate: `r` then `r'` = `r + r'`. -/
theorem dblChained_rounds_add (r r' m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    dblChained.run (dblChainSteps r m + dblChainSteps r' (m * 2 ^ r))
      ⟨dblChained.start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨dblChained.start, Tape.mk ([none] ++ L) (unary (m * 2 ^ (r + r')) ++ [none])⟩ := by
  rw [DTM.run_add dblChained (dblChainSteps r m) (dblChainSteps r' (m * 2 ^ r)),
    dblChained_rounds r m hm L,
    dblChained_rounds r' (m * 2 ^ r) (Nat.mul_pos hm (Nat.pow_pos (by decide : 0 < 2))) L,
    Nat.pow_add, Nat.mul_assoc]

end DTM

end Pnp
