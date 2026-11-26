/-
  文件：Pnp/Machine/CounterRegion.lean
  File: Pnp/Machine/CounterRegion.lean

  主题：**unary 计数器区**的走位与增减件（B5 外层枚举 E 的 L1 路线 C，#280/#281）。
  Topic: walking / increment / decrement machines for the unary counter region (route C).

  计数器区布局（纸带左端方向 write 成「头朝向外的顺序」，即 `Tape.mk L R` 的 `L` 头紧贴读写头）：
      `[标志格 some false][真格串 true^i][消费空白…][已写数字区…]`
  - 加一（`extendTrue`，#281）：在真格串右端（头部所在处）写一个真格，串长 `k ↦ k+1`；
  - 减一（`shrinkTrue`）：头停在串右侧空白上时，左移一格把紧贴头部的真格擦成空白；
  - 走位件 `skipNonBlankL` / `skipBlankL`：从写区向计数区回扫时「跳过已写块」、
    「跳过已消费空白」，两者拼接即到达未消费真格串的边界。
  Layout (head-outward): `[marker false][true^i][consumed blanks…][written digit area…]`.
-/

import Pnp.Machine.DigitShape
import Pnp.Machine.WalkLT

namespace Pnp

namespace DTM

/-- 未停机时 `run 1` 就是一步（本文件自带的局部版本，避免额外依赖）。
    `run 1` is one step when the configuration is not halted. -/
theorem run_one_stp {n : Nat} (M : DTM n) (c : Config n) (h : M.halted c = false) :
    M.run 1 c = M.stepConfig c := by
  rw [show (1 : Nat) = 0 + 1 from rfl, DTM.run_succ_of_not_halted _ 0 _ h]
  rfl

/-! ### 左向跳过非空白 -/

/-- **左向跳过非空白**：左移越过所有非空白格，停在第一个空白格上并接受。
    Skips non-blank cells to the left; halts on the first blank. -/
def skipNonBlankL : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then ((1 : Fin 2), a, Dir.stay)
      else ((0 : Fin 2), a, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态处的格局不停机。 A start-state configuration never halts. -/
theorem skipNonBlankL_halted_start (L R : List Sym) :
    skipNonBlankL.halted ⟨(0 : Fin 2), Tape.mk L R⟩ = false := by
  show (((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))
      || ((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))) = false
  decide

/-- 非终止状态（≠ 1）不停机。 States other than 1 never halt. -/
theorem skipNonBlankL_halted_ne (st : Nat) (hst : st < 2) (h1 : st ≠ 1) (t : Tape) :
    skipNonBlankL.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show skipNonBlankL.accept.val = 1 from rfl] at hv
    exact h1 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show skipNonBlankL.reject.val = 1 from rfl] at hv
    exact h1 hv

/-- 读到空白：停在原地并接受。 On a blank: stay and accept. -/
theorem skipNonBlankL_step_blank (L R : List Sym) :
    skipNonBlankL.stepConfig ⟨(0 : Fin 2), Tape.mk L (none :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk L (none :: R)⟩ :=
  stepConfig_of_lit skipNonBlankL (0 : Fin 2) none L R (1 : Fin 2) none Dir.stay
    (Tape.mk L (none :: R))
    (by
      simp only [skipNonBlankL]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 读到非空白：左移一格（左侧必须非空）。 On a non-blank: move left. -/
theorem skipNonBlankL_step_left (x : Sym) (L R : List Sym) (a : Sym) (ha : a ≠ none) :
    skipNonBlankL.stepConfig ⟨(0 : Fin 2), Tape.mk (x :: L) (a :: R)⟩ =
      ⟨(0 : Fin 2), Tape.mk L (x :: a :: R)⟩ :=
  stepConfig_of_lit skipNonBlankL (0 : Fin 2) a (x :: L) R (0 : Fin 2) a Dir.left
    (Tape.mk L (x :: a :: R))
    (by
      simp only [skipNonBlankL]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- **整段运行**：左带 `xs`（全非空白）、其后一个空白，`|xs| + 2` 步后头停在空白上。
    Full run: over `xs` (all non-blank) onto the blank behind them. -/
theorem skipNonBlankL_run : ∀ (xs : List Sym), (∀ x ∈ xs, x ≠ none) →
    ∀ (a : Sym) (ha : a ≠ none) (L R : List Sym),
      skipNonBlankL.run (xs.length + 2)
          ⟨(0 : Fin 2), Tape.mk (xs ++ none :: L) (a :: R)⟩ =
        ⟨(1 : Fin 2), Tape.mk L (none :: (xs.reverse ++ a :: R))⟩
  | [], _, a, ha, L, R => by
      show skipNonBlankL.run (0 + 2)
          ⟨(0 : Fin 2), Tape.mk ([] ++ none :: L) (a :: R)⟩ = _
      rw [List.nil_append, show (0 + 2 : Nat) = 1 + 1 from rfl,
        DTM.run_add skipNonBlankL 1 1]
      rw [run_one_stp _ _ (skipNonBlankL_halted_start (none :: L) (a :: R))]
      rw [skipNonBlankL_step_left none L R a ha]
      rw [run_one_stp _ _ (skipNonBlankL_halted_start L (none :: a :: R))]
      rw [skipNonBlankL_step_blank L (a :: R)]
      rfl
  | x :: xs, hx, a, ha, L, R => by
      have hxs : ∀ y ∈ xs, y ≠ none := fun y hy => hx y (List.mem_cons_of_mem x hy)
      have hxne : x ≠ none := hx x List.mem_cons_self
      show skipNonBlankL.run ((x :: xs).length + 2)
          ⟨(0 : Fin 2), Tape.mk ((x :: xs) ++ none :: L) (a :: R)⟩ = _
      rw [List.cons_append]
      have hlen : (x :: xs).length = xs.length + 1 := by rw [List.length_cons]
      rw [show (x :: xs).length + 2 = (xs.length + 2) + 1 from by omega]
      rw [DTM.run_succ_of_not_halted skipNonBlankL (xs.length + 2) _
        (skipNonBlankL_halted_start (x :: (xs ++ none :: L)) (a :: R))]
      rw [skipNonBlankL_step_left x (xs ++ none :: L) R a ha]
      rw [skipNonBlankL_run xs hxs x hxne L (a :: R)]
      rw [List.reverse_cons, List.append_assoc]
      rfl

/-! ### 右向跳过非空白 -/

/-- **右向跳过非空白**：右移越过所有非空白格，停在第一个空白格上并接受。
    数字区组循环中用于「从刚写出的块向右穿过旧段，走到下一段」。
    Skips non-blank cells to the right; halts on the first blank. -/
def skipNonBlankR : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then ((1 : Fin 2), a, Dir.stay)
      else ((0 : Fin 2), a, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态处的格局不停机。 A start-state configuration never halts. -/
theorem skipNonBlankR_halted_start (L R : List Sym) :
    skipNonBlankR.halted ⟨(0 : Fin 2), Tape.mk L R⟩ = false := by
  show (((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))
      || ((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))) = false
  decide

/-- 非终止状态（≠ 1）不停机。 States other than 1 never halt. -/
theorem skipNonBlankR_halted_ne (st : Nat) (hst : st < 2) (h1 : st ≠ 1) (t : Tape) :
    skipNonBlankR.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show skipNonBlankR.accept.val = 1 from rfl] at hv
    exact h1 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show skipNonBlankR.reject.val = 1 from rfl] at hv
    exact h1 hv

/-- 读到空白：停在原地并接受。 On a blank: stay and accept. -/
theorem skipNonBlankR_step_blank (L R : List Sym) :
    skipNonBlankR.stepConfig ⟨(0 : Fin 2), Tape.mk L (none :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk L (none :: R)⟩ :=
  stepConfig_of_lit skipNonBlankR (0 : Fin 2) none L R (1 : Fin 2) none Dir.stay
    (Tape.mk L (none :: R))
    (by
      simp only [skipNonBlankR]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 读到非空白：右移一格。 On a non-blank: move right. -/
theorem skipNonBlankR_step_right (L : List Sym) (a : Sym) (R : List Sym) (ha : a ≠ none) :
    skipNonBlankR.stepConfig ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩ =
      ⟨(0 : Fin 2), Tape.mk (a :: L) R⟩ :=
  stepConfig_of_lit skipNonBlankR (0 : Fin 2) a L R (0 : Fin 2) a Dir.right
    (Tape.mk (a :: L) R)
    (by
      simp only [skipNonBlankR]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- **整段运行**：右带 `xs`（全非空白）后接一个空白，`|xs| + 1` 步后头停在那个空白上。
    Full run: over `xs` (all non-blank) onto the blank behind them. -/
theorem skipNonBlankR_run : ∀ (xs : List Sym), (∀ x ∈ xs, x ≠ none) →
    ∀ (L R : List Sym),
      skipNonBlankR.run (xs.length + 1)
          ⟨(0 : Fin 2), Tape.mk L (xs ++ none :: R)⟩ =
        ⟨(1 : Fin 2), Tape.mk (xs.reverse ++ L) (none :: R)⟩
  | [], _, L, R => by
      show skipNonBlankR.run (0 + 1)
          ⟨(0 : Fin 2), Tape.mk L ([] ++ none :: R)⟩ = _
      rw [List.nil_append]
      rw [run_one_stp _ _ (skipNonBlankR_halted_start L (none :: R))]
      rw [skipNonBlankR_step_blank L R]
      rfl
  | x :: xs, hx, L, R => by
      have hxs : ∀ y ∈ xs, y ≠ none := fun y hy => hx y (List.mem_cons_of_mem x hy)
      have hxne : x ≠ none := hx x List.mem_cons_self
      show skipNonBlankR.run ((x :: xs).length + 1)
          ⟨(0 : Fin 2), Tape.mk L ((x :: xs) ++ none :: R)⟩ = _
      rw [List.cons_append]
      rw [List.length_cons]
      rw [show xs.length + 1 + 1 = (xs.length + 1) + 1 from rfl]
      rw [DTM.run_succ_of_not_halted skipNonBlankR (xs.length + 1) _
        (skipNonBlankR_halted_start L (x :: (xs ++ none :: R)))]
      rw [skipNonBlankR_step_right L x (xs ++ none :: R) hxne]
      rw [skipNonBlankR_run xs hxs (x :: L) R]
      rw [List.reverse_cons, List.append_assoc]
      rfl

/-! ### 左向跳过空白 -/

/-- **左向跳过空白**：左移越过所有空白格，停在第一个非空白格上并接受。
    Skips blanks to the left; halts on the first non-blank. -/
def skipBlankL : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then ((0 : Fin 2), a, Dir.left)
      else ((1 : Fin 2), a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态处的格局不停机。 A start-state configuration never halts. -/
theorem skipBlankL_halted_start (L R : List Sym) :
    skipBlankL.halted ⟨(0 : Fin 2), Tape.mk L R⟩ = false := by
  show (((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))
      || ((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))) = false
  decide

/-- 读到空白：左移一格（左侧必须非空）。 On a blank: move left. -/
theorem skipBlankL_step_left (x : Sym) (L R : List Sym) :
    skipBlankL.stepConfig ⟨(0 : Fin 2), Tape.mk (x :: L) (none :: R)⟩ =
      ⟨(0 : Fin 2), Tape.mk L (x :: none :: R)⟩ :=
  stepConfig_of_lit skipBlankL (0 : Fin 2) none (x :: L) R (0 : Fin 2) none Dir.left
    (Tape.mk L (x :: none :: R))
    (by
      simp only [skipBlankL]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 读到非空白：停在原地并接受。 On a non-blank: stay and accept. -/
theorem skipBlankL_step_stop (L R : List Sym) (a : Sym) (ha : a ≠ none) :
    skipBlankL.stepConfig ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk L (a :: R)⟩ :=
  stepConfig_of_lit skipBlankL (0 : Fin 2) a L R (1 : Fin 2) a Dir.stay
    (Tape.mk L (a :: R))
    (by
      simp only [skipBlankL]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- **整段运行**：头在空白上、左带 `m` 个空白后接非空白 `a`，`m + 2` 步后停在 `a` 上。
    Full run: over `m` blanks (plus the head cell) onto the following non-blank. -/
theorem skipBlankL_run : ∀ (m : Nat) (a : Sym) (ha : a ≠ none) (L R : List Sym),
    skipBlankL.run (m + 2)
        ⟨(0 : Fin 2), Tape.mk (List.replicate m none ++ a :: L) (none :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk L (a :: (List.replicate (m + 1) none ++ R))⟩
  | 0, a, ha, L, R => by
      rw [List.replicate_zero, List.nil_append]
      show skipBlankL.run (0 + 2) ⟨(0 : Fin 2), Tape.mk (a :: L) (none :: R)⟩ = _
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add skipBlankL 1 1]
      rw [run_one_stp _ _ (skipBlankL_halted_start (a :: L) (none :: R))]
      rw [skipBlankL_step_left a L R]
      rw [run_one_stp _ _ (skipBlankL_halted_start L (a :: none :: R))]
      rw [skipBlankL_step_stop L (none :: R) a ha]
      rfl
  | m + 1, a, ha, L, R => by
      rw [List.replicate_succ, List.cons_append]
      show skipBlankL.run (m + 1 + 2)
          ⟨(0 : Fin 2), Tape.mk (none :: (List.replicate m none ++ a :: L)) (none :: R)⟩ = _
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add skipBlankL 1 (m + 2)]
      rw [run_one_stp _ _ (skipBlankL_halted_start
        (none :: (List.replicate m none ++ a :: L)) (none :: R))]
      rw [skipBlankL_step_left none (List.replicate m none ++ a :: L) R]
      rw [skipBlankL_run m a ha L (none :: R)]
      rw [replicate_succ_append (m + 1) none R]

/-! ### unary 减一 -/

/-- **unary 减一**：头停在真格串右侧空白上时，左移一格再把它擦成空白；2 步停机。
    Unary decrement: move left onto the last true cell, erase it, halt (2 steps). -/
def shrinkTrue : DTM 3 where
  step := fun s a =>
    if s.val = 0 then ((1 : Fin 3), a, Dir.left)
    else if s.val = 1 then ((2 : Fin 3), none, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 2

/-- 非终止状态（≠ 2）不停机。 States other than 2 never halt. -/
theorem shrinkTrue_halted_ne (st : Nat) (hst : st < 3) (h2 : st ≠ 2) (t : Tape) :
    shrinkTrue.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show shrinkTrue.accept.val = 2 from rfl] at hv
    exact h2 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show shrinkTrue.reject.val = 2 from rfl] at hv
    exact h2 hv

/-- 状态 0 处的格局不停机（字面量版，供 `rw` 匹配）。 State-0 configurations never halt. -/
theorem shrinkTrue_halted_zero (L R : List Sym) :
    shrinkTrue.halted ⟨(0 : Fin 3), Tape.mk L R⟩ = false := by
  show (((0 : Fin 3) == (⟨2, by omega⟩ : Fin 3))
      || ((0 : Fin 3) == (⟨2, by omega⟩ : Fin 3))) = false
  decide

/-- 状态 1 处的格局不停机（字面量版）。 State-1 configurations never halt. -/
theorem shrinkTrue_halted_one (L R : List Sym) :
    shrinkTrue.halted ⟨(1 : Fin 3), Tape.mk L R⟩ = false := by
  show (((1 : Fin 3) == (⟨2, by omega⟩ : Fin 3))
      || ((1 : Fin 3) == (⟨2, by omega⟩ : Fin 3))) = false
  decide

/-- 第一步：左移一格（左侧必须非空）。 Step one: move left. -/
theorem shrinkTrue_step_left (x : Sym) (L : List Sym) (a : Sym) (R : List Sym) :
    shrinkTrue.stepConfig ⟨(0 : Fin 3), Tape.mk (x :: L) (a :: R)⟩ =
      ⟨(1 : Fin 3), Tape.mk L (x :: a :: R)⟩ :=
  stepConfig_of_lit shrinkTrue (0 : Fin 3) a (x :: L) R (1 : Fin 3) a Dir.left
    (Tape.mk L (x :: a :: R))
    (by
      simp only [shrinkTrue]
      rw [if_pos (show (0 : Fin 3).val = 0 from rfl)])
    (by rfl)

/-- 第二步：把当前格擦成空白并停机。 Step two: erase the head cell and halt. -/
theorem shrinkTrue_step_erase (L : List Sym) (x : Sym) (R : List Sym) :
    shrinkTrue.stepConfig ⟨(1 : Fin 3), Tape.mk L (x :: R)⟩ =
      ⟨(2 : Fin 3), Tape.mk L (none :: R)⟩ :=
  stepConfig_of_lit shrinkTrue (1 : Fin 3) x L R (2 : Fin 3) none Dir.stay
    (Tape.mk L (none :: R))
    (by
      simp only [shrinkTrue]
      rw [if_neg (show ¬ ((1 : Fin 3).val = 0) from by decide)]
      rw [if_pos (show (1 : Fin 3).val = 1 from rfl)])
    (by rfl)

/-- **减一整段**：真格串长度 `m+1 ↦ m`（头回停在串右侧空白上）。
    Decrement: the true run goes `m+1 ↦ m` in 2 steps. -/
theorem shrinkTrue_run (m : Nat) (L R : List Sym) :
    shrinkTrue.run 2
        ⟨(0 : Fin 3), Tape.mk (List.replicate (m + 1) (some true) ++ L) (none :: R)⟩ =
      ⟨(2 : Fin 3), Tape.mk (List.replicate m (some true) ++ L) (none :: none :: R)⟩ := by
  have hrep : List.replicate (m + 1) (some true) ++ L
      = some true :: (List.replicate m (some true) ++ L) := by
    rw [List.replicate_succ, List.cons_append]
  show shrinkTrue.run (1 + 1)
      ⟨(0 : Fin 3), Tape.mk (List.replicate (m + 1) (some true) ++ L) (none :: R)⟩ =
    ⟨(2 : Fin 3), Tape.mk (List.replicate m (some true) ++ L) (none :: none :: R)⟩
  rw [DTM.run_add shrinkTrue 1 1]
  rw [run_one_stp _ _ (shrinkTrue_halted_zero _ _)]
  rw [hrep]
  rw [shrinkTrue_step_left (some true) (List.replicate m (some true) ++ L) none R]
  rw [run_one_stp _ _ (shrinkTrue_halted_one _ _)]
  rw [shrinkTrue_step_erase (List.replicate m (some true) ++ L)]

/-! ### 左向组合回扫（跳过已写区，再跳过已消费空白） -/

/-- **左向组合回扫**：相位 0 左移跳过所有非空白（已写块），相位 1 左移跳过所有空白
    （已消费区），停在第一个非空白上（未消费真格或计数器标志格）。
    Two-phase left scan: skip non-blank (written blocks), then skip blanks (consumed
    region), halting on the first non-blank. -/
def scanBackL : DTM 3 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then ((1 : Fin 3), a, Dir.stay)
      else ((0 : Fin 3), a, Dir.left)
    else if s.val = 1 then
      if a = none then ((1 : Fin 3), a, Dir.left)
      else ((2 : Fin 3), a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 2

/-- 状态 0 处的格局不停机。 State-0 configurations never halt. -/
theorem scanBackL_halted_zero (L R : List Sym) :
    scanBackL.halted ⟨(0 : Fin 3), Tape.mk L R⟩ = false := by
  show (((0 : Fin 3) == (⟨2, by omega⟩ : Fin 3))
      || ((0 : Fin 3) == (⟨2, by omega⟩ : Fin 3))) = false
  decide

/-- 状态 1 处的格局不停机。 State-1 configurations never halt. -/
theorem scanBackL_halted_one (L R : List Sym) :
    scanBackL.halted ⟨(1 : Fin 3), Tape.mk L R⟩ = false := by
  show (((1 : Fin 3) == (⟨2, by omega⟩ : Fin 3))
      || ((1 : Fin 3) == (⟨2, by omega⟩ : Fin 3))) = false
  decide

/-- 相位 0 读到非空白：左移一格。 Phase 0 on a non-blank: move left. -/
theorem scanBackL_step_nb (x : Sym) (L : List Sym) (a : Sym) (R : List Sym) (ha : a ≠ none) :
    scanBackL.stepConfig ⟨(0 : Fin 3), Tape.mk (x :: L) (a :: R)⟩ =
      ⟨(0 : Fin 3), Tape.mk L (x :: a :: R)⟩ :=
  stepConfig_of_lit scanBackL (0 : Fin 3) a (x :: L) R (0 : Fin 3) a Dir.left
    (Tape.mk L (x :: a :: R))
    (by
      simp only [scanBackL]
      rw [if_pos (show (0 : Fin 3).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- 相位 0 读到空白：转入相位 1、原地不动。 Phase 0 on a blank: switch to phase 1. -/
theorem scanBackL_step_switch (L R : List Sym) :
    scanBackL.stepConfig ⟨(0 : Fin 3), Tape.mk L (none :: R)⟩ =
      ⟨(1 : Fin 3), Tape.mk L (none :: R)⟩ :=
  stepConfig_of_lit scanBackL (0 : Fin 3) none L R (1 : Fin 3) none Dir.stay
    (Tape.mk L (none :: R))
    (by
      simp only [scanBackL]
      rw [if_pos (show (0 : Fin 3).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 相位 1 读到空白：左移一格。 Phase 1 on a blank: move left. -/
theorem scanBackL_step_bl (x : Sym) (L R : List Sym) :
    scanBackL.stepConfig ⟨(1 : Fin 3), Tape.mk (x :: L) (none :: R)⟩ =
      ⟨(1 : Fin 3), Tape.mk L (x :: none :: R)⟩ :=
  stepConfig_of_lit scanBackL (1 : Fin 3) none (x :: L) R (1 : Fin 3) none Dir.left
    (Tape.mk L (x :: none :: R))
    (by
      simp only [scanBackL]
      rw [if_neg (show ¬ ((1 : Fin 3).val = 0) from by decide)]
      rw [if_pos (show (1 : Fin 3).val = 1 from rfl)]
      rfl)
    (by rfl)

/-- 相位 1 读到非空白：停在原地并停机（进入接受态 2）。 Phase 1 on a non-blank: halt. -/
theorem scanBackL_step_hit (L R : List Sym) (a : Sym) (ha : a ≠ none) :
    scanBackL.stepConfig ⟨(1 : Fin 3), Tape.mk L (a :: R)⟩ =
      ⟨(2 : Fin 3), Tape.mk L (a :: R)⟩ :=
  stepConfig_of_lit scanBackL (1 : Fin 3) a L R (2 : Fin 3) a Dir.stay
    (Tape.mk L (a :: R))
    (by
      simp only [scanBackL]
      rw [if_neg (show ¬ ((1 : Fin 3).val = 0) from by decide)]
      rw [if_pos (show (1 : Fin 3).val = 1 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- 相位 1 的整段：越过 `m + 1` 个空白后停在非空白 `a` 上并停机。
    Phase-1 run: over `m + 1` blanks onto the non-blank `a`. -/
theorem scanBackL_skip_run : ∀ (m : Nat) (a : Sym) (ha : a ≠ none) (L R : List Sym),
    scanBackL.run (m + 2)
        ⟨(1 : Fin 3), Tape.mk (List.replicate m none ++ a :: L) (none :: R)⟩ =
      ⟨(2 : Fin 3), Tape.mk L (a :: (List.replicate (m + 1) none ++ R))⟩
  | 0, a, ha, L, R => by
      rw [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from by omega]
      rw [DTM.run_add scanBackL 1 1]
      rw [run_one_stp _ _ (scanBackL_halted_one (a :: L) (none :: R))]
      rw [scanBackL_step_bl a L R]
      rw [run_one_stp _ _ (scanBackL_halted_one L (a :: none :: R))]
      rw [scanBackL_step_hit L (none :: R) a ha]
      rfl
  | m + 1, a, ha, L, R => by
      rw [List.replicate_succ, List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega]
      rw [DTM.run_add scanBackL 1 (m + 2)]
      rw [run_one_stp _ _ (scanBackL_halted_one
        (none :: (List.replicate m none ++ a :: L)) (none :: R))]
      rw [scanBackL_step_bl none (List.replicate m none ++ a :: L) R]
      rw [scanBackL_skip_run m a ha L (none :: R)]
      rw [replicate_succ_append (m + 1) none R]

set_option maxHeartbeats 4000000 in
/-- **组合回扫整段**：头在已写区的最后一格 `b` 上，左带为「已写块 `blocks` + `m + 1` 个
    消费空白 + 未消费区的首格 `a`」；`|blocks| + m + 4` 步后头停在 `a` 上并停机。
    Full scan: over the written blocks and the consumed blanks onto `a`. -/
theorem scanBackL_run : ∀ (blocks : List Sym), (∀ x ∈ blocks, x ≠ none) →
    ∀ (m : Nat) (a : Sym) (ha : a ≠ none) (b : Sym) (bne : b ≠ none)
      (L R : List Sym),
      scanBackL.run (blocks.length + m + 4)
        ⟨(0 : Fin 3),
          Tape.mk (blocks ++ List.replicate (m + 1) none ++ a :: L) (b :: R)⟩ =
        ⟨(2 : Fin 3),
          Tape.mk L (a :: (List.replicate (m + 1) none ++ blocks.reverse ++ b :: R))⟩
  | [], _, m, a, ha, b, bne, L, R => by
      rw [List.nil_append, List.length_nil]
      rw [show (0 + m + 4 : Nat) = 1 + (1 + (m + 2)) from by omega]
      rw [DTM.run_add scanBackL 1 (1 + (m + 2))]
      rw [run_one_stp _ _ (scanBackL_halted_zero
        (List.replicate (m + 1) none ++ a :: L) (b :: R))]
      rw [show List.replicate (m + 1) none ++ a :: L
            = none :: (List.replicate m none ++ a :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [scanBackL_step_nb none (List.replicate m none ++ a :: L) b R bne]
      rw [DTM.run_add scanBackL 1 (m + 2)]
      rw [run_one_stp _ _ (scanBackL_halted_zero
        (List.replicate m none ++ a :: L) (none :: b :: R))]
      rw [scanBackL_step_switch (List.replicate m none ++ a :: L) (b :: R)]
      rw [scanBackL_skip_run m a ha L (b :: R)]
      simp
  | c :: cs, hx, m, a, ha, b, bne, L, R => by
      have hcs : ∀ y ∈ cs, y ≠ none := fun y hy => hx y (List.mem_cons_of_mem c hy)
      have hc : c ≠ none := hx c List.mem_cons_self
      rw [List.cons_append]
      rw [show (c :: cs).length + m + 4 = 1 + (cs.length + m + 4) from by
        rw [List.length_cons]; omega]
      rw [DTM.run_add scanBackL 1 (cs.length + m + 4)]
      rw [List.cons_append]
      rw [run_one_stp _ _ (scanBackL_halted_zero
        (c :: (cs ++ List.replicate (m + 1) none ++ a :: L)) (b :: R))]
      rw [scanBackL_step_nb c (cs ++ List.replicate (m + 1) none ++ a :: L) b R bne]
      rw [scanBackL_run cs hcs m a ha c hc L (b :: R)]
      rw [List.reverse_cons]
      simp

/-! ### 组消费：把最近至多 B 个真格翻成空白（计数值进状态） -/

/-- **组消费机**：从边界真格起左行，把真格逐个翻成空白，至多 `B` 个；状态值即已翻个数。
    读到非真格或已满 `B` 后原地吸收（后续步数不改变格局），故可作为相位串接。
    Group consumer: flip up to `B` true cells to blanks walking left; the state value is the
    number flipped; afterwards the configuration is a fixed point. -/
def consumeTrue (B : Nat) : DTM (B + 2) where
  step := fun s a =>
    if h : s.val < B then
      match a with
      | some true => (⟨s.val + 1, by omega⟩, none, Dir.left)
      | _ => (s, a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := ⟨B + 1, by omega⟩
  reject := ⟨B + 1, by omega⟩

/-- 非终止状态（≠ `B+1`）不停机。 States other than `B+1` never halt. -/
theorem consumeTrue_halted_false (B : Nat) (st : Nat) (hst : st < B + 2) (h : st ≠ B + 1)
    (t : Tape) : (consumeTrue B).halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (consumeTrue B).accept.val = B + 1 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (consumeTrue B).reject.val = B + 1 from rfl] at hv
    exact h hv

/-- 单步（读真格且未满）：翻成空白、左移一格。 One true cell flipped to blank, move left. -/
theorem consumeTrue_step_true (B st : Nat) (hs : st < B + 2) (hval : st < B)
    (x : Sym) (L R : List Sym) :
    (consumeTrue B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 2)) (Tape.mk (x :: L) (some true :: R))) =
      Config.mk (⟨st + 1, by omega⟩ : Fin (B + 2)) (Tape.mk L (x :: none :: R)) := by
  simp only [DTM.stepConfig, consumeTrue, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_pos hval]

/-- 单步（读非真格或已满 `B`）：原地吸收。 A non-true cell (or full): fixed point. -/
theorem consumeTrue_step_stuck (B st : Nat) (hs : st < B + 2) (a : Sym)
    (ha : a ≠ some true) (L R : List Sym) :
    (consumeTrue B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 2)) (Tape.mk L (a :: R))) =
      Config.mk (⟨st, hs⟩ : Fin (B + 2)) (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, consumeTrue, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  cases a with
  | none => split <;> rfl
  | some b =>
      cases b with
      | false => split <;> rfl
      | true => exact absurd rfl ha

/-- **组消费整段（带初值状态）**：从状态 `j`（已翻 `j` 个）起把 `k + 1` 个真格翻成空白，
    `k + 1` 步后状态为 `j + k + 1`，头停在紧随其后的非真格 `a₀` 上。
    Consumer run with an initial state: flip `k + 1` more true cells. -/
theorem consumeTrue_run_aux (B : Nat) :
    ∀ (k j : Nat) (h1 : j < B + 2) (h2 : j + k + 1 < B + 2) (hj : j + k + 1 ≤ B)
      (a₀ : Sym) (h₀ : a₀ ≠ some true) (L R : List Sym),
      (consumeTrue B).run (k + 1)
        ⟨(⟨j, h1⟩ : Fin (B + 2)),
          Tape.mk (List.replicate k (some true) ++ a₀ :: L) (some true :: R)⟩ =
        ⟨(⟨j + k + 1, h2⟩ : Fin (B + 2)),
          Tape.mk L (a₀ :: List.replicate (k + 1) none ++ R)⟩ := by
  intro k
  induction k with
  | zero =>
      intro j h1 h2 hj a₀ h₀ L R
      rw [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp (consumeTrue B)
        (Config.mk (⟨j, h1⟩ : Fin (B + 2)) (Tape.mk (a₀ :: L) (some true :: R)))
        (consumeTrue_halted_false B j h1 (by omega) (Tape.mk (a₀ :: L) (some true :: R)))]
      rw [consumeTrue_step_true B j h1 (by omega) a₀ L R]
      rw [List.replicate_one]
      rfl
  | succ k ih =>
      intro j h1 h2 hj a₀ h₀ L R
      rw [show List.replicate (k + 1) (some true) ++ a₀ :: L
            = some true :: (List.replicate k (some true) ++ a₀ :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show (k + 1) + 1 = 1 + (k + 1) from by omega]
      rw [DTM.run_add (consumeTrue B) 1 (k + 1)]
      rw [run_one_stp (consumeTrue B)
        (Config.mk (⟨j, h1⟩ : Fin (B + 2))
          (Tape.mk (some true :: (List.replicate k (some true) ++ a₀ :: L)) (some true :: R)))
        (consumeTrue_halted_false B j h1 (by omega)
          (Tape.mk (some true :: (List.replicate k (some true) ++ a₀ :: L)) (some true :: R)))]
      rw [consumeTrue_step_true B j h1 (by omega) (some true)
        (List.replicate k (some true) ++ a₀ :: L) R]
      rw [ih (j + 1) (by omega) (by omega) (by omega) a₀ h₀ L (none :: R)]
      rw [show 1 + (k + 1) = (k + 1) + 1 from by omega]
      rw [List.cons_append, replicate_succ_append]
      have hst : (j + 1) + k + 1 = j + (k + 1) + 1 := by omega
      simp only [hst]
      rfl

/-- **组消费整段**：从状态 0 起把 `k + 1` 个真格翻成空白，头停在非真格 `a₀` 上。
    Consumer run from the start state. -/
theorem consumeTrue_run (B k : Nat) (hk : k + 1 ≤ B) (a₀ : Sym) (h₀ : a₀ ≠ some true)
    (L R : List Sym) :
    (consumeTrue B).run (k + 1)
      ⟨(0 : Fin (B + 2)),
        Tape.mk (List.replicate k (some true) ++ a₀ :: L) (some true :: R)⟩ =
      ⟨(⟨k + 1, by omega⟩ : Fin (B + 2)),
        Tape.mk L (a₀ :: List.replicate (k + 1) none ++ R)⟩ := by
  have h1 : (0 : Nat) < B + 2 := by omega
  have h2 : (0 : Nat) + k + 1 < B + 2 := by omega
  have h := consumeTrue_run_aux B k 0 h1 h2 (by omega) a₀ h₀ L R
  simp only [Nat.zero_add] at h
  exact h

/-! ### 块写出：按状态里的计数值写出 `some false :: true^m`（左向写出） -/

/-- **块写出机**：入口状态 = 待写真格数 `m`；每步在头格写真格并左移（状态减一），
    状态归 0 时在头格写 `some false` 并右移一格停机。左向写出的物理顺序正好是
    `false :: true^m`，即 `blockCode` 的形状（`m = c + 2` 时就是 `blockCode c`）。
    Block writer: entered with state = number `m` of true cells to write; each step writes
    one true cell and moves left (state − 1), and at state 0 it writes `some false` and moves
    right, halting. Writing leftward yields `false :: true^m` physically — the `blockCode` shape. -/
def writeBlock (B : Nat) : DTM (B + 4) where
  step := fun s a =>
    if h : s.val = 0 then (⟨B + 3, by omega⟩, some false, Dir.right)
    else (⟨s.val - 1, by omega⟩, some true, Dir.left)
  start := 0
  accept := ⟨B + 3, by omega⟩
  reject := ⟨B + 3, by omega⟩

/-- 非终止状态（≠ `B+3`）不停机。 States other than `B+3` never halt. -/
theorem writeBlock_halted_false (B : Nat) (st : Nat) (hst : st < B + 4) (h : st ≠ B + 3)
    (t : Tape) : (writeBlock B).halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (writeBlock B).accept.val = B + 3 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (writeBlock B).reject.val = B + 3 from rfl] at hv
    exact h hv

/-- 计数步：头格改写为真格、左移、状态减一。 Counting step: write one true cell, move left. -/
theorem writeBlock_step_true (B st : Nat) (hs : st < B + 4) (h0 : st ≠ 0)
    (x : Sym) (L R : List Sym) :
    (writeBlock B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 4)) (Tape.mk (x :: L) R)) =
      Config.mk (⟨st - 1, by omega⟩ : Fin (B + 4))
        (Tape.mk L (x :: some true :: R.tail)) := by
  simp only [DTM.stepConfig, writeBlock, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_neg h0]

/-- 收尾步：状态 0 时头格写 `some false` 并右移停机。 Final step: write `some false`, move right. -/
theorem writeBlock_step_false (B st : Nat) (hs : st < B + 4) (h0 : st = 0)
    (L R : List Sym) :
    (writeBlock B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 4)) (Tape.mk L R)) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 4)) (Tape.mk (some false :: L) R.tail) := by
  simp only [DTM.stepConfig, writeBlock, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_pos h0]

/-- **块写出整段**：入口状态 `m`、`m + 1` 步后写出 `some false :: replicate m true`，
    头停在该块第一个真格上；左侧恰好消费 `m` 格、右侧尾部 `R₀.tail` 原样保留。
    Block writer run: entry state `m` yields the block `false :: true^m` in `m + 1` steps. -/
theorem writeBlock_run (B : Nat) :
    ∀ (m : Nat) (hm : m ≤ B + 2) (L₀ R₀ : List Sym), m ≤ L₀.length →
      (writeBlock B).run (m + 1)
        ⟨(⟨m, by omega⟩ : Fin (B + 4)), Tape.mk L₀ R₀⟩ =
      ⟨(⟨B + 3, by omega⟩ : Fin (B + 4)),
        Tape.mk (some false :: L₀.drop m) (List.replicate m (some true) ++ R₀.tail)⟩
  | 0, hm, L₀, R₀, hlen => by
      rw [Nat.zero_add]
      rw [run_one_stp (writeBlock B)
        (Config.mk (⟨(0 : Nat), by omega⟩ : Fin (B + 4)) (Tape.mk L₀ R₀))
        (writeBlock_halted_false B 0 (by omega) (by omega) (Tape.mk L₀ R₀))]
      rw [writeBlock_step_false B 0 (by omega) rfl L₀ R₀]
      rfl
  | m + 1, hm, L₀, R₀, hlen => by
      obtain ⟨x, L₁, hL⟩ : ∃ (x : Sym) (L₁ : List Sym), L₀ = x :: L₁ := by
        cases L₀ with
        | nil => simp at hlen
        | cons x L₁ => exact ⟨x, L₁, rfl⟩
      subst hL
      simp only [List.length_cons] at hlen
      rw [show m + 1 + 1 = 1 + (m + 1) from by omega]
      rw [DTM.run_add (writeBlock B) 1 (m + 1)]
      rw [run_one_stp (writeBlock B)
        (Config.mk (⟨(m + 1 : Nat), by omega⟩ : Fin (B + 4)) (Tape.mk (x :: L₁) R₀))
        (writeBlock_halted_false B (m + 1) (by omega) (by omega) (Tape.mk (x :: L₁) R₀))]
      rw [writeBlock_step_true B (m + 1) (by omega) (by omega) x L₁ R₀]
      simp only [show m + 1 - 1 = m from by omega]
      rw [writeBlock_run B m (by omega) L₁ (x :: some true :: R₀.tail) (by omega)]
      rw [List.drop_succ_cons, List.tail_cons, replicate_succ_append]

/-- **写出一整块 `blockCode c`**：入口状态 = `c + 2`（真格数），`c + 3` 步后物理上得到
    `some false :: true^(c+2)`（即 `blockCode c`：`false` 在最左、头停在块内第一个真格上）。
    Writing the whole block `blockCode c`: entry state `c + 2`, done in `c + 3` steps. -/
theorem writeBlock_run_blockCode (B c : Nat) (hc : c ≤ B) (L₀ R₀ : List Sym)
    (hlen : c + 2 ≤ L₀.length) :
    (writeBlock B).run (c + 3)
        ⟨(⟨c + 2, by omega⟩ : Fin (B + 4)), Tape.mk L₀ R₀⟩ =
      ⟨(⟨B + 3, by omega⟩ : Fin (B + 4)),
        Tape.mk (some false :: L₀.drop (c + 2))
          (List.replicate (c + 2) (some true) ++ R₀.tail)⟩ :=
  writeBlock_run B (c + 2) (by omega) L₀ R₀ hlen

/-! ### 组计数：非破坏地数出 unary 组长度（计数值进状态） -/

/-- **组计数机**：与 `consumeTrue` 同形，但**不擦除**——逐格左移、状态值加一，
    读到非真格（分隔格）即原地吸收。用于把计数器寄存器「读出来」而不破坏它。
    Group counter: like `consumeTrue` but non-destructive — the state value counts the true
    cells passed, and the machine becomes a fixed point on the first non-true cell. -/
def countGroup (B : Nat) : DTM (B + 2) where
  step := fun s a =>
    if h : s.val < B then
      match a with
      | some true => (⟨s.val + 1, by omega⟩, a, Dir.left)
      | _ => (s, a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := ⟨B + 1, by omega⟩
  reject := ⟨B + 1, by omega⟩

/-- 非终止状态（≠ `B+1`）不停机。 States other than `B+1` never halt. -/
theorem countGroup_halted_false (B : Nat) (st : Nat) (hst : st < B + 2) (h : st ≠ B + 1)
    (t : Tape) : (countGroup B).halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (countGroup B).accept.val = B + 1 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (countGroup B).reject.val = B + 1 from rfl] at hv
    exact h hv

/-- 计数步：读真格左移、状态加一（纸带只移动不改写）。 Counting step: move left, keep the cell. -/
theorem countGroup_step_true (B st : Nat) (hs : st < B + 2) (hval : st < B)
    (x : Sym) (L R : List Sym) :
    (countGroup B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 2)) (Tape.mk (x :: L) (some true :: R))) =
      Config.mk (⟨st + 1, by omega⟩ : Fin (B + 2)) (Tape.mk L (x :: some true :: R)) := by
  simp only [DTM.stepConfig, countGroup, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_pos hval]

/-- 吸收步：读非真格或已满 `B`，原地不动。 Fixed point on a non-true cell (or when full). -/
theorem countGroup_step_stuck (B st : Nat) (hs : st < B + 2) (a : Sym)
    (ha : a ≠ some true) (L R : List Sym) :
    (countGroup B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 2)) (Tape.mk L (a :: R))) =
      Config.mk (⟨st, hs⟩ : Fin (B + 2)) (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, countGroup, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  cases a with
  | none => split <;> rfl
  | some b =>
      cases b with
      | false => split <;> rfl
      | true => exact absurd rfl ha

/-- **组计数整段（带初值状态）**：从状态 `j` 起数过 `k + 1` 个真格，`k + 1` 步后状态
    `j + k + 1`，头停在紧随其后的非真格上，纸带只左移不改写。
    Counting run with an initial state: pass `k + 1` true cells without erasing them. -/
theorem countGroup_run_aux (B : Nat) :
    ∀ (k j : Nat) (h1 : j < B + 2) (h2 : j + k + 1 < B + 2) (hj : j + k + 1 ≤ B)
      (a₀ : Sym) (h₀ : a₀ ≠ some true) (L R : List Sym),
      (countGroup B).run (k + 1)
        ⟨(⟨j, h1⟩ : Fin (B + 2)),
          Tape.mk (List.replicate k (some true) ++ a₀ :: L) (some true :: R)⟩ =
        ⟨(⟨j + k + 1, h2⟩ : Fin (B + 2)),
          Tape.mk L (a₀ :: List.replicate (k + 1) (some true) ++ R)⟩ := by
  intro k
  induction k with
  | zero =>
      intro j h1 h2 hj a₀ h₀ L R
      rw [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp (countGroup B)
        (Config.mk (⟨j, h1⟩ : Fin (B + 2)) (Tape.mk (a₀ :: L) (some true :: R)))
        (countGroup_halted_false B j h1 (by omega) (Tape.mk (a₀ :: L) (some true :: R)))]
      rw [countGroup_step_true B j h1 (by omega) a₀ L R]
      rw [List.replicate_one]
      rfl
  | succ k ih =>
      intro j h1 h2 hj a₀ h₀ L R
      rw [show List.replicate (k + 1) (some true) ++ a₀ :: L
            = some true :: (List.replicate k (some true) ++ a₀ :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show (k + 1) + 1 = 1 + (k + 1) from by omega]
      rw [DTM.run_add (countGroup B) 1 (k + 1)]
      rw [run_one_stp (countGroup B)
        (Config.mk (⟨j, h1⟩ : Fin (B + 2))
          (Tape.mk (some true :: (List.replicate k (some true) ++ a₀ :: L)) (some true :: R)))
        (countGroup_halted_false B j h1 (by omega)
          (Tape.mk (some true :: (List.replicate k (some true) ++ a₀ :: L)) (some true :: R)))]
      rw [countGroup_step_true B j h1 (by omega) (some true)
        (List.replicate k (some true) ++ a₀ :: L) R]
      rw [ih (j + 1) (by omega) (by omega) (by omega) a₀ h₀ L (some true :: R)]
      rw [show 1 + (k + 1) = (k + 1) + 1 from by omega]
      rw [List.cons_append, replicate_succ_append]
      have hst : (j + 1) + k + 1 = j + (k + 1) + 1 := by omega
      simp only [hst]
      rfl

/-- **组计数整段**：从状态 0 起数出 `k + 1` 个真格（不擦除），头停在非真格上。
    Counting run from the start state: non-destructive, ends on the non-true cell. -/
theorem countGroup_run (B k : Nat) (hk : k + 1 ≤ B) (a₀ : Sym) (h₀ : a₀ ≠ some true)
    (L R : List Sym) :
    (countGroup B).run (k + 1)
      ⟨(0 : Fin (B + 2)),
        Tape.mk (List.replicate k (some true) ++ a₀ :: L) (some true :: R)⟩ =
      ⟨(⟨k + 1, by omega⟩ : Fin (B + 2)),
        Tape.mk L (a₀ :: List.replicate (k + 1) (some true) ++ R)⟩ := by
  have h1 : (0 : Nat) < B + 2 := by omega
  have h2 : (0 : Nat) + k + 1 < B + 2 := by omega
  have h := countGroup_run_aux B k 0 h1 h2 (by omega) a₀ h₀ L R
  simp only [Nat.zero_add] at h
  exact h

/-! ### 段清零：把一个 unary 组的真格全部改写成空白（右行） -/

/-- **段清零机**：右行掠过真格、逐格改写为空白，遇非真格（分隔格）即原地停机。
    进位时把溢出位清零用；清零后该组长度为 0，可再被 `extendTrue` 从空白处增长。
    Segment clearer: walking right, overwrite each true cell with a blank and halt on the
    first non-true cell. Used to zero an overflowing digit group before carrying. -/
def clearTrueR : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then ((0 : Fin 2), none, Dir.right)
      else ((1 : Fin 2), a, Dir.stay)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态处的格局不停机。 A start-state configuration never halts. -/
theorem clearTrueR_halted_start (L R : List Sym) :
    clearTrueR.halted ⟨(0 : Fin 2), Tape.mk L R⟩ = false := by
  show (((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))
      || ((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))) = false
  decide

/-- 清零步：读真格改写为空白、右移。 Clearing step: write a blank and move right. -/
theorem clearTrueR_step_true (L R : List Sym) :
    clearTrueR.stepConfig ⟨(0 : Fin 2), Tape.mk L (some true :: R)⟩ =
      ⟨(0 : Fin 2), Tape.mk (none :: L) R⟩ :=
  stepConfig_of_lit clearTrueR (0 : Fin 2) (some true) L R (0 : Fin 2) none Dir.right
    (Tape.mk (none :: L) R)
    (by
      simp only [clearTrueR]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 停机步：读非真格，原地进终止态。 Halting step on a non-true cell. -/
theorem clearTrueR_step_stop (L R : List Sym) (a : Sym) (ha : a ≠ some true) :
    clearTrueR.stepConfig ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk L (a :: R)⟩ :=
  stepConfig_of_lit clearTrueR (0 : Fin 2) a L R (1 : Fin 2) a Dir.stay
    (Tape.mk L (a :: R))
    (by
      simp only [clearTrueR]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- 清零过程：`k` 步把整段 `k` 个真格改写成空白，头停在非真格上（状态仍为 0）。
    Clearing walk over `k` true cells. -/
theorem clearTrueR_erase : ∀ (k : Nat) (L : List Sym) (a : Sym), a ≠ some true →
    ∀ (R : List Sym),
      clearTrueR.run k
          ⟨(0 : Fin 2), Tape.mk L (List.replicate k (some true) ++ a :: R)⟩ =
        ⟨(0 : Fin 2), Tape.mk (List.replicate k none ++ L) (a :: R)⟩
  | 0, L, a, _, R => by
      show clearTrueR.run 0 ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩ =
        ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩
      rfl
  | k + 1, L, a, ha, R => by
      rw [show List.replicate (k + 1) (some true) ++ a :: R
          = some true :: (List.replicate k (some true) ++ a :: R) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted _ k _
        (clearTrueR_halted_start L (some true :: (List.replicate k (some true) ++ a :: R)))]
      rw [clearTrueR_step_true L (List.replicate k (some true) ++ a :: R)]
      rw [clearTrueR_erase k (none :: L) a ha R]
      rw [replicate_succ_append]

/-- **段清零**：`k + 2` 步把一段 `k + 1` 个真格全部改写成空白并停机
    （`k + 1` 步擦除 + 1 步读到分隔格停机）。Segment clearing: `k + 1` true cells erased
    and halted in `k + 2` steps. -/
theorem clearTrueR_run (k : Nat) (L : List Sym) (a : Sym) (ha : a ≠ some true)
    (R : List Sym) :
    clearTrueR.run (k + 2)
        ⟨(0 : Fin 2), Tape.mk L (List.replicate (k + 1) (some true) ++ a :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk (List.replicate (k + 1) none ++ L) (a :: R)⟩ := by
  rw [show k + 2 = (k + 1) + 1 from by omega]
  rw [DTM.run_add clearTrueR (k + 1) 1]
  rw [clearTrueR_erase (k + 1) L a ha R]
  rw [run_one_stp clearTrueR
    ⟨(0 : Fin 2), Tape.mk (List.replicate (k + 1) none ++ L) (a :: R)⟩
    (clearTrueR_halted_start (List.replicate (k + 1) none ++ L) (a :: R))]
  rw [clearTrueR_step_stop (List.replicate (k + 1) none ++ L) R a ha]

/-! ### 单段加一：段内加一并给出「完成 / 进位」两种结局（进位链的单段件） -/

/-- **单段加一机**：头在该段第一个真格上、右侧是段的真格串 + 一个非真格。
    状态 `0..B` 计数；读到非真格时按新值 `s+1` 决策：未满 `B` ⇒ 追加一个真格进 `B+2`
    （完成，accept）；将满 `B` ⇒ 左移进 `B+1`（清零相位），从段尾逐格擦除，擦完进 `B+3`
    （进位，reject）。段长 `d` 满足 `d+1 < B` 时完成、`d+1 = B` 时进位。
    Single-segment increment: counts the segment, then either appends one true cell (done) or
    erases the whole segment (carry), with the two outcomes in distinct halting states. -/
def segInc (B : Nat) : DTM (B + 7) where
  step := fun s a =>
    if h : s.val < B + 1 then
      match a with
      | some true => (⟨s.val + 1, by omega⟩, a, Dir.right)
      | _ =>
          if h2 : s.val + 1 < B then (⟨B + 2, by omega⟩, some true, Dir.right)
          else (⟨B + 1, by omega⟩, a, Dir.left)
    else
      if h3 : s.val = B + 1 then
        if a = some true then (⟨B + 1, by omega⟩, none, Dir.left)
        else (⟨B + 3, by omega⟩, a, Dir.stay)
      else
        if h4 : s.val = B + 3 then
          match a with
          | none => (⟨B + 3, by omega⟩, a, Dir.left)
          | some true => (⟨B + 4, by omega⟩, a, Dir.left)
          | some false => (⟨B + 6, by omega⟩, a, Dir.stay)
        else
          if h5 : s.val = B + 4 then
            match a with
            | some true => (⟨B + 4, by omega⟩, a, Dir.left)
            | _ => ((0 : Fin (B + 7)), a, Dir.right)
          else (s, a, Dir.stay)
  start := 0
  accept := ⟨B + 2, by omega⟩
  reject := ⟨B + 6, by omega⟩

/-- 工作状态（≠ `B+2` 且 ≠ `B+6`）不停机。 Working states never halt. -/
theorem segInc_halted_false (B : Nat) (st : Nat) (hst : st < B + 7)
    (h2 : st ≠ B + 2) (h3 : st ≠ B + 6) (t : Tape) :
    (segInc B).halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (segInc B).accept.val = B + 2 from rfl] at hv
    exact h2 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (segInc B).reject.val = B + 6 from rfl] at hv
    exact h3 hv

/-- 计数步：读真格右移、状态加一（符号保留）。 Counting step over one true cell. -/
theorem segInc_count_true (B st : Nat) (hs : st < B + 7) (hlt : st < B + 1)
    (L R : List Sym) :
    (segInc B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 7)) (Tape.mk L (some true :: R))) =
      Config.mk (⟨st + 1, by omega⟩ : Fin (B + 7)) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_pos hlt]

/-- 决策步（未满）：读到非真格时新值仍小于 `B` ⇒ 追加一个真格、右移、进完成态。
    Decision (not full): append one true cell and enter the done state. -/
theorem segInc_decide_done (B st : Nat) (hs : st < B + 7) (hlt : st < B + 1)
    (hnew : st + 1 < B) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 7)) (Tape.mk L (a :: R))) =
      Config.mk (⟨B + 2, by omega⟩ : Fin (B + 7)) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  cases a with
  | none => rw [dif_pos hlt, dif_pos hnew]
  | some b =>
      cases b with
      | false => rw [dif_pos hlt, dif_pos hnew]
      | true => exact absurd rfl ha

/-- 决策步（将满）：新值达到 `B` ⇒ 左移进清零相位（回到段内最后一个真格上）。
    Decision (full): move left into the clearing phase. -/
theorem segInc_decide_carry (B st : Nat) (hs : st < B + 7) (hlt : st < B + 1)
    (hnew : ¬ st + 1 < B) (x : Sym) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).stepConfig
        (Config.mk (⟨st, hs⟩ : Fin (B + 7)) (Tape.mk (x :: L) (a :: R))) =
      Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7)) (Tape.mk L (x :: a :: R)) := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  cases a with
  | none => rw [dif_pos hlt, dif_neg hnew]
  | some b =>
      cases b with
      | false => rw [dif_pos hlt, dif_neg hnew]
      | true => exact absurd rfl ha

/-- 清零步：清零相位读真格 ⇒ 改写空白、左移。 Clearing step: erase one true cell leftward. -/
theorem segInc_erase_true (B : Nat) (x : Sym) (L R : List Sym) :
    (segInc B).stepConfig
        (Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7)) (Tape.mk (x :: L) (some true :: R))) =
      Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7)) (Tape.mk L (x :: none :: R)) := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_neg (by omega : ¬ B + 1 < B + 1)]
  split
  · rfl
  · next h => exact absurd trivial h

/-- 清零收尾：清零相位读非真格 ⇒ 进进位态停机。 Clearing finished: enter the carry state. -/
theorem segInc_erase_stop (B : Nat) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).stepConfig
        (Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7)) (Tape.mk L (a :: R))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_neg (by omega : ¬ B + 1 < B + 1)]
  split
  · rfl
  · next h => exact absurd trivial h

/-- 计数过程（带初值状态）：数过 `d` 个真格，状态 `j ↦ j + d`。 Counting walk with an initial state. -/
theorem segInc_count_aux (B : Nat) :
    ∀ (d j : Nat) (h1 : j < B + 7) (h2 : j + d < B + 7) (hj : j + d ≤ B)
      (L : List Sym) (a : Sym), a ≠ some true → ∀ (R : List Sym),
      (segInc B).run d
        ⟨(⟨j, h1⟩ : Fin (B + 7)), Tape.mk L (List.replicate d (some true) ++ a :: R)⟩ =
      ⟨(⟨j + d, h2⟩ : Fin (B + 7)),
        Tape.mk (List.replicate d (some true) ++ L) (a :: R)⟩ := by
  intro d
  induction d with
  | zero =>
      intro j h1 h2 hj L a ha R
      rw [List.replicate_zero, List.nil_append]
      rfl
  | succ d ih =>
      intro j h1 h2 hj L a ha R
      rw [show List.replicate (d + 1) (some true) ++ a :: R
            = some true :: (List.replicate d (some true) ++ a :: R) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted (segInc B) _ _
        (segInc_halted_false B j h1 (by omega) (by omega)
          (Tape.mk L (some true :: (List.replicate d (some true) ++ a :: R))))]
      rw [segInc_count_true B j h1 (by omega) L (List.replicate d (some true) ++ a :: R)]
      rw [ih (j + 1) (by omega) (by omega) (by omega) (some true :: L) a ha R]
      have hst : j + 1 + d = j + (d + 1) := by omega
      simp only [hst]
      rw [replicate_succ_append]

/-- 清零过程：从段尾真格起，`n + 1` 步把整段擦成空白，头停在段左侧的非真格上。
    Clearing walk: erase `n + 1` true cells leftward. -/
theorem segInc_erase_run (B : Nat) :
    ∀ (n : Nat) (a₀ : Sym), a₀ ≠ some true → ∀ (L : List Sym) (a : Sym), a ≠ some true →
      ∀ (R : List Sym),
      (segInc B).run (n + 1)
        ⟨(⟨B + 1, by omega⟩ : Fin (B + 7)),
          Tape.mk (List.replicate n (some true) ++ a₀ :: L) (some true :: a :: R)⟩ =
      ⟨(⟨B + 1, by omega⟩ : Fin (B + 7)),
        Tape.mk L (a₀ :: List.replicate (n + 1) none ++ a :: R)⟩ := by
  intro n
  induction n with
  | zero =>
      intro a₀ ha₀ L a ha R
      rw [List.replicate_zero, List.nil_append]
      rw [run_one_stp (segInc B)
        (Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7)) (Tape.mk (a₀ :: L) (some true :: a :: R)))
        (segInc_halted_false B (B + 1) (by omega) (by omega) (by omega) _)]
      rw [segInc_erase_true B a₀ L (a :: R)]
      rw [List.replicate_one]
      rfl
  | succ n ih =>
      intro a₀ ha₀ L a ha R
      rw [show List.replicate (n + 1) (some true) ++ a₀ :: L
            = some true :: (List.replicate n (some true) ++ a₀ :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted (segInc B) _ _
        (segInc_halted_false B (B + 1) (by omega) (by omega) (by omega)
          (Tape.mk (some true :: (List.replicate n (some true) ++ a₀ :: L)) (some true :: a :: R)))]
      rw [segInc_erase_true B (some true)
        (List.replicate n (some true) ++ a₀ :: L) (a :: R)]
      rw [ih a₀ ha₀ L none (by simp) (a :: R)]
      rw [List.cons_append]
      rw [replicate_succ_append (n + 1) none (a :: R)]
      rw [List.cons_append]

/-- **单段加一（完成）**：段长 `d` 且 `d + 1 < B` ⇒ `d + 1` 步后段长 `d ↦ d + 1`、进完成态。
    Segment increment (done): the run length goes `d ↦ d + 1`. -/
theorem segInc_run_done (B d : Nat) (hd : d + 1 < B) (L R : List Sym) :
    (segInc B).run (d + 1)
        ⟨(0 : Fin (B + 7)), Tape.mk L (List.replicate d (some true) ++ none :: R)⟩ =
      ⟨(⟨B + 2, by omega⟩ : Fin (B + 7)),
        Tape.mk (List.replicate (d + 1) (some true) ++ L) R⟩ := by
  have h1 : (0 : Nat) < B + 7 := by omega
  have h2 : (0 : Nat) + d < B + 7 := by omega
  rw [show (0 : Fin (B + 7)) = (⟨(0 : Nat), h1⟩ : Fin (B + 7)) from rfl]
  rw [DTM.run_add (segInc B) d 1]
  rw [segInc_count_aux B d 0 h1 h2 (by omega) L none (by simp) R]
  simp only [Nat.zero_add]
  rw [run_one_stp (segInc B)
    (Config.mk (⟨d, by omega⟩ : Fin (B + 7))
      (Tape.mk (List.replicate d (some true) ++ L) (none :: R)))
    (segInc_halted_false B d (by omega) (by omega) (by omega) _)]
  rw [segInc_decide_done B d (by omega) (by omega) hd none (by simp)
    (List.replicate d (some true) ++ L) R]
  rw [List.replicate_succ, List.cons_append]

/-- **单段加一（进位）**：段长 `k + 1` 且 `k + 2 = B` ⇒ 段满，`2k + 4` 步后整段清零、
    进进位态（头停在段左侧的非真格上）。Segment increment (carry): the full segment is erased. -/
theorem segInc_run_carry (B k : Nat) (hk : k + 2 = B) (a₀ : Sym) (ha₀ : a₀ ≠ some true)
    (L R : List Sym) :
    (segInc B).run (2 * k + 4)
        ⟨(0 : Fin (B + 7)),
          Tape.mk (a₀ :: L) (List.replicate (k + 1) (some true) ++ none :: R)⟩ =
      ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
        Tape.mk L (a₀ :: List.replicate (k + 1) none ++ none :: R)⟩ := by
  have h1 : (0 : Nat) < B + 7 := by omega
  have h2 : (0 : Nat) + (k + 1) < B + 7 := by omega
  -- 分四段：(k+1) 计数 + 1 决策 + (k+1) 清零 + 1 停机
  rw [show 2 * k + 4 = (k + 1) + (k + 3) from by omega]
  rw [DTM.run_add (segInc B) (k + 1) (k + 3)]
  rw [show (0 : Fin (B + 7)) = (⟨(0 : Nat), h1⟩ : Fin (B + 7)) from rfl]
  rw [segInc_count_aux B (k + 1) 0 h1 h2 (by omega) (a₀ :: L) none (by simp) R]
  simp only [Nat.zero_add]
  rw [show k + 3 = 1 + (k + 2) from by omega]
  rw [DTM.run_add (segInc B) 1 (k + 2)]
  -- 把计数终态的 `replicate (k+1)` 重述成「一格 + 余段」的写法（定义等价）
  show (segInc B).run (k + 2)
      ((segInc B).run 1 (Config.mk (⟨k + 1, by omega⟩ : Fin (B + 7))
        (Tape.mk ((some true :: List.replicate k (some true)) ++ a₀ :: L) (none :: R)))) =
    ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
      Tape.mk L (a₀ :: List.replicate (k + 1) none ++ none :: R)⟩
  rw [run_one_stp (segInc B)
    (Config.mk (⟨k + 1, by omega⟩ : Fin (B + 7))
      (Tape.mk ((some true :: List.replicate k (some true)) ++ a₀ :: L) (none :: R)))
    (segInc_halted_false B (k + 1) (by omega) (by omega) (by omega) _)]
  have hstep : (segInc B).stepConfig
      (Config.mk (⟨k + 1, by omega⟩ : Fin (B + 7))
        (Tape.mk ((some true :: List.replicate k (some true)) ++ a₀ :: L) (none :: R))) =
      Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7))
        (Tape.mk (List.replicate k (some true) ++ a₀ :: L) (some true :: none :: R)) :=
    segInc_decide_carry B (k + 1) (by omega) (by omega) (by omega)
      (some true) none (by simp) (List.replicate k (some true) ++ a₀ :: L) R
  rw [hstep]
  rw [show k + 2 = (k + 1) + 1 from by omega]
  rw [DTM.run_add (segInc B) (k + 1) 1]
  rw [segInc_erase_run B k a₀ ha₀ L none (by simp) R]
  rw [run_one_stp (segInc B)
    (Config.mk (⟨B + 1, by omega⟩ : Fin (B + 7))
      (Tape.mk L (a₀ :: List.replicate (k + 1) none ++ none :: R)))
    (segInc_halted_false B (B + 1) (by omega) (by omega) (by omega) _)]
  rw [List.cons_append]
  rw [segInc_erase_stop B a₀ ha₀ L (List.replicate (k + 1) none ++ none :: R)]

/-! ### 段间走位：从已擦除段的左侧空白走到下一段的最左真格 -/

/-- **走到下一段**：状态 0 左移跳过空白垫，遇真格转状态 1 继续左移跳过整段真格，
    最后右移一格停在下一段最左真格上（接受态 2）；若先碰到标志格 `some false`，
    则进拒绝态 3（计数器溢出到顶）。
    Walk to the next segment: skip blank pads and the next true run, then step right onto the
    run's leftmost cell (accept 2); a `some false` marker halts in the reject state 3. -/
def nextSeg : DTM 4 where
  step := fun s a =>
    if s.val = 0 then
      match a with
      | none => ((0 : Fin 4), a, Dir.left)
      | some true => ((1 : Fin 4), a, Dir.left)
      | some false => ((3 : Fin 4), a, Dir.stay)
    else if s.val = 1 then
      match a with
      | some true => ((1 : Fin 4), a, Dir.left)
      | _ => ((2 : Fin 4), a, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 3

/-- 工作状态（0/1）不停机。 Working states never halt. -/
theorem nextSeg_halted_false (st : Nat) (hst : st < 4) (h2 : st ≠ 2) (h3 : st ≠ 3)
    (t : Tape) : nextSeg.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show nextSeg.accept.val = 2 from rfl] at hv
    exact h2 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show nextSeg.reject.val = 3 from rfl] at hv
    exact h3 hv

/-- 状态 0 读到空白：左移一格。 Blank in state 0: move left. -/
theorem nextSeg_step_blank (x : Sym) (L R : List Sym) :
    nextSeg.stepConfig ⟨(0 : Fin 4), Tape.mk (x :: L) (none :: R)⟩ =
      ⟨(0 : Fin 4), Tape.mk L (x :: none :: R)⟩ := by
  simp only [DTM.stepConfig, nextSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rfl

/-- 状态 0 读到真格：转状态 1 并左移。 True in state 0: go to state 1 and move left. -/
theorem nextSeg_step_true0 (x : Sym) (L R : List Sym) :
    nextSeg.stepConfig ⟨(0 : Fin 4), Tape.mk (x :: L) (some true :: R)⟩ =
      ⟨(1 : Fin 4), Tape.mk L (x :: some true :: R)⟩ := by
  simp only [DTM.stepConfig, nextSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rfl

/-- 状态 0 读到标志格 `some false`：进拒绝态停机（溢出）。 Flag: halt in the reject state. -/
theorem nextSeg_step_flag (L R : List Sym) :
    nextSeg.stepConfig ⟨(0 : Fin 4), Tape.mk L (some false :: R)⟩ =
      ⟨(3 : Fin 4), Tape.mk L (some false :: R)⟩ := by
  simp only [DTM.stepConfig, nextSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rfl

/-- 状态 1 读到真格：左移一格。 True in state 1: move left. -/
theorem nextSeg_step_true1 (x : Sym) (L R : List Sym) :
    nextSeg.stepConfig ⟨(1 : Fin 4), Tape.mk (x :: L) (some true :: R)⟩ =
      ⟨(1 : Fin 4), Tape.mk L (x :: some true :: R)⟩ := by
  simp only [DTM.stepConfig, nextSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rfl

/-- 状态 1 读到非真格：右移一格并接受（落到该段最左真格上）。 Non-true in state 1: step
    right onto the run's leftmost cell and accept. -/
theorem nextSeg_stop (L R : List Sym) (a : Sym) (ha : a ≠ some true) :
    nextSeg.stepConfig ⟨(1 : Fin 4), Tape.mk L (a :: R)⟩ =
      ⟨(2 : Fin 4), Tape.mk (a :: L) R⟩ := by
  cases a with
  | none =>
      simp only [DTM.stepConfig, nextSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight, List.headD, List.tail]
      rfl
  | some b =>
      cases b with
      | false =>
          simp only [DTM.stepConfig, nextSeg, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, Tape.moveRight, List.headD, List.tail]
          rfl
      | true => exact absurd rfl ha

/-- 跳过 `p` 个空白垫（`p + 1` 步，含入口那一个空白）。 Skip `p` blank pads. -/
theorem nextSeg_pads (p : Nat) :
    ∀ (L R : List Sym) (a : Sym),
      nextSeg.run (p + 1)
        ⟨(0 : Fin 4), Tape.mk (List.replicate p none ++ a :: L) (none :: R)⟩ =
      ⟨(0 : Fin 4), Tape.mk L (a :: List.replicate p none ++ none :: R)⟩ := by
  induction p with
  | zero =>
      intro L R a
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp nextSeg (Config.mk (0 : Fin 4) (Tape.mk (a :: L) (none :: R)))
        (nextSeg_halted_false 0 (by omega) (by omega) (by omega) _)]
      rw [nextSeg_step_blank a L R]
      rw [List.singleton_append]
  | succ p ih =>
      intro L R a
      rw [show List.replicate (p + 1) none ++ a :: L
          = none :: (List.replicate p none ++ a :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show p + 1 + 1 = 1 + (p + 1) from by omega]
      rw [DTM.run_add nextSeg 1 (p + 1)]
      rw [run_one_stp nextSeg
        (Config.mk (0 : Fin 4)
          (Tape.mk (none :: (List.replicate p none ++ a :: L)) (none :: R)))
        (nextSeg_halted_false 0 (by omega) (by omega) (by omega) _)]
      rw [nextSeg_step_blank none (List.replicate p none ++ a :: L) R]
      rw [ih L (none :: R) a]
      rw [List.cons_append]
      rw [replicate_succ_append p none (none :: R)]
      rw [List.cons_append]

/-- 状态 1 跳过 `e + 1` 个真格（含当前格），停在左侧非真格上。
    State 1 walks left over `e + 1` true cells. -/
theorem nextSeg_trues1 (e : Nat) :
    ∀ (L R : List Sym) (a : Sym), a ≠ some true →
      nextSeg.run (e + 1)
        ⟨(1 : Fin 4), Tape.mk (List.replicate e (some true) ++ a :: L) (some true :: R)⟩ =
      ⟨(1 : Fin 4), Tape.mk L (a :: List.replicate (e + 1) (some true) ++ R)⟩ := by
  induction e with
  | zero =>
      intro L R a ha
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp nextSeg (Config.mk (1 : Fin 4) (Tape.mk (a :: L) (some true :: R)))
        (nextSeg_halted_false 1 (by omega) (by omega) (by omega) _)]
      rw [nextSeg_step_true1 a L R]
      rw [List.replicate_one]
      rw [List.cons_append, List.singleton_append]
  | succ e ih =>
      intro L R a ha
      rw [show List.replicate (e + 1) (some true) ++ a :: L
          = some true :: (List.replicate e (some true) ++ a :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show e + 1 + 1 = 1 + (e + 1) from by omega]
      rw [DTM.run_add nextSeg 1 (e + 1)]
      rw [run_one_stp nextSeg
        (Config.mk (1 : Fin 4)
          (Tape.mk (some true :: (List.replicate e (some true) ++ a :: L))
            (some true :: R)))
        (nextSeg_halted_false 1 (by omega) (by omega) (by omega) _)]
      rw [nextSeg_step_true1 (some true) (List.replicate e (some true) ++ a :: L) R]
      rw [ih L (some true :: R) a ha]
      rw [List.cons_append]
      rw [show 1 + (e + 1) = (e + 1) + 1 from by omega]
      rw [replicate_succ_append (e + 1) (some true) R]
      rw [List.cons_append]

/-- 状态 0 跳过 `k + 2` 个真格（含当前格与 `k + 1` 个左邻格）。
    State 0 walks left over a run of `k + 2` true cells. -/
theorem nextSeg_trues0 (k : Nat) :
    ∀ (L R : List Sym) (a : Sym), a ≠ some true →
      nextSeg.run (k + 2)
        ⟨(0 : Fin 4),
          Tape.mk (List.replicate (k + 1) (some true) ++ a :: L) (some true :: R)⟩ =
      ⟨(1 : Fin 4), Tape.mk L (a :: List.replicate (k + 2) (some true) ++ R)⟩ := by
  intro L R a ha
  rw [show List.replicate (k + 1) (some true) ++ a :: L
      = some true :: (List.replicate k (some true) ++ a :: L) from by
    rw [List.replicate_succ, List.cons_append]]
  rw [show k + 2 = 1 + (k + 1) from by omega]
  rw [DTM.run_add nextSeg 1 (k + 1)]
  rw [run_one_stp nextSeg
    (Config.mk (0 : Fin 4)
      (Tape.mk (some true :: (List.replicate k (some true) ++ a :: L)) (some true :: R)))
    (nextSeg_halted_false 0 (by omega) (by omega) (by omega) _)]
  rw [nextSeg_step_true0 (some true) (List.replicate k (some true) ++ a :: L) R]
  rw [nextSeg_trues1 k L (some true :: R) a ha]
  rw [List.cons_append]
  rw [show 1 + (k + 1) = (k + 1) + 1 from by omega]
  rw [replicate_succ_append (k + 1) (some true) R]
  rw [List.cons_append]

/-- **走到下一段（整段）**：从已擦除段的左侧空白起，跳过 `p` 个空白垫、再跳过长度 `k + 2`
    的真格串，`p + k + 4` 步后头停在下一段最左真格上并接受。
    Full next-segment walk: `p + k + 4` steps land on the next run's leftmost cell. -/
theorem nextSeg_run (p k : Nat) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    nextSeg.run (p + k + 4)
        ⟨(0 : Fin 4),
          Tape.mk (List.replicate p none ++ List.replicate (k + 2) (some true) ++ a :: L)
            (none :: R)⟩ =
      ⟨(2 : Fin 4),
        Tape.mk (a :: L)
          (List.replicate (k + 2) (some true) ++ List.replicate p none ++ none :: R)⟩ := by
  rw [show List.replicate (k + 2) (some true)
      = some true :: List.replicate (k + 1) (some true) from by
    rw [List.replicate_succ]]
  rw [show (List.replicate p none
        ++ (some true :: List.replicate (k + 1) (some true))) ++ (a :: L)
      = List.replicate p none
        ++ some true :: (List.replicate (k + 1) (some true) ++ a :: L) from by
    rw [List.append_assoc, List.cons_append]]
  rw [show p + k + 4 = (p + 1) + ((k + 2) + 1) from by omega]
  rw [DTM.run_add nextSeg (p + 1) ((k + 2) + 1)]
  rw [nextSeg_pads p (List.replicate (k + 1) (some true) ++ a :: L) R (some true)]
  rw [DTM.run_add nextSeg (k + 2) 1]
  rw [show (some true :: List.replicate p none) ++ (none :: R)
      = some true :: (List.replicate p none ++ none :: R) from by
    rw [List.cons_append]]
  rw [nextSeg_trues0 k L (List.replicate p none ++ none :: R) a ha]
  rw [run_one_stp nextSeg
    (Config.mk (1 : Fin 4)
      (Tape.mk L (a :: List.replicate (k + 2) (some true)
        ++ (List.replicate p none ++ none :: R))))
    (nextSeg_halted_false 1 (by omega) (by omega) (by omega) _)]
  rw [show (a :: List.replicate (k + 2) (some true)) ++ (List.replicate p none ++ none :: R)
      = a :: (List.replicate (k + 2) (some true)
        ++ (List.replicate p none ++ none :: R)) from by
    rw [List.cons_append]]
  rw [nextSeg_stop L (List.replicate (k + 2) (some true)
    ++ (List.replicate p none ++ none :: R)) a ha]
  simp only [List.replicate_succ, List.cons_append, List.append_assoc]

/-! ### 进位链：segInc 的清零相位之后续走位与逐段进位 -/

/-- 进位链左侧的 `r` 个满段：每层 `p + 1` 个空白垫 + `B - 1` 个真格。
    `r` full layers on the left of the carry chain (`p+1` pads + `B-1` trues each). -/
def chainL (p B : Nat) : Nat → List Sym
  | 0 => []
  | r + 1 => List.replicate (p + 1) none ++ List.replicate (B - 1) (some true) ++ chainL p B r

/-- 进位链走过 `r` 段后在右侧积累的空白：每轮前置 `p` 个垫格、`B-1` 个擦除格与 1 个尾格。
    Blanks accumulated on the right after `r` carried segments. -/
def chainJunk (p B : Nat) : Nat → List Sym → List Sym
  | 0, J => J
  | r + 1, J => List.replicate p none ++ List.replicate (B - 1) none ++ none :: chainJunk p B r J

/-- 空白记账的前移一步：`r` 轮记账再前置一块 = `r + 1` 轮记账。
    Prepending one block to the `r`-round ledger equals the `(r+1)`-round ledger. -/
theorem chainJunk_shift (p B r : Nat) (J : List Sym) :
    chainJunk p B r (List.replicate p none ++ List.replicate (B - 1) none ++ none :: J)
      = chainJunk p B (r + 1) J := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [chainJunk, ih]
      rw [show chainJunk p B (r + 1 + 1) J
          = List.replicate p none ++ List.replicate (B - 1) none
            ++ none :: chainJunk p B (r + 1) J from rfl]

/-- 左带 `chainL r ++ M` 的首格是空白（`M` 的首格为空白时）。 -/
theorem chainL_head_none (p B r : Nat) (M : List Sym) (hM : M.head? = some none) :
    (chainL p B r ++ M).head? = some none := by
  induction r with
  | zero => exact hM
  | succ r ih =>
      rw [show chainL p B (r + 1) ++ M
          = none :: (List.replicate p none ++ List.replicate (B - 1) (some true)
            ++ chainL p B r ++ M) from by
        simp only [chainL, List.replicate_succ, List.cons_append, List.append_assoc]]
      rfl

/-! ### 进位链：segInc 的清零相位之后续走位与逐段进位 -/

/-- 走位相位（`B+3`）读到空白：左移一格。 Walk phase on a blank: move left. -/
theorem segInc_walk_blank (B : Nat) (x : Sym) (L R : List Sym) :
    (segInc B).stepConfig
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)), Tape.mk (x :: L) (none :: R)⟩ =
      ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)), Tape.mk L (x :: none :: R)⟩ := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (exfalso; simp_all)

/-- 走位相位读到真格：进 `B+4` 并左移。 Walk phase on a true cell: enter `B+4`, move left. -/
theorem segInc_walk_true0 (B : Nat) (x : Sym) (L R : List Sym) :
    (segInc B).stepConfig
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)), Tape.mk (x :: L) (some true :: R)⟩ =
      ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)), Tape.mk L (x :: some true :: R)⟩ := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (exfalso; simp_all)

/-- 走位相位读到标志格 `some false`：进溢出拒绝态。 Walk phase on the flag: overflow. -/
theorem segInc_walk_flag (B : Nat) (L R : List Sym) :
    (segInc B).stepConfig
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)), Tape.mk L (some false :: R)⟩ =
      ⟨(⟨B + 6, by omega⟩ : Fin (B + 7)), Tape.mk L (some false :: R)⟩ := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (exfalso; simp_all)

/-- 走位相位 `B+4` 读到真格：左移一格。 Walk phase `B+4` on a true cell: move left. -/
theorem segInc_walk_true1 (B : Nat) (x : Sym) (L R : List Sym) :
    (segInc B).stepConfig
        ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)), Tape.mk (x :: L) (some true :: R)⟩ =
      ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)), Tape.mk L (x :: some true :: R)⟩ := by
  simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (exfalso; simp_all)

/-- 走位相位 `B+4` 读到非真格：右移一格并**重启**（回到计数相位 0）。
    Walk phase `B+4` on a non-true cell: step right and restart at state 0. -/
theorem segInc_walk_stop (B : Nat) (L R : List Sym) (a : Sym) (ha : a ≠ some true) :
    (segInc B).stepConfig
        ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)), Tape.mk L (a :: R)⟩ =
      ⟨(0 : Fin (B + 7)), Tape.mk (a :: L) R⟩ := by
  cases a with
  | none =>
      simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight, List.headD, List.tail]
      repeat' split
      all_goals first | rfl | (exfalso; omega) | (exfalso; simp_all)
  | some b =>
      cases b with
      | false =>
          simp only [DTM.stepConfig, segInc, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, Tape.moveRight, List.headD, List.tail]
          repeat' split
          all_goals first | rfl | (exfalso; omega) | (exfalso; simp_all)
      | true => exact absurd rfl ha

/-- 走位相位跳过 `p` 个空白垫（`p + 1` 步）。 Walk phase over `p` blank pads. -/
theorem segInc_walk_pads (B p : Nat) :
    ∀ (L R : List Sym) (a : Sym),
      (segInc B).run (p + 1)
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
          Tape.mk (List.replicate p none ++ a :: L) (none :: R)⟩ =
      ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
        Tape.mk L (a :: List.replicate p none ++ none :: R)⟩ := by
  induction p with
  | zero =>
      intro L R a
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp (segInc B)
        (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: L) (none :: R)))
        (segInc_halted_false B (B + 3) (by omega) (by omega) (by omega) _)]
      rw [segInc_walk_blank B a L R]
      rw [List.singleton_append]
  | succ p ih =>
      intro L R a
      rw [show List.replicate (p + 1) none ++ a :: L
          = none :: (List.replicate p none ++ a :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show p + 1 + 1 = 1 + (p + 1) from by omega]
      rw [DTM.run_add (segInc B) 1 (p + 1)]
      rw [run_one_stp (segInc B)
        (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
          (Tape.mk (none :: (List.replicate p none ++ a :: L)) (none :: R)))
        (segInc_halted_false B (B + 3) (by omega) (by omega) (by omega) _)]
      rw [segInc_walk_blank B none (List.replicate p none ++ a :: L) R]
      rw [ih L (none :: R) a]
      rw [List.cons_append]
      rw [replicate_succ_append p none (none :: R)]
      rw [List.cons_append]

/-- 走位相位 `B+4` 跳过 `e + 1` 个真格。 Walk phase `B+4` over `e + 1` true cells. -/
theorem segInc_walk_trues1 (B e : Nat) :
    ∀ (L R : List Sym) (a : Sym), a ≠ some true →
      (segInc B).run (e + 1)
        ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)),
          Tape.mk (List.replicate e (some true) ++ a :: L) (some true :: R)⟩ =
      ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)),
        Tape.mk L (a :: List.replicate (e + 1) (some true) ++ R)⟩ := by
  induction e with
  | zero =>
      intro L R a ha
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp (segInc B)
        (Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: L) (some true :: R)))
        (segInc_halted_false B (B + 4) (by omega) (by omega) (by omega) _)]
      rw [segInc_walk_true1 B a L R]
      rw [List.replicate_one]
      rw [List.cons_append, List.singleton_append]
  | succ e ih =>
      intro L R a ha
      rw [show List.replicate (e + 1) (some true) ++ a :: L
          = some true :: (List.replicate e (some true) ++ a :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show e + 1 + 1 = 1 + (e + 1) from by omega]
      rw [DTM.run_add (segInc B) 1 (e + 1)]
      rw [run_one_stp (segInc B)
        (Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
          (Tape.mk (some true :: (List.replicate e (some true) ++ a :: L))
            (some true :: R)))
        (segInc_halted_false B (B + 4) (by omega) (by omega) (by omega) _)]
      rw [segInc_walk_true1 B (some true) (List.replicate e (some true) ++ a :: L) R]
      rw [ih L (some true :: R) a ha]
      rw [List.cons_append]
      rw [show 1 + (e + 1) = (e + 1) + 1 from by omega]
      rw [replicate_succ_append (e + 1) (some true) R]
      rw [List.cons_append]

/-- 走位相位 `B+3` 跳过 `k + 2` 个真格。 Walk phase `B+3` over `k + 2` true cells. -/
theorem segInc_walk_trues0 (B k : Nat) :
    ∀ (L R : List Sym) (a : Sym), a ≠ some true →
      (segInc B).run (k + 2)
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
          Tape.mk (List.replicate (k + 1) (some true) ++ a :: L) (some true :: R)⟩ =
      ⟨(⟨B + 4, by omega⟩ : Fin (B + 7)),
        Tape.mk L (a :: List.replicate (k + 2) (some true) ++ R)⟩ := by
  intro L R a ha
  rw [show List.replicate (k + 1) (some true) ++ a :: L
      = some true :: (List.replicate k (some true) ++ a :: L) from by
    rw [List.replicate_succ, List.cons_append]]
  rw [show k + 2 = 1 + (k + 1) from by omega]
  rw [DTM.run_add (segInc B) 1 (k + 1)]
  rw [run_one_stp (segInc B)
    (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
      (Tape.mk (some true :: (List.replicate k (some true) ++ a :: L)) (some true :: R)))
    (segInc_halted_false B (B + 3) (by omega) (by omega) (by omega) _)]
  rw [segInc_walk_true0 B (some true) (List.replicate k (some true) ++ a :: L) R]
  rw [segInc_walk_trues1 B k L (some true :: R) a ha]
  rw [List.cons_append]
  rw [show 1 + (k + 1) = (k + 1) + 1 from by omega]
  rw [replicate_succ_append (k + 1) (some true) R]
  rw [List.cons_append]

/-- **走位整段**：跳过 `p` 个空白垫与长度 `k + 2` 的真格，`p + k + 4` 步后重启（状态 0）
    在下一段最左真格上。 Full walk: `p + k + 4` steps restart at the next run's leftmost cell. -/
theorem segInc_walk_run (B p k : Nat) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).run (p + k + 4)
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
          Tape.mk (List.replicate p none ++ List.replicate (k + 2) (some true) ++ a :: L)
            (none :: R)⟩ =
      ⟨(0 : Fin (B + 7)),
        Tape.mk (a :: L)
          (List.replicate (k + 2) (some true) ++ List.replicate p none ++ none :: R)⟩ := by
  rw [show List.replicate (k + 2) (some true)
      = some true :: List.replicate (k + 1) (some true) from by
    rw [List.replicate_succ]]
  rw [show (List.replicate p none
        ++ (some true :: List.replicate (k + 1) (some true))) ++ (a :: L)
      = List.replicate p none
        ++ some true :: (List.replicate (k + 1) (some true) ++ a :: L) from by
    rw [List.append_assoc, List.cons_append]]
  rw [show p + k + 4 = (p + 1) + ((k + 2) + 1) from by omega]
  rw [DTM.run_add (segInc B) (p + 1) ((k + 2) + 1)]
  rw [segInc_walk_pads B p (List.replicate (k + 1) (some true) ++ a :: L) R (some true)]
  rw [DTM.run_add (segInc B) (k + 2) 1]
  rw [show (some true :: List.replicate p none) ++ (none :: R)
      = some true :: (List.replicate p none ++ none :: R) from by
    rw [List.cons_append]]
  rw [segInc_walk_trues0 B k L (List.replicate p none ++ none :: R) a ha]
  rw [run_one_stp (segInc B)
    (Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
      (Tape.mk L (a :: List.replicate (k + 2) (some true)
        ++ (List.replicate p none ++ none :: R))))
    (segInc_halted_false B (B + 4) (by omega) (by omega) (by omega) _)]
  rw [show (a :: List.replicate (k + 2) (some true)) ++ (List.replicate p none ++ none :: R)
      = a :: (List.replicate (k + 2) (some true)
        ++ (List.replicate p none ++ none :: R)) from by
    rw [List.cons_append]]
  rw [segInc_walk_stop B L (List.replicate (k + 2) (some true)
    ++ (List.replicate p none ++ none :: R)) a ha]
  simp only [List.replicate_succ, List.cons_append, List.append_assoc]

/-- **进位链的一轮**：当前满段（`B - 1` 个真格）整段擦除后，向左跳过 `p` 个空白垫与
    一段 `d` 个真格，重启在下一段左端（状态 0）；成本 `2B + p + d + 2`。
    One carry round: erase the current full segment, walk left over `p` pads and a run of
    `d` trues, and restart state 0 at the next segment's left end. -/
theorem segInc_roundC (B p d : Nat) (hB : 3 ≤ B) (hp : 1 ≤ p) (hd : 2 ≤ d)
    (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).run (2 * B + p + d + 2)
        ⟨(0 : Fin (B + 7)),
          Tape.mk (List.replicate (p + 1) none ++ List.replicate d (some true) ++ a :: L)
            (List.replicate (B - 1) (some true) ++ none :: R)⟩ =
      ⟨(0 : Fin (B + 7)),
        Tape.mk (a :: L)
          (List.replicate d (some true) ++ List.replicate (p + 1) none
            ++ List.replicate (B - 1) none ++ none :: R)⟩ := by
  -- 入口左带拆成一格 + 余段（配合进位段 `a₀ :: L` 的形态）
  rw [show List.replicate (p + 1) none ++ List.replicate d (some true) ++ a :: L
      = none :: (List.replicate p none ++ List.replicate d (some true) ++ a :: L) from by
    simp only [List.replicate_succ, List.cons_append, List.append_assoc]]
  -- 进位段：参数 `k₁ = B - 2`
  rw [show List.replicate (B - 1) (some true) = List.replicate ((B - 2) + 1) (some true) from by
    rw [show (B - 2) + 1 = B - 1 from by omega]]
  rw [show 2 * B + p + d + 2 = (2 * (B - 2) + 4) + (p + (d - 2) + 4) from by omega]
  rw [DTM.run_add (segInc B) (2 * (B - 2) + 4) (p + (d - 2) + 4)]
  rw [segInc_run_carry B (B - 2) (by omega) none (by simp)
    (List.replicate p none ++ List.replicate d (some true) ++ a :: L) R]
  -- 走位段：参数 `k₂ = d - 2`
  rw [show List.replicate (B - 2 + 1) none = List.replicate (B - 1) none from by
    rw [show (B - 2) + 1 = B - 1 from by omega]]
  rw [show List.replicate d (some true) = List.replicate ((d - 2) + 2) (some true) from by
    rw [show (d - 2) + 2 = d from by omega]]
  rw [show (none :: List.replicate (B - 1) none) ++ none :: R
      = none :: (List.replicate (B - 1) none ++ none :: R) from List.cons_append]
  rw [segInc_walk_run B p (d - 2) a ha L (List.replicate (B - 1) none ++ none :: R)]
  rw [show List.replicate ((d - 2) + 2) (some true) = List.replicate d (some true) from by
    rw [show (d - 2) + 2 = d from by omega]]
  simp only [replicate_succ_append, List.append_assoc]

/-- **进位链的 `r` 轮**：左侧 `r` 个满段逐轮擦除，`r` 轮后头回到状态 0、停在剩余左带
    首格，右侧积累 `r` 轮空白记账。成本 `r * (3B + p + 1)`。
    `r` carry rounds peel `r` full layers at cost `r * (3B + p + 1)`. -/
theorem segInc_carryIter (B p r : Nat) (hB : 3 ≤ B) (hp : 1 ≤ p) :
    ∀ (M : List Sym) (hM : M.head? = some none) (J : List Sym),
      (segInc B).run (r * (3 * B + p + 1))
          ⟨(0 : Fin (B + 7)),
            Tape.mk (chainL p B r ++ M) (List.replicate (B - 1) (some true) ++ none :: J)⟩ =
        ⟨(0 : Fin (B + 7)),
          Tape.mk M (List.replicate (B - 1) (some true) ++ none :: chainJunk p B r J)⟩ := by
  induction r with
  | zero =>
      intro M hM J
      simp only [chainL, chainJunk, Nat.zero_mul, List.nil_append]
      rfl
  | succ r ih =>
      intro M hM J
      have hhead : (chainL p B r ++ M).head? = some none := chainL_head_none p B r M hM
      obtain ⟨M', hM'⟩ : ∃ M', chainL p B r ++ M = none :: M' := by
        cases h : chainL p B r ++ M with
        | nil => rw [h] at hhead; simp at hhead
        | cons a t =>
            rw [h] at hhead
            simp only [List.head?_cons, Option.some.injEq] at hhead
            exact ⟨t, by rw [hhead]⟩
      rw [show chainL p B (r + 1) ++ M
          = List.replicate (p + 1) none ++ List.replicate (B - 1) (some true)
            ++ (chainL p B r ++ M) from by
        simp only [chainL, List.append_assoc]]
      rw [hM']
      rw [show (r + 1) * (3 * B + p + 1)
          = (3 * B + p + 1) + r * (3 * B + p + 1) from by
        rw [Nat.succ_mul, Nat.add_comm]]
      have hrun : ∀ k : Nat, (segInc B).run (3 * B + p + 1 + k)
          = (segInc B).run (2 * B + p + (B - 1) + 2 + k) := by
        intro k
        rw [show 3 * B + p + 1 = 2 * B + p + (B - 1) + 2 from by omega]
      rw [hrun (r * (3 * B + p + 1))]
      rw [DTM.run_add (segInc B) (2 * B + p + (B - 1) + 2) (r * (3 * B + p + 1))]
      rw [segInc_roundC B p (B - 1) hB hp (by omega) none (by simp) M' J]
      -- 右带整理成「真格串 + 一格空白 + 记账」的形态，接归纳假设
      rw [show List.replicate (B - 1) (some true) ++ List.replicate (p + 1) none
            ++ List.replicate (B - 1) none ++ none :: J
          = List.replicate (B - 1) (some true) ++ none
            :: (List.replicate p none ++ List.replicate (B - 1) none ++ none :: J) from by
        simp only [List.replicate_succ, List.cons_append, List.append_assoc]]
      rw [← hM']
      rw [ih M hM (List.replicate p none ++ List.replicate (B - 1) none ++ none :: J)]
      rw [chainJunk_shift]

/-- **进位链整条（满段进位 + 末段加一）**：`r` 个满段逐轮擦除、进位落到 `d` 格段上，
    末段加一后停机于接受态；`r = 0` 即「直接加一」。
    The full carry chain: peel `r` full segments, then increment a `d`-cell segment. -/
theorem segInc_carryChain (B p d r : Nat) (hB : 3 ≤ B) (hp : 1 ≤ p) (hd : 2 ≤ d)
    (hdB : d + 1 < B) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).run (r * (3 * B + p + 1) + (2 * B + p + d + 2) + (d + 1))
        ⟨(0 : Fin (B + 7)),
          Tape.mk (chainL p B r ++ List.replicate (p + 1) none
            ++ List.replicate d (some true) ++ a :: L)
            (List.replicate (B - 1) (some true) ++ none :: R)⟩ =
      ⟨(⟨B + 2, by omega⟩ : Fin (B + 7)),
        Tape.mk (List.replicate (d + 1) (some true) ++ a :: L)
          (List.replicate p none ++ List.replicate (B - 1) none
            ++ none :: chainJunk p B r R)⟩ := by
  rw [show r * (3 * B + p + 1) + (2 * B + p + d + 2) + (d + 1)
      = (r * (3 * B + p + 1) + (2 * B + p + d + 2)) + (d + 1) from rfl]
  rw [DTM.run_add (segInc B) (r * (3 * B + p + 1) + (2 * B + p + d + 2)) (d + 1)]
  rw [DTM.run_add (segInc B) (r * (3 * B + p + 1)) (2 * B + p + d + 2)]
  rw [show chainL p B r ++ List.replicate (p + 1) none ++ List.replicate d (some true)
        ++ a :: L
      = chainL p B r ++ (List.replicate (p + 1) none ++ List.replicate d (some true)
        ++ a :: L) from by
    simp only [List.append_assoc]]
  have hM : (List.replicate (p + 1) none ++ List.replicate d (some true) ++ a :: L).head?
      = some none := by
    rw [show List.replicate (p + 1) none = none :: List.replicate p none from by
      rw [List.replicate_succ]]
    simp only [List.cons_append, List.head?_cons]
  rw [segInc_carryIter B p r hB hp
    (List.replicate (p + 1) none ++ List.replicate d (some true) ++ a :: L) hM R]
  rw [segInc_roundC B p d hB hp hd a ha L (chainJunk p B r R)]
  rw [show List.replicate d (some true) ++ List.replicate (p + 1) none
        ++ List.replicate (B - 1) none ++ none :: chainJunk p B r R
      = List.replicate d (some true) ++ none
        :: (List.replicate p none ++ List.replicate (B - 1) none
          ++ none :: chainJunk p B r R) from by
    simp only [List.replicate_succ, List.cons_append, List.append_assoc]]
  rw [segInc_run_done B d hdB (a :: L)
    (List.replicate p none ++ List.replicate (B - 1) none ++ none :: chainJunk p B r R)]

/-- **走位整段（任意长度）**：跳过 `p` 个空白垫与 **任意长度 `q ≥ 1`** 的真格串，
    `p + q + 2` 步后重启（状态 0）在下一段最左真格上。
    Full walk over a run of any length `q ≥ 1` (`p + q + 2` steps). -/
theorem segInc_walk_any (B p q : Nat) (hq : 1 ≤ q) (a : Sym) (ha : a ≠ some true)
    (L R : List Sym) :
    (segInc B).run (p + q + 2)
        ⟨(⟨B + 3, by omega⟩ : Fin (B + 7)),
          Tape.mk (List.replicate p none ++ List.replicate q (some true) ++ a :: L)
            (none :: R)⟩ =
      ⟨(0 : Fin (B + 7)),
        Tape.mk (a :: L) (List.replicate q (some true) ++ List.replicate p none
          ++ none :: R)⟩ := by
  cases q with
  | zero => omega
  | succ q1 =>
      cases q1 with
      | zero =>
          -- `q = 1`：垫 → 读真格进 `B+4` → 非真格右移重启
          rw [show List.replicate 1 (some true) = some true :: [] from List.replicate_one]
          rw [List.append_assoc]
          rw [List.singleton_append]
          rw [show p + (0 + 1) + 2 = (p + 1) + (1 + 1) from by omega]
          rw [DTM.run_add (segInc B) (p + 1) 2]
          rw [segInc_walk_pads B p (a :: L) R (some true)]
          rw [show (some true :: List.replicate p none) ++ none :: R
              = some true :: (List.replicate p none ++ none :: R) from List.cons_append]
          rw [DTM.run_add (segInc B) 1 1]
          rw [run_one_stp (segInc B)
            (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
              (Tape.mk (a :: L) (some true :: (List.replicate p none ++ none :: R))))
            (segInc_halted_false B (B + 3) (by omega) (by omega) (by omega) _)]
          rw [segInc_walk_true0 B a L (List.replicate p none ++ none :: R)]
          rw [run_one_stp (segInc B)
            (Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
              (Tape.mk L (a :: some true :: (List.replicate p none ++ none :: R))))
            (segInc_halted_false B (B + 4) (by omega) (by omega) (by omega) _)]
          rw [segInc_walk_stop B L (some true :: (List.replicate p none ++ none :: R)) a ha]
          simp only [List.singleton_append, List.cons_append, List.nil_append]
      | succ q2 =>
          -- `q = q2 + 2`：直接复用 `segInc_walk_run`
          rw [show p + (q2 + 1 + 1) + 2 = p + q2 + 4 from by omega]
          rw [segInc_walk_run B p q2 a ha L R]

/-- **进位链的一轮（任意段长）**：当前满段擦除后，向左跳过 `p` 个空白垫与任意长度
    `q ≥ 1` 的真格段，重启状态 0 于下一段左端；成本 `2B + p + q + 2`。
    One carry round with a walked segment of any length `q ≥ 1`. -/
theorem segInc_roundC_any (B p q : Nat) (hB : 3 ≤ B) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).run (2 * B + p + q + 2)
        ⟨(0 : Fin (B + 7)),
          Tape.mk (List.replicate (p + 1) none ++ List.replicate q (some true) ++ a :: L)
            (List.replicate (B - 1) (some true) ++ none :: R)⟩ =
      ⟨(0 : Fin (B + 7)),
        Tape.mk (a :: L)
          (List.replicate q (some true) ++ List.replicate (p + 1) none
            ++ List.replicate (B - 1) none ++ none :: R)⟩ := by
  rw [show List.replicate (p + 1) none ++ List.replicate q (some true) ++ a :: L
      = none :: (List.replicate p none ++ List.replicate q (some true) ++ a :: L) from by
    simp only [List.replicate_succ, List.cons_append, List.append_assoc]]
  rw [show List.replicate (B - 1) (some true) = List.replicate ((B - 2) + 1) (some true) from by
    rw [show (B - 2) + 1 = B - 1 from by omega]]
  rw [show 2 * B + p + q + 2 = (2 * (B - 2) + 4) + (p + q + 2) from by omega]
  rw [DTM.run_add (segInc B) (2 * (B - 2) + 4) (p + q + 2)]
  rw [segInc_run_carry B (B - 2) (by omega) none (by simp)
    (List.replicate p none ++ List.replicate q (some true) ++ a :: L) R]
  rw [show List.replicate (B - 2 + 1) none = List.replicate (B - 1) none from by
    rw [show (B - 2) + 1 = B - 1 from by omega]]
  rw [show (none :: List.replicate (B - 1) none) ++ none :: R
      = none :: (List.replicate (B - 1) none ++ none :: R) from List.cons_append]
  rw [segInc_walk_any B p q hq a ha L (List.replicate (B - 1) none ++ none :: R)]
  simp only [replicate_succ_append, List.append_assoc]

/-- **进位链整条（任意段长版）**：`r` 轮满段进位 + 末段（长度 `q < B`）加一，
    终态接受 `B+2`；覆盖 `q = 1`（数字 0）等小段情形。
    Full carry chain with a final segment of any length `q < B`, including `q = 1`. -/
theorem segInc_carryChain_any (B p q r : Nat) (hB : 3 ≤ B) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hqB : q + 1 < B) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (segInc B).run (r * (3 * B + p + 1) + (2 * B + p + q + 2) + (q + 1))
        ⟨(0 : Fin (B + 7)),
          Tape.mk (chainL p B r ++ List.replicate (p + 1) none
            ++ List.replicate q (some true) ++ a :: L)
            (List.replicate (B - 1) (some true) ++ none :: R)⟩ =
      ⟨(⟨B + 2, by omega⟩ : Fin (B + 7)),
        Tape.mk (List.replicate (q + 1) (some true) ++ a :: L)
          (List.replicate p none ++ List.replicate (B - 1) none
            ++ none :: chainJunk p B r R)⟩ := by
  rw [show r * (3 * B + p + 1) + (2 * B + p + q + 2) + (q + 1)
      = (r * (3 * B + p + 1) + (2 * B + p + q + 2)) + (q + 1) from rfl]
  rw [DTM.run_add (segInc B) (r * (3 * B + p + 1) + (2 * B + p + q + 2)) (q + 1)]
  rw [DTM.run_add (segInc B) (r * (3 * B + p + 1)) (2 * B + p + q + 2)]
  rw [show chainL p B r ++ List.replicate (p + 1) none ++ List.replicate q (some true)
        ++ a :: L
      = chainL p B r ++ (List.replicate (p + 1) none ++ List.replicate q (some true)
        ++ a :: L) from by
    simp only [List.append_assoc]]
  have hM : (List.replicate (p + 1) none ++ List.replicate q (some true) ++ a :: L).head?
      = some none := by
    rw [show List.replicate (p + 1) none = none :: List.replicate p none from by
      rw [List.replicate_succ]]
    simp only [List.cons_append, List.head?_cons]
  rw [segInc_carryIter B p r hB hp
    (List.replicate (p + 1) none ++ List.replicate q (some true) ++ a :: L) hM R]
  rw [segInc_roundC_any B p q hB hp hq a ha L (chainJunk p B r R)]
  rw [show List.replicate q (some true) ++ List.replicate (p + 1) none
        ++ List.replicate (B - 1) none ++ none :: chainJunk p B r R
      = List.replicate q (some true) ++ none
        :: (List.replicate p none ++ List.replicate (B - 1) none
          ++ none :: chainJunk p B r R) from by
    simp only [List.replicate_succ, List.cons_append, List.append_assoc]]
  rw [segInc_run_done B q hqB (a :: L)
    (List.replicate p none ++ List.replicate (B - 1) none ++ none :: chainJunk p B r R)]

/-! ### 读段写块机：计数相位读完段长后直接跳进写块相位 -/

/-- **读段写块机**：状态 `0..B+1` 是计数相位（状态值 = 已数真格数），读到非真格时
    **一步跳进**写块相位（状态 `B+2 + (count+1)`）；写块相位与 `writeBlock B` 逐字一致
    （状态整体平移 `B+2`），写出 `blockCode count = false :: true^(count+2)`。
    Read-segment-then-write-block machine: a one-step hand-off from counting to writing. -/
def readWriteSeg (B : Nat) : DTM (2 * B + 6) where
  step := fun s a =>
    if hc : s.val < B + 2 then
      match a with
      | some true => (⟨s.val + 1, by omega⟩, a, Dir.left)
      | _ => (⟨B + 2 + (s.val + 1), by omega⟩, a, Dir.stay)
    else
      if h0 : s.val = B + 2 then (⟨2 * B + 5, by omega⟩, some false, Dir.right)
      else (⟨s.val - 1, by omega⟩, some true, Dir.left)
  start := 0
  accept := ⟨2 * B + 5, by omega⟩
  reject := ⟨2 * B + 5, by omega⟩

/-- 非终止状态（≠ `2B+5`）不停机。 States other than `2B+5` never halt. -/
theorem readWriteSeg_halted_false (B st : Nat) (hst : st < 2 * B + 6) (h : st ≠ 2 * B + 5)
    (t : Tape) : (readWriteSeg B).halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (readWriteSeg B).accept.val = 2 * B + 5 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (readWriteSeg B).reject.val = 2 * B + 5 from rfl] at hv
    exact h hv

/-- 计数相位读真格：左移一格、状态加一。 Counting phase on a true cell. -/
theorem readWriteSeg_step_count (B st : Nat) (hst : st < 2 * B + 6) (hc : st < B + 2)
    (x : Sym) (L R : List Sym) :
    (readWriteSeg B).stepConfig
        (Config.mk (⟨st, hst⟩ : Fin (2 * B + 6)) (Tape.mk (x :: L) (some true :: R))) =
      Config.mk (⟨st + 1, by omega⟩ : Fin (2 * B + 6)) (Tape.mk L (x :: some true :: R)) := by
  simp only [DTM.stepConfig, readWriteSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_pos hc]

/-- 计数相位读非真格：一步跳进写块相位（纸带不动）。 Counting phase hand-off on a non-true cell. -/
theorem readWriteSeg_step_switch (B st : Nat) (hst : st < 2 * B + 6) (hc : st < B + 2)
    (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (readWriteSeg B).stepConfig
        (Config.mk (⟨st, hst⟩ : Fin (2 * B + 6)) (Tape.mk L (a :: R))) =
      Config.mk (⟨B + 2 + (st + 1), by omega⟩ : Fin (2 * B + 6)) (Tape.mk L (a :: R)) := by
  cases a with
  | none =>
      simp only [DTM.stepConfig, readWriteSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        Tape.moveRight, List.headD, List.tail]
      rw [dif_pos hc]
  | some b =>
      cases b with
      | false =>
          simp only [DTM.stepConfig, readWriteSeg, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, Tape.moveRight, List.headD, List.tail]
          rw [dif_pos hc]
      | true => exact absurd rfl ha

/-- 写块相位（状态 `B+2+m`，`m ≥ 1`）：写一个真格、左移一格、状态减一。 -/
theorem readWriteSeg_step_write1 (B m : Nat) (hm : 1 ≤ m) (hmB : m ≤ B + 2)
    (x : Sym) (L R : List Sym) :
    (readWriteSeg B).stepConfig
        (Config.mk (⟨B + 2 + m, by omega⟩ : Fin (2 * B + 6)) (Tape.mk (x :: L) R)) =
      Config.mk (⟨B + 2 + m - 1, by omega⟩ : Fin (2 * B + 6))
        (Tape.mk L (x :: some true :: R.tail)) := by
  simp only [DTM.stepConfig, readWriteSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_neg (by omega : ¬ B + 2 + m < B + 2)]
  rw [dif_neg (by omega : ¬ (B + 2 + m) = B + 2)]

/-- 写块相位（状态 `B+2`，`m = 0`）：写 `some false`、右移一格、进接受态。 -/
theorem readWriteSeg_step_write0 (B : Nat) (L R : List Sym) :
    (readWriteSeg B).stepConfig
        (Config.mk (⟨B + 2, by omega⟩ : Fin (2 * B + 6)) (Tape.mk L R)) =
      Config.mk (⟨2 * B + 5, by omega⟩ : Fin (2 * B + 6))
        (Tape.mk (some false :: L) R.tail) := by
  simp only [DTM.stepConfig, readWriteSeg, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, List.headD, List.tail]
  rw [dif_neg (by omega : ¬ B + 2 < B + 2)]
  rw [dif_pos (show True from trivial)]

/-- 同符号真格串的位移：`replicate (n+1) a ++ a :: R = replicate n a ++ a :: a :: R`。
    用于走位段（末尾多一个真格）与写块段（块码 `false :: true^(n+2)`）的接口对齐。
    Shifting a run of equal symbols: moving one `a` from the front to just after the run. -/
theorem replicate_succ_cons_append (n : Nat) (a : Sym) (R : List Sym) :
    List.replicate (n + 1) a ++ a :: R = List.replicate n a ++ a :: (a :: R) := by
  rw [replicate_succ_append (n + 1) a R]
  rw [replicate_succ_append n a (a :: R)]
  rw [replicate_succ_append (n + 1) a R]

/-- 计数相位的整段运行：左侧 `n` 个真格、头下再一个真格，`n + 1` 步后头停在左侧非真格上。
    Counting phase: `n + 1` steps walk left over `n + 1` true cells, leaving them on the right. -/
theorem readWriteSeg_run_count (B : Nat) :
    ∀ (n j : Nat) (h1 : j < 2 * B + 6) (h2 : j + n + 1 < 2 * B + 6)
      (hj : j + n ≤ B + 1) (a₀ : Sym) (h₀ : a₀ ≠ some true) (L R : List Sym),
      (readWriteSeg B).run (n + 1)
        ⟨(⟨j, h1⟩ : Fin (2 * B + 6)),
          Tape.mk (List.replicate n (some true) ++ a₀ :: L) (some true :: R)⟩ =
        ⟨(⟨j + n + 1, h2⟩ : Fin (2 * B + 6)),
          Tape.mk L (a₀ :: (List.replicate n (some true) ++ some true :: R))⟩ := by
  intro n
  induction n with
  | zero =>
      intro j h1 h2 hj a₀ h₀ L R
      rw [List.replicate_zero, List.nil_append, Nat.zero_add]
      rw [run_one_stp (readWriteSeg B)
        (Config.mk (⟨j, h1⟩ : Fin (2 * B + 6)) (Tape.mk (a₀ :: L) (some true :: R)))
        (readWriteSeg_halted_false B j h1 (by omega)
          (Tape.mk (a₀ :: L) (some true :: R)))]
      rw [readWriteSeg_step_count B j h1 (by omega) a₀ L R]
      rw [List.nil_append]
  | succ n ih =>
      intro j h1 h2 hj a₀ h₀ L R
      rw [show List.replicate (n + 1) (some true) ++ a₀ :: L
          = some true :: (List.replicate n (some true) ++ a₀ :: L) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [show n + 1 + 1 = 1 + (n + 1) from by omega]
      rw [DTM.run_add (readWriteSeg B) 1 (n + 1)]
      rw [run_one_stp (readWriteSeg B)
        (Config.mk (⟨j, h1⟩ : Fin (2 * B + 6))
          (Tape.mk (some true :: (List.replicate n (some true) ++ a₀ :: L)) (some true :: R)))
        (readWriteSeg_halted_false B j h1 (by omega) _)]
      rw [readWriteSeg_step_count B j h1 (by omega) (some true)
        (List.replicate n (some true) ++ a₀ :: L) R]
      rw [ih (j + 1) (by omega) (by omega) (by omega) a₀ h₀ L (some true :: R)]
      rw [replicate_succ_cons_append n (some true) R]
      exact congrArg
        (fun s => (Config.mk s
          (Tape.mk L (a₀ :: (List.replicate n (some true) ++ some true :: some true :: R))) :
            Config (2 * B + 6)))
        (by
          apply Fin.ext
          show j + 1 + n + 1 = j + (n + 1) + 1
          omega)

/-- 写块相位的整段运行：状态 `B+2+m` 起，`m + 1` 步写出块码 `false :: true^m`。
    Write phase: from state `B+2+m` it writes `blockCode m` leftward in `m + 1` steps. -/
theorem readWriteSeg_run_write (B : Nat) :
    ∀ (m : Nat) (hmB : m ≤ B + 2) (L₀ R₀ : List Sym), m ≤ L₀.length →
      (readWriteSeg B).run (m + 1)
        ⟨(⟨B + 2 + m, by omega⟩ : Fin (2 * B + 6)), Tape.mk L₀ R₀⟩ =
      ⟨(⟨2 * B + 5, by omega⟩ : Fin (2 * B + 6)),
        Tape.mk (some false :: L₀.drop m) (List.replicate m (some true) ++ R₀.tail)⟩ := by
  intro m
  induction m with
  | zero =>
      intro hmB L₀ R₀ hlen
      rw [Nat.zero_add]
      rw [show (⟨B + 2 + 0, by omega⟩ : Fin (2 * B + 6)) = ⟨B + 2, by omega⟩ from by
        apply Fin.ext
        show B + 2 + 0 = B + 2
        omega]
      rw [run_one_stp (readWriteSeg B)
        (Config.mk (⟨B + 2, by omega⟩ : Fin (2 * B + 6)) (Tape.mk L₀ R₀))
        (readWriteSeg_halted_false B (B + 2) (by omega) (by omega) _)]
      rw [readWriteSeg_step_write0 B L₀ R₀]
      rw [List.drop_zero, List.replicate_zero, List.nil_append]
  | succ m ih =>
      intro hmB L₀ R₀ hlen
      cases L₀ with
      | nil => exact absurd hlen (by simp)
      | cons x L₁ =>
          have hlen' : m ≤ L₁.length := by
            have h2 : m + 1 ≤ (x :: L₁).length := hlen
            simp only [List.length_cons] at h2
            omega
          rw [show m + 1 + 1 = 1 + (m + 1) from by omega]
          rw [DTM.run_add (readWriteSeg B) 1 (m + 1)]
          rw [run_one_stp (readWriteSeg B)
            (Config.mk (⟨B + 2 + (m + 1), by omega⟩ : Fin (2 * B + 6))
              (Tape.mk (x :: L₁) R₀))
            (readWriteSeg_halted_false B (B + 2 + (m + 1)) (by omega) (by omega) _)]
          rw [readWriteSeg_step_write1 B (m + 1) (by omega) (by omega) x L₁ R₀]
          rw [show (⟨B + 2 + (m + 1) - 1, by omega⟩ : Fin (2 * B + 6))
              = ⟨B + 2 + m, by omega⟩ from by
            apply Fin.ext
            show B + 2 + (m + 1) - 1 = B + 2 + m
            omega]
          rw [ih (by omega) L₁ (x :: some true :: R₀.tail) hlen']
          rw [show (x :: some true :: R₀.tail).tail = some true :: R₀.tail from rfl]
          rw [List.drop_succ_cons]
          rw [← replicate_succ_append m (some true) R₀.tail]

/-- **读段写块整段运行**：真格段 `true^(k+1)`（长度 ≤ `B`）后接非真格，机器在 `2k+5` 步内把它
    改写成块码 `false :: true^(k+2)`（即 `blockCode k`），并停在接受态。
    Whole-segment run: a segment of `k+1` trues is rewritten as the block code of digit `k`. -/
theorem readWriteSeg_run (B k : Nat) (hkB : k + 1 ≤ B) (a₀ : Sym) (h₀ : a₀ ≠ some true)
    (L R : List Sym) (hlen : k + 2 ≤ L.length) :
    (readWriteSeg B).run (2 * k + 5)
        ⟨(⟨0, by omega⟩ : Fin (2 * B + 6)),
          Tape.mk (List.replicate k (some true) ++ a₀ :: L) (some true :: R)⟩ =
      ⟨(⟨2 * B + 5, by omega⟩ : Fin (2 * B + 6)),
        Tape.mk (some false :: L.drop (k + 2))
          (List.replicate (k + 2) (some true)
            ++ (List.replicate k (some true) ++ some true :: R))⟩ := by
  -- 计数段 `k+1` 步 → 跳转 1 步 → 写块段 `k+3` 步
  rw [show 2 * k + 5 = (k + 1) + (1 + (k + 3)) from by omega]
  rw [DTM.run_add (readWriteSeg B) (k + 1) (1 + (k + 3))]
  rw [readWriteSeg_run_count B k 0 (by omega) (by omega) (by omega) a₀ h₀ L R]
  rw [show (⟨0 + k + 1, by omega⟩ : Fin (2 * B + 6)) = ⟨k + 1, by omega⟩ from by
    apply Fin.ext
    show 0 + k + 1 = k + 1
    omega]
  rw [DTM.run_add (readWriteSeg B) 1 (k + 3)]
  rw [run_one_stp (readWriteSeg B)
    (Config.mk (⟨k + 1, by omega⟩ : Fin (2 * B + 6))
      (Tape.mk L (a₀ :: (List.replicate k (some true) ++ some true :: R))))
    (readWriteSeg_halted_false B (k + 1) (by omega) (by omega) _)]
  rw [readWriteSeg_step_switch B (k + 1) (by omega) (by omega) a₀ h₀ L
    (List.replicate k (some true) ++ some true :: R)]
  rw [show (⟨B + 2 + (k + 1 + 1), by omega⟩ : Fin (2 * B + 6))
      = ⟨B + 2 + (k + 2), by omega⟩ from by
    apply Fin.ext
    show B + 2 + (k + 1 + 1) = B + 2 + (k + 2)
    omega]
  rw [readWriteSeg_run_write B (k + 2) (by omega) L
    (a₀ :: (List.replicate k (some true) ++ some true :: R)) hlen]
  rw [show (a₀ :: (List.replicate k (some true) ++ some true :: R)).tail
      = List.replicate k (some true) ++ some true :: R from rfl]
