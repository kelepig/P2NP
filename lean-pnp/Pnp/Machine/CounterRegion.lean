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

end DTM

end Pnp
