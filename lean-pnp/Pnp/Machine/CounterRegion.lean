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

end DTM

end Pnp
