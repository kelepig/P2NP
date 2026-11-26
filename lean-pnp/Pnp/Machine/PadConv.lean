/-
  文件：Pnp/Machine/PadConv.lean
  File: Pnp/Machine/PadConv.lean

  主题：**间隔式源的原地改写**——把 `(some true, none, none)^k` 这种「每单位 3 格」的
        源块，原地逐格改写成 `some false`，得到长度 `3k` 的连续 pad 段（`padStr` 单元）。
  Topic: in-place rewriting of the spaced source `(some true, none, none)^k` into a
  contiguous block of `some false` (the pad cells). Two states, `3k + 1` steps.

  设计要点（见 docs/07 补记 #199）：pad 段的长度必须**等于**源段的物理长度，
  因此源要写成固定的 3 格/单位；机器只需「逐格右行改写、遇哨兵 `some false` 停」，
  不需要任何左向行程（左向行程固定的写机无法让输出增长）。
  Design point: the pad block must fill exactly the source's physical length, so the source
  is laid out as fixed 3-symbol units; the machine only walks right, converting cells, and
  stops at the `some false` sentinel.
-/

import Pnp.Classes
import Pnp.Machine.WriteCodeL

namespace Pnp

namespace DTM

/-- 间隔式源块：`(some true, none, none)^k`（长度恰为 `3k`）。
    The spaced source block `(some true, none, none)^k`. -/
def padSrc : Nat → List Sym
  | 0 => []
  | k + 1 => some true :: none :: none :: padSrc k

@[simp] theorem padSrc_zero : padSrc 0 = [] := rfl

@[simp] theorem padSrc_succ (k : Nat) :
    padSrc (k + 1) = some true :: none :: none :: padSrc k := rfl

theorem padSrc_length (k : Nat) : (padSrc k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [padSrc_succ, ih, Nat.mul_succ]

/-- 末尾补三个同符号：`replicate n a ++ (a :: a :: a :: L) = replicate (n+3) a ++ L`。
    Appending three copies of `a` extends the replicate block by three. -/
theorem replicate_three_append (n : Nat) (a : Sym) (L : List Sym) :
    List.replicate n a ++ a :: a :: a :: L = List.replicate (n + 3) a ++ L := by
  rw [show a :: a :: a :: L = List.replicate 3 a ++ L from rfl]
  rw [← List.append_assoc, List.replicate_append_replicate]

/-- 原地改写机：状态 0 逐格右行、写入 `some false`；读到哨兵 `some false` 即接受。
    The converter: state 0 walks right writing `some false`; the sentinel `some false` accepts. -/
def padConv : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = some false then ((⟨1, by omega⟩ : Fin 2), a, Dir.stay)
      else ((0 : Fin 2), some false, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态（非终止）处的格局不停机。 A configuration in the start state never halts. -/
theorem padConv_halted_start (t : Tape) :
    padConv.halted ⟨(0 : Fin 2), t⟩ = false := by
  rw [DTM.halted]
  have h1 : (⟨(0 : Fin 2), t⟩ : Config 2).state = (0 : Fin 2) := rfl
  rw [h1]
  decide

/-- **改写一格**（非哨兵）：写 `some false` 并右移，左侧多一个 `some false`。
    Convert one non-sentinel cell: write `some false` and move right. -/
theorem padConv_step_write (P : List Sym) (a : Sym) (R : List Sym) (ha : a ≠ some false) :
    padConv.stepConfig ⟨(0 : Fin 2), Tape.mk P (a :: R)⟩
      = ⟨(0 : Fin 2), Tape.mk (some false :: P) R⟩ :=
  stepConfig_of_lit padConv (0 : Fin 2) a P R (0 : Fin 2) (some false) Dir.right
    (Tape.mk (some false :: P) R)
    (by
      simp only [padConv]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- **哨兵步**：读到 `some false` 即进入接受态（纸带不变）。
    The sentinel step: reading `some false` accepts without changing the tape. -/
theorem padConv_step_stop (P : List Sym) (R : List Sym) :
    padConv.stepConfig ⟨(0 : Fin 2), Tape.mk P (some false :: R)⟩
      = ⟨(1 : Fin 2), Tape.mk P (some false :: R)⟩ :=
  stepConfig_of_lit padConv (0 : Fin 2) (some false) P R (1 : Fin 2) (some false) Dir.stay
    (Tape.mk P (some false :: R))
    (by
      simp only [padConv]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      simp)
    (by rfl)

/-- 单步运行（非哨兵）。 One step on a non-sentinel cell. -/
theorem padConv_run1_write (P : List Sym) (a : Sym) (R : List Sym) (ha : a ≠ some false) :
    padConv.run 1 ⟨(0 : Fin 2), Tape.mk P (a :: R)⟩
      = ⟨(0 : Fin 2), Tape.mk (some false :: P) R⟩ := by
  rw [DTM.run_succ_of_not_halted padConv 0 _ (padConv_halted_start _)]
  exact padConv_step_write P a R ha

/-- 单步运行（哨兵）。 One step on the sentinel. -/
theorem padConv_run1_stop (P : List Sym) (R : List Sym) :
    padConv.run 1 ⟨(0 : Fin 2), Tape.mk P (some false :: R)⟩
      = ⟨(1 : Fin 2), Tape.mk P (some false :: R)⟩ := by
  rw [DTM.run_succ_of_not_halted padConv 0 _ (padConv_halted_start _)]
  exact padConv_step_stop P R

/-- **主定理**：`padSrc k` 后接哨兵 `some false`，在 `3k + 1` 步内原地变成
    长度 `3k` 的连续 `some false` 段并接受（左侧上下文 `L` 原样保留）。
    The main theorem: the spaced source becomes `3k` contiguous pad marks in `3k + 1` steps. -/
theorem padConv_run (k : Nat) (L : List Sym) (R : List Sym) :
    padConv.run (3 * k + 1)
      ⟨(0 : Fin 2), Tape.mk L (padSrc k ++ some false :: R)⟩
      = ⟨(1 : Fin 2),
          Tape.mk (List.replicate (3 * k) (some false) ++ L) (some false :: R)⟩ := by
  induction k generalizing L with
  | zero =>
      simpa using padConv_run1_stop L R
  | succ k ih =>
      -- 前三格 `some true, none, none` 逐格改写
      have hpad : padSrc (k + 1) ++ some false :: R
          = some true :: none :: none :: (padSrc k ++ some false :: R) := by
        simp only [padSrc_succ, List.cons_append]
      rw [hpad]
      have hs1 := padConv_run1_write L (some true) (none :: none :: (padSrc k ++ some false :: R))
        (by decide)
      have hs2 := padConv_run1_write (some false :: L) none (none :: (padSrc k ++ some false :: R))
        (by decide)
      have hs3 := padConv_run1_write (some false :: some false :: L) none
        (padSrc k ++ some false :: R) (by decide)
      rw [show 3 * (k + 1) + 1 = (1 + 1 + 1) + (3 * k + 1) from by omega,
        DTM.run_add padConv (1 + 1 + 1) (3 * k + 1),
        DTM.run_add padConv (1 + 1) 1, DTM.run_add padConv 1 1, hs1, hs2, hs3,
        ih (some false :: some false :: some false :: L)]
      -- 长度对齐：`3k + 3 = 3(k+1)`
      have hrep : List.replicate (3 * k) (some false) ++
          (some false :: some false :: some false :: L)
          = List.replicate (3 * (k + 1)) (some false) ++ L := by
        rw [replicate_three_append (3 * k) (some false) L,
          show 3 * k + 3 = 3 * (k + 1) from by omega]
      rw [hrep]

end DTM

end Pnp
