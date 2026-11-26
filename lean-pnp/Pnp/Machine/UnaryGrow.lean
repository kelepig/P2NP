/-
  文件：Pnp/Machine/UnaryGrow.lean
  File: Pnp/Machine/UnaryGrow.lean

  主题：**unary 计数器加一**——把一串 `some true` 的右端再写一个真格。
  Topic: unary counter increment — extend a run of `some true` by one cell on the right.

  用途（B5 外层枚举 E 的 L1 路线 C，见 #280/#281）：数字区不能就地自增，故计数器改用
  **一进制（unary）**存在独立的计数器区：加一只是「多一个真格」，完全没有进位问题。
  计数器区布局：`[标志格 some false][真格串 true^i][数字区…]`——标志格在左、数字区在右，
  于是「右端追加一个真格」就是覆盖真格串右端的那一个空白格。
  Purpose (route C of L1): the counter is stored in unary in its own region, so incrementing
  it is just appending one true cell — no carries at all.

  与 `markTrue`（#201）的区别：`markTrue` 把整段 `some false` 改写成真格并在空白处接受；
  本机**只写一个**真格（写完右移一格）就停机，真格串长度因此恰好多 1。
  Difference from `markTrue`: this machine writes exactly one true cell (then moves right)
  and halts, so the run of true cells grows by exactly one.

  注：状态用 `Fin` 字面量（`(0 : Fin 2)`）而非 `⟨0, by omega⟩`，这样 `s.val` 能按 `rfl` 归约。
  Note: literal `Fin` states are used so that `s.val` reduces by `rfl`.
-/

import Pnp.Machine.MarkTrue

namespace Pnp

namespace DTM

/-- unary 计数器加一机：右行掠过真格，在第一个非真格处写 `some true` 并右移停机。
    Unary increment: walk right over the true run, write one true cell, move right, halt. -/
def extendTrue : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then ((0 : Fin 2), a, Dir.right)
      else ((1 : Fin 2), some true, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态处的格局不停机。 A start-state configuration never halts. -/
theorem extendTrue_halted_start (L R : List Sym) :
    extendTrue.halted ⟨(0 : Fin 2), Tape.mk L R⟩ = false := by
  show (((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))
      || ((0 : Fin 2) == (⟨1, by omega⟩ : Fin 2))) = false
  decide

/-- 掠过一格真格：右移。 Walk one true cell to the right. -/
theorem extendTrue_step_move (L R : List Sym) :
    extendTrue.stepConfig ⟨(0 : Fin 2), Tape.mk L (some true :: R)⟩ =
      ⟨(0 : Fin 2), Tape.mk (some true :: L) R⟩ :=
  stepConfig_of_lit extendTrue (0 : Fin 2) (some true) L R (0 : Fin 2) (some true) Dir.right
    (Tape.mk (some true :: L) R)
    (by
      simp only [extendTrue]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 在第一个非真格处写一个真格、右移并停机。 Write one true cell, move right, halt. -/
theorem extendTrue_step_write (L : List Sym) (a : Sym) (ha : a ≠ some true) (R : List Sym) :
    extendTrue.stepConfig ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk (some true :: L) R⟩ :=
  stepConfig_of_lit extendTrue (0 : Fin 2) a L R (1 : Fin 2) (some true) Dir.right
    (Tape.mk (some true :: L) R)
    (by
      simp only [extendTrue]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- 掠过整段真格：`k` 步后头停在段后的第一个非真格上，状态仍是 0。
    Walking over `k` true cells. -/
theorem extendTrue_walk : ∀ (k : Nat) (L : List Sym) (a : Sym), a ≠ some true →
    ∀ (R : List Sym),
      extendTrue.run k
          ⟨(0 : Fin 2), Tape.mk L (List.replicate k (some true) ++ a :: R)⟩ =
        ⟨(0 : Fin 2), Tape.mk (List.replicate k (some true) ++ L) (a :: R)⟩
  | 0, L, a, _, R => by
      show extendTrue.run 0 ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩ =
        ⟨(0 : Fin 2), Tape.mk L (a :: R)⟩
      rfl
  | k + 1, L, a, ha, R => by
      rw [show List.replicate (k + 1) (some true) ++ a :: R
          = some true :: (List.replicate k (some true) ++ a :: R) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted _ k _
        (extendTrue_halted_start L (some true :: (List.replicate k (some true) ++ a :: R)))]
      rw [extendTrue_step_move L (List.replicate k (some true) ++ a :: R)]
      rw [extendTrue_walk k (some true :: L) a ha R]
      rw [replicate_succ_append]

/-- **unary 计数器加一**：`k+1` 步后真格串长度 `k ↦ k+1`，头停在串尾右侧并停机。
    Unary increment: the run length goes `k ↦ k+1` in `k+1` steps. -/
theorem extendTrue_run (k : Nat) (L R : List Sym) :
    extendTrue.run (k + 1)
        ⟨(0 : Fin 2), Tape.mk L (List.replicate k (some true) ++ none :: R)⟩ =
      ⟨(1 : Fin 2), Tape.mk (List.replicate (k + 1) (some true) ++ L) R⟩ := by
  rw [DTM.run_add _ k 1]
  rw [extendTrue_walk k L none (by simp) R]
  show extendTrue.run (0 + 1)
      ⟨(0 : Fin 2), Tape.mk (List.replicate k (some true) ++ L) (none :: R)⟩ = _
  rw [DTM.run_succ_of_not_halted _ 0 _
    (extendTrue_halted_start (List.replicate k (some true) ++ L) (none :: R))]
  show extendTrue.stepConfig
      ⟨(0 : Fin 2), Tape.mk (List.replicate k (some true) ++ L) (none :: R)⟩ =
    ⟨(1 : Fin 2), Tape.mk (List.replicate (k + 1) (some true) ++ L) R⟩
  rw [extendTrue_step_write (List.replicate k (some true) ++ L) none (by simp) R]
  rw [List.replicate_succ, List.cons_append]

end DTM

end Pnp
