/-
  文件：Pnp/Machine/MarkTrue.lean
  File: Pnp/Machine/MarkTrue.lean

  主题：**整段 `some false` 原地改写成 `some true`（遇空白停）**——unary 加法「统一符号」
        收尾阶段的机器。逐格右行、写入 `some true`，读到空白即接受。
  Topic: rewrite a contiguous `some false` block into `some true` (stop at the first blank).
  The unification stage of the unary addition machine.

  依赖：`WalkLT.replicate_succ_append`（末尾补一个同符号的长度引理）。
  Uses `replicate_succ_append` from `Pnp/Machine/WalkLT.lean`.
-/

import Pnp.Machine.WalkLT

namespace Pnp

namespace DTM

/-- 统一符号机：状态 0 逐格右行写 `some true`；读到空白进状态 1（接受）。
    The unification machine: state 0 walks right writing `some true`; a blank accepts. -/
def markTrue : DTM 2 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then ((⟨1, by omega⟩ : Fin 2), a, Dir.stay)
      else ((0 : Fin 2), some true, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 1

/-- 起始态处的格局不停机。 A start-state configuration never halts. -/
theorem markTrue_halted_start (t : Tape) :
    markTrue.halted ⟨(0 : Fin 2), t⟩ = false := by
  rw [DTM.halted]
  have h1 : (⟨(0 : Fin 2), t⟩ : Config 2).state = (0 : Fin 2) := rfl
  rw [h1]
  decide

/-- **改写一格**（非空白）：写 `some true` 并右移。 Convert one cell to `some true`. -/
theorem markTrue_step_write (P : List Sym) (a : Sym) (R : List Sym) (ha : a ≠ none) :
    markTrue.stepConfig ⟨(0 : Fin 2), Tape.mk P (a :: R)⟩
      = ⟨(0 : Fin 2), Tape.mk (some true :: P) R⟩ :=
  stepConfig_of_lit markTrue (0 : Fin 2) a P R (0 : Fin 2) (some true) Dir.right
    (Tape.mk (some true :: P) R)
    (by
      simp only [markTrue]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rw [if_neg ha])
    (by rfl)

/-- **空白步**：读到空白即接受（纸带不变）。 The blank step: accept without change. -/
theorem markTrue_step_stop (P : List Sym) (R : List Sym) :
    markTrue.stepConfig ⟨(0 : Fin 2), Tape.mk P (none :: R)⟩
      = ⟨(1 : Fin 2), Tape.mk P (none :: R)⟩ :=
  stepConfig_of_lit markTrue (0 : Fin 2) none P R (1 : Fin 2) none Dir.stay
    (Tape.mk P (none :: R))
    (by
      simp only [markTrue]
      rw [if_pos (show (0 : Fin 2).val = 0 from rfl)]
      rfl)
    (by rfl)

/-- 单步运行（非空白）。 One step on a non-blank cell. -/
theorem markTrue_run1_write (P : List Sym) (a : Sym) (R : List Sym) (ha : a ≠ none) :
    markTrue.run 1 ⟨(0 : Fin 2), Tape.mk P (a :: R)⟩
      = ⟨(0 : Fin 2), Tape.mk (some true :: P) R⟩ := by
  have h := DTM.run_succ_of_not_halted markTrue 0
    ⟨(0 : Fin 2), Tape.mk P (a :: R)⟩ (markTrue_halted_start _)
  rw [markTrue_step_write P a R ha] at h
  simpa [DTM.run] using h

/-- 单步运行（空白）。 One step on the blank. -/
theorem markTrue_run1_stop (P : List Sym) (R : List Sym) :
    markTrue.run 1 ⟨(0 : Fin 2), Tape.mk P (none :: R)⟩
      = ⟨(1 : Fin 2), Tape.mk P (none :: R)⟩ := by
  have h := DTM.run_succ_of_not_halted markTrue 0
    ⟨(0 : Fin 2), Tape.mk P (none :: R)⟩ (markTrue_halted_start _)
  rw [markTrue_step_stop P R] at h
  simpa [DTM.run] using h

/-- **主定理**：连续 `m` 个 `some false` 之后是空白时，`m + 1` 步把它们原地改成
    `some true` 并接受（左侧上下文 `L` 原样保留）。
    The main theorem: `m` `some false` cells become `some true` in `m + 1` steps. -/
theorem markTrue_run (m : Nat) (L : List Sym) (R : List Sym) :
    markTrue.run (m + 1)
      ⟨(0 : Fin 2), Tape.mk L (List.replicate m (some false) ++ none :: R)⟩
      = ⟨(1 : Fin 2),
          Tape.mk (List.replicate m (some true) ++ L) (none :: R)⟩ := by
  induction m generalizing L with
  | zero => simpa using markTrue_run1_stop L R
  | succ m ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 1 : Nat) = 1 + (m + 1) from by omega,
        DTM.run_add markTrue 1 (m + 1)]
      rw [markTrue_run1_write L (some false)
        (List.replicate m (some false) ++ none :: R) (by decide)]
      rw [ih (some true :: L)]
      rw [replicate_succ_append m (some true) L]

end DTM

end Pnp
