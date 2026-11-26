/-
  文件：Pnp/Machine/GoComp.lean
  File: Pnp/Machine/GoComp.lean

  主题：走位机的**顺序组合模板**——`goLeft a` 后接 `goLeft b` 的一台机器。
  Topic: the composition template for movers — `goLeft a` followed by `goLeft b` as one machine.

  用途（E 装配）：区域装配段要「左移 `3(T+1)` → 左移 `3|l'|` → 写头标记」，
  原有规格（`ExpandInit.expand_pad_to_initReg`）是**纸带函数**串接，不是一台机器；
  把 `goLeft` 用 `seqComp` 拼起来后，`seqComp_run` 一次给出整段运行，
  为后续五相位装配提供第一块可复用的机器级积木。
  Purpose: E needs the alignment segment as a real machine; this file proves the
  two-stage left-mover template with `seqComp_run`.
-/

import Pnp.Machine.Go
import Pnp.Machine.SeqComp
import Pnp.Machine.RegionBuild

namespace Pnp

namespace Tape

/-- 左移一步后右带必非空（左带为空时右带补一个空白；否则右带补回首符号）。
    A left move always leaves a nonempty right tape. -/
theorem moveLeft_right_ne (t : Tape) : t.moveLeft.right ≠ [] := by
  obtain ⟨l, r⟩ := t
  cases l with
  | nil => simp [Tape.moveLeft]
  | cons a as => simp [Tape.moveLeft]

end Tape

namespace DTM

/-- 至少左移一步后右带必非空。 A left-most-once mover keeps the right tape nonempty. -/
theorem moveLeftN_right_ne (k : Nat) (t : Tape) : (moveLeftN (k + 1) t).right ≠ [] := by
  induction k generalizing t with
  | zero => simpa [moveLeftN] using Tape.moveLeft_right_ne t
  | succ k ih =>
      rw [show moveLeftN (k + 1 + 1) t = moveLeftN (k + 1) (Tape.moveLeft t) from rfl]
      exact ih (Tape.moveLeft t)

/-- **两段左走机**：`goLeft a` 之后接着 `goLeft b`（状态数 `(a+1)+(b+1)`）。
    Two-stage left mover: `goLeft a` followed by `goLeft b`. -/
def goLeft2 (a b : Nat) : DTM ((a + 1) + (b + 1)) :=
  seqComp (goLeft a) (goLeft b)

/-- 组合机的右带非空判据（`a = 0` 时直落原纸带）。
    Right-tape nonemptiness after `a` left moves. -/
theorem moveLeftN_right_ne_of_pos (a : Nat) (t : Tape) (hr : t.right ≠ []) :
    (moveLeftN a t).right ≠ [] := by
  cases a with
  | zero => simpa [moveLeftN] using hr
  | succ a => exact moveLeftN_right_ne a t

/-- **两段左走的主运行引理**：从起点出发，`a + 1 + b` 步后停在接受态，纸带左移 `a+b` 次
    （分两段：先 `a` 次，再 `b` 次）。
    Primary run lemma for the two-stage left mover: after `a + 1 + b` steps the head has moved
    left `a` times, then `b` more. -/
theorem goLeft2_run (a b : Nat) (t : Tape) (hr : t.right ≠ []) :
    (goLeft2 a b).run (a + 1 + b) ⟨(goLeft2 a b).start, t⟩
      = ⟨(goLeft2 a b).accept, moveLeftN b (moveLeftN a t)⟩ := by
  have hne : (moveLeftN a t).right ≠ [] := moveLeftN_right_ne_of_pos a t hr
  refine seqComp_run (goLeft a) (goLeft b) a b ⟨(goLeft a).start, t⟩
    (moveLeftN a t) (moveLeftN b (moveLeftN a t))
    (goLeft_run a t hr) hne (goLeft_run b (moveLeftN a t) hne) ?_ ?_
  · -- A 段（`goLeft a`）在 `a` 步内不停机
    intro k hk
    rw [show (goLeft a).start = (⟨0, by omega⟩ : Fin (a + 1)) from rfl]
    rw [goLeft_run_from a k 0 t (by omega) hr]
    exact goLeft_halted_false a (0 + k) (by omega) (moveLeftN k t)
  · -- B 段（`goLeft b`）在 `b` 步内不停机
    intro k hk
    rw [show (goLeft b).start = (⟨0, by omega⟩ : Fin (b + 1)) from rfl]
    rw [goLeft_run_from b k 0 (moveLeftN a t) (by omega) hne]
    exact goLeft_halted_false b (0 + k) (by omega) (moveLeftN k (moveLeftN a t))

end DTM

end Pnp
