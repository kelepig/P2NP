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

/-- `goLeft2_run` 的「纸带合并」写法：左移总次数合并成 `moveLeftN (a+b)`，
    便于与既有纸带级规格（如 `moveLeftN (3*(T+1))`）直接对接。
    Paper-level form of `goLeft2_run`, merged into `moveLeftN (a + b)`. -/
theorem goLeft2_run_add (a b : Nat) (t : Tape) (hr : t.right ≠ []) :
    (goLeft2 a b).run (a + 1 + b) ⟨(goLeft2 a b).start, t⟩
      = ⟨(goLeft2 a b).accept, moveLeftN (a + b) t⟩ := by
  rw [goLeft2_run a b t hr, moveLeftN_add]

/-- **`goLeft2` 左半段不停机**（`k ≤ a`）：组合机在左侧状态处不是终止态。
    The left half of `goLeft2` never halts (composite accept/reject live on the right). -/
theorem goLeft2_halted_false_left (a b k : Nat) (t : Tape) (hk : k ≤ a) (hr : t.right ≠ []) :
    (goLeft2 a b).halted ((goLeft2 a b).run k ⟨(goLeft2 a b).start, t⟩) = false := by
  -- 左段运行：状态 `castAdd ⟨k⟩`、纸带左移 `k` 次
  have hnh : ∀ j, j < k → (goLeft a).halted ((goLeft a).run j ⟨(goLeft a).start, t⟩) = false := by
    intro j hj
    rw [show (goLeft a).start = (⟨0, by omega⟩ : Fin (a + 1)) from rfl]
    rw [goLeft_run_from a j 0 t (by omega) hr]
    exact goLeft_halted_false a (0 + j) (by omega) (moveLeftN j t)
  have hrun : (goLeft2 a b).run k ⟨(goLeft2 a b).start, t⟩
      = ⟨Fin.castAdd (b + 1) ((goLeft a).run k ⟨(goLeft a).start, t⟩).state,
         ((goLeft a).run k ⟨(goLeft a).start, t⟩).tape⟩ :=
    seqComp_embed_left (goLeft a) (goLeft b) k ⟨(goLeft a).start, t⟩ hnh
  rw [hrun]
  -- 组合机的接受/拒绝都在右侧，左侧状态必不停机
  have h1 := (seqComp_halt_castAdd (goLeft a) (goLeft b)
    ((goLeft a).run k ⟨(goLeft a).start, t⟩).state).1
  have h2 := (seqComp_halt_castAdd (goLeft a) (goLeft b)
    ((goLeft a).run k ⟨(goLeft a).start, t⟩).state).2
  exact halted_false_of_ne (goLeft2 a b) _ h1.symm h2.symm

/-- **`goLeft2` 的停机判据**：整台组合机只在「右段走完」的那个状态停机
    （`goLeft` 的接受态与拒绝态相同，故组合机的终止态唯一）。
    有了它，「`k < a+1+b` 时不停机」只需比对状态数值即可。
    `goLeft2` halts exactly at its single terminal state, characterized by state value. -/
theorem goLeft2_halted_true_iff (a b : Nat) (c : Config ((a + 1) + (b + 1))) :
    (goLeft2 a b).halted c = true ↔ c.state.val = (a + 1) + b := by
  have hAR : (goLeft2 a b).accept = (goLeft2 a b).reject := rfl
  rw [Bool.eq_iff_iff, halted, hAR, Bool.or_self, beq_iff_eq, Fin.ext_iff]
  rw [show (goLeft2 a b).reject.val = (a + 1) + (goLeft b).reject.val from rfl]
  rw [show (goLeft b).reject.val = b from rfl]
  simp

/-- **`goLeft2` 右半段不停机**（`a+1 ≤ k < a+1+b`）：切换后进入右段，右段未走完时
    状态值严格小于终止值 `a+1+b`，故由 `goLeft2_halted_true_iff` 不停机。
    The right half of `goLeft2` never halts before its final state. -/
theorem goLeft2_halted_false_right (a b : Nat) (t : Tape) (j : Nat) (hj : j < b)
    (hr : t.right ≠ []) :
    (goLeft2 a b).halted ((goLeft2 a b).run ((a + 1) + j) ⟨(goLeft2 a b).start, t⟩)
      = false := by
  have hne : (moveLeftN a t).right ≠ [] := moveLeftN_right_ne_of_pos a t hr
  -- 左段不停机
  have hnhA : ∀ i, i < a → (goLeft a).halted ((goLeft a).run i ⟨(goLeft a).start, t⟩) = false := by
    intro i hi
    rw [show (goLeft a).start = (⟨0, by omega⟩ : Fin (a + 1)) from rfl]
    rw [goLeft_run_from a i 0 t (by omega) hr]
    exact goLeft_halted_false a (0 + i) (by omega) (moveLeftN i t)
  -- 左段 `a` 步的完整格局（状态 + 纸带）
  have hrun_a : (goLeft2 a b).run a ⟨(goLeft2 a b).start, t⟩
      = ⟨Fin.castAdd (b + 1) ((goLeft a).run a ⟨(goLeft a).start, t⟩).state,
         ((goLeft a).run a ⟨(goLeft a).start, t⟩).tape⟩ := by
    change (seqComp (goLeft a) (goLeft b)).run a _ = _
    exact seqComp_embed_left (goLeft a) (goLeft b) a ⟨(goLeft a).start, t⟩ hnhA
  -- 切换后的纸带仍是 `moveLeftN a t`（读到什么写回什么）
  have hstep : (goLeft2 a b).run 1 ⟨Fin.castAdd (b + 1) ((goLeft a).run a ⟨(goLeft a).start, t⟩).state,
        ((goLeft a).run a ⟨(goLeft a).start, t⟩).tape⟩
      = ⟨Fin.natAdd (a + 1) (goLeft b).start, moveLeftN a t⟩ := by
    change (seqComp (goLeft a) (goLeft b)).run 1 _ = _
    rw [goLeft_run a t hr]
    have hsw := seqComp_switch (goLeft a) (goLeft b)
      ⟨(⟨a, by omega⟩ : Fin (a + 1)), moveLeftN a t⟩ rfl
    rw [hsw, Tape.write_read (moveLeftN a t) hne]
    rfl
  -- `a+1` 步后落在右段起点
  have hpre : (goLeft2 a b).run (a + 1) ⟨(goLeft2 a b).start, t⟩
      = ⟨Fin.natAdd (a + 1) (goLeft b).start, moveLeftN a t⟩ := by
    rw [run_add (goLeft2 a b) a 1 ⟨(goLeft2 a b).start, t⟩, hrun_a]
    exact hstep
  -- 右段不停机
  have hnhB : ∀ i, i < j →
      (goLeft b).halted ((goLeft b).run i ⟨(goLeft b).start, moveLeftN a t⟩) = false := by
    intro i hi
    rw [show (goLeft b).start = (⟨0, by omega⟩ : Fin (b + 1)) from rfl]
    rw [goLeft_run_from b i 0 (moveLeftN a t) (by omega) hne]
    exact goLeft_halted_false b (0 + i) (by omega) (moveLeftN i (moveLeftN a t))
  -- 右段 `j` 步后的状态值
  have hstate_j : ((goLeft2 a b).run j ⟨Fin.natAdd (a + 1) (goLeft b).start, moveLeftN a t⟩).state
      = Fin.natAdd (a + 1) (⟨0 + j, by omega⟩ : Fin (b + 1)) := by
    have := seqComp_embed_right (goLeft a) (goLeft b) j ⟨(goLeft b).start, moveLeftN a t⟩ hnhB
    rw [show (goLeft b).start = (⟨0, by omega⟩ : Fin (b + 1)) from rfl,
      goLeft_run_from b j 0 (moveLeftN a t) (by omega) hne] at this
    exact congrArg Config.state this
  -- 组装：状态值 = `(a+1) + (0+j) < a+1+b`
  have hstate : ((goLeft2 a b).run ((a + 1) + j) ⟨(goLeft2 a b).start, t⟩).state.val
      = (a + 1) + (0 + j) := by
    rw [run_add (goLeft2 a b) (a + 1) j ⟨(goLeft2 a b).start, t⟩, hpre, hstate_j]
    rfl
  have hiff := goLeft2_halted_true_iff a b
    ((goLeft2 a b).run ((a + 1) + j) ⟨(goLeft2 a b).start, t⟩)
  rw [hstate] at hiff
  have hne' : (a + 1) + (0 + j) ≠ (a + 1) + b := by omega
  cases hb : (goLeft2 a b).halted
      ((goLeft2 a b).run ((a + 1) + j) ⟨(goLeft2 a b).start, t⟩) with
  | false => rfl
  | true => exact absurd (hiff.mp hb) hne'

/-- **`goLeft2` 全程不停机**（未走满 `a+1+b` 步）。
    `goLeft2` never halts before completing its `a+1+b` steps. -/
theorem goLeft2_halted_false (a b k : Nat) (t : Tape) (hk : k < a + 1 + b)
    (hr : t.right ≠ []) :
    (goLeft2 a b).halted ((goLeft2 a b).run k ⟨(goLeft2 a b).start, t⟩) = false := by
  rcases Nat.lt_or_ge k (a + 1) with h | h
  · exact goLeft2_halted_false_left a b k t (by omega) hr
  · obtain ⟨j, rfl⟩ : ∃ j, k = (a + 1) + j := ⟨k - (a + 1), by omega⟩
    exact goLeft2_halted_false_right a b t j (by omega) hr

/-- **头定位 + 写头标记机**：左移 `n` 格后原地写入 `some true`（区域编码的头标记）。
    状态数 `(n+1) + 2`。
    Head locator and marker: move left `n` cells, then write `some true` in place. -/
def markAlign (n : Nat) : DTM ((n + 1) + 2) :=
  seqComp (goLeft n) markHead

/-- **`markAlign` 的主运行引理**：`n + 1 + 1` 步后停在接受态，纸带左移 `n` 格且当前格
    被改写成 `some true`（区域编码的头标记位）。
    Primary run lemma for `markAlign`. -/
theorem markAlign_run (n : Nat) (t : Tape) (hr : t.right ≠ []) :
    (markAlign n).run (n + 1 + 1) ⟨(markAlign n).start, t⟩
      = ⟨(markAlign n).accept, (moveLeftN n t).write (some true)⟩ := by
  have hne : (moveLeftN n t).right ≠ [] := moveLeftN_right_ne_of_pos n t hr
  -- 右带拆成「头符号 + 余下」
  obtain ⟨L, a, R, ht⟩ : ∃ L a R, moveLeftN n t = Tape.mk L (a :: R) := by
    obtain ⟨L, R⟩ := moveLeftN n t
    cases R with
    | nil => exact absurd rfl hne
    | cons a as => exact ⟨L, a, as, rfl⟩
  -- 左段不停机
  have hnhA : ∀ i, i < n → (goLeft n).halted ((goLeft n).run i ⟨(goLeft n).start, t⟩) = false := by
    intro i hi
    rw [show (goLeft n).start = (⟨0, by omega⟩ : Fin (n + 1)) from rfl]
    rw [goLeft_run_from n i 0 t (by omega) hr]
    exact goLeft_halted_false n (0 + i) (by omega) (moveLeftN i t)
  -- 右段（`markHead` 一步）不停机（只有 `k = 0`）
  have hnhB : ∀ i, i < 1 →
      markHead.halted (markHead.run i ⟨markHead.start, moveLeftN n t⟩) = false := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact markHead_halted_zero (moveLeftN n t)
  refine seqComp_run (goLeft n) markHead n 1 ⟨(goLeft n).start, t⟩
    (moveLeftN n t) ((moveLeftN n t).write (some true))
    (goLeft_run n t hr) hne ?_ hnhA hnhB
  -- `markHead` 在主纸带上的运行
  rw [ht]
  have := markHead_run L a R
  rw [show (moveLeftN n t).write (some true) = Tape.mk L (some true :: R) from by
    rw [ht]; rfl]
  exact this

/-- `markAlign` 的结果与「分段左移」写法一致：`moveLeftN (a + (b + 1))` 即
    「左移 `a`、再左移 `b`、再左移 1」，与 `ExpandInit` 的纸带级链直接对接。
    The merged paper form matching the nested spec chain. -/
theorem moveLeftN_split3 (a b : Nat) (t : Tape) :
    moveLeftN (a + (b + 1)) t = Tape.moveLeft (moveLeftN b (moveLeftN a t)) := by
  rw [moveLeftN_add, moveLeftN_add]

end DTM

end Pnp
