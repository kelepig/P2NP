/-
  文件：Pnp/Machine/LenCount.lean
  File: Pnp/Machine/LenCount.lean

  主题：**unary 计数器的复核相位 `cntWrite`**——从格块内任意位置左行越过整块（跳过非空白），
        跨过分隔空白，继续左行越过计数器，在最左空白处写一个 `some true`（计数器加一），
        再右行穿越新增计数段与分隔空白，回到格块的**左端**相位 0。
  Topic: the "counter write" phase `cntWrite`: from inside the cell block it walks left across the
  whole block, crosses the separator blank, walks left over the existing unary counter and writes
  one `some true` at the frontier (counter + 1), then walks right back to the block's left end.

  布局（`left` 列表离头最近在前）：
      〈Lb ++ none :: true^k ++ none :: F , a :: R〉
  `Lb` = 块内头左侧的符号（最近在前），`a :: R` = 块内头起其余符号与块外内容；
  终态 `〈none :: true^(k+1) ++ F , Lb.reverse ++ a :: R〉`（头回块左端，计数器 +1）。
  Layout: left tape holds `Lb ++ none :: true^k ++ none :: F` (nearest first); the head sits on
  `a`, the block's remainder. The run ends at the block's left end with the counter grown by one.

  用途（#216，`T = |w|^k + k` 机内计算的「记 n = |w|」段）：与 `seekMark3` 组成一轮。
  Use (#216, the "record n = |w|" part of computing `T = |w|^k + k` in-machine): one round together
  with `seekMark3`.

  本文件给出：
    - 机器 `cntWrite : DTM 5`（0 = 越格块、1 = 越计数器、2 = 右行越回、3 = 回相位 0）；
    - 单步 `cntWrite_step0_move` / `cntWrite_step0_blank` 与单步套路 `estepCW`；
    - 段引理 `cntWrite_walkBlock`（`|Lb|+1` 步到分隔空格）、`cntWrite_enterCounter`（进计数器）、
      `cntWrite_walkBlock_pos` / `cntWrite_walkBlock_zero`（合起来 `|Lb|+2` 步）、
      `cntWrite_skipCounter` / `cntWrite_write0` / `cntWrite_skipTrue` / `cntWrite_step3(_prefix)`；
    - **`cntWrite_run`**：`|Lb| + 2k + 6` 步，计数器 `k ↦ k+1`，头回块左端（`k = 0` 单列一支）。
  This file gives the machine, the segment lemmas, and the whole-phase run spec.
-/

import Pnp.Machine.LenSeek

namespace Pnp

namespace DTM

/-- **计数器复核相位机**：0 左行越过格块（非空白）、遇空白进 1；1 左行越过 `some true`、
    遇空白写 `some true` 进 2；2 右行越过 `some true`、遇空白进 3；3 见非空白回 0。
    4 = accept = reject（不可达）。
    The counter-write phase machine; 4 is an unreachable halt state. -/
def cntWrite : DTM 5 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | none => (⟨1, by omega⟩, none, Dir.left)
       | some x => (⟨0, by omega⟩, some x, Dir.left))
    | 1 => (match a with
       | some true => (⟨1, by omega⟩, some true, Dir.left)
       | _ => (⟨2, by omega⟩, some true, Dir.stay))
    | 2 => (match a with
       | some true => (⟨2, by omega⟩, some true, Dir.right)
       | _ => (⟨3, by omega⟩, none, Dir.right))
    | 3 => (match a with
       | none => (⟨3, by omega⟩, none, Dir.right)
       | some x => (⟨0, by omega⟩, some x, Dir.stay))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨4, by omega⟩
  reject := ⟨4, by omega⟩

/-- 相位机在 0–3 内永不停机。 The phase machine never halts while in states 0–3. -/
theorem cntWrite_halted_ne (st : Nat) (hst : st < 5) (h4 : st ≠ 4) (t : Tape) :
    cntWrite.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show cntWrite.accept.val = 4 from rfl] at hv
    exact h4 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show cntWrite.reject.val = 4 from rfl] at hv
    exact h4 hv

/-- `cntWrite` 的单步套路。 The one-step idiom for `cntWrite`. -/
theorem estepCW (st : Nat) (hst : st < 5) (a : Sym) (q' : Fin 5) (s : Sym) (d : Dir)
    (h : cntWrite.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 4) :
    cntWrite.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (cntWrite_halted_ne st hst hne _)]
  exact stepConfig_of_step cntWrite ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 0 读非空白：左移一格（左带首符号推到头位，原头退居第二位）。
    State 0 on a non-blank head moves left, popping the left tape's first symbol. -/
theorem cntWrite_step0_move (x : Sym) (L' : List Sym) (a : Sym) (R : List Sym)
    (ha : a ≠ none) :
    cntWrite.run 1 ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk (x :: L') (a :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk L' (x :: a :: R)⟩ := by
  rcases ha' : a with _ | b
  · exact absurd ha' ha
  rw [estepCW 0 (by omega) (some b) (⟨0, by omega⟩ : Fin 5) (some b) Dir.left
    (by rfl) _ _ (by omega)]
  etape

/-- 状态 0 读空白：跨分隔，进状态 1。 State 0 on a blank crosses the separator. -/
theorem cntWrite_step0_blank (x : Sym) (L' : List Sym) (R : List Sym) :
    cntWrite.run 1 ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk (x :: L') (none :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 5), Tape.mk L' (x :: none :: R)⟩ := by
  rw [estepCW 0 (by omega) none (⟨1, by omega⟩ : Fin 5) none Dir.left
    (by rfl) _ _ (by omega)]
  etape

/-- **越过格块到分隔空白**：`|Lb|+1` 步吃掉整块与分隔空白，头落在计数器最近一格（或其空位），
    状态仍为 0；左带只剩计数器与远端。
    Crossing the whole block and the separator: `|Lb|+1` steps with state still 0. -/
theorem cntWrite_walkBlock : ∀ (Lb : List Sym) (k : Nat) (F : List Sym) (a : Sym)
    (R : List Sym), (∀ x ∈ Lb, x ≠ none) → a ≠ none →
    cntWrite.run (Lb.length + 1)
      ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk (Lb ++ none :: List.replicate k (some true) ++ none :: F) (a :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5),
          Tape.mk (List.replicate k (some true) ++ none :: F) (none :: Lb.reverse ++ a :: R)⟩
  | [], k, F, a, R, _, ha => by
      rw [show ([].length + 1 : Nat) = 1 from rfl]
      simp only [List.nil_append, List.cons_append]
      rw [cntWrite_step0_move none (List.replicate k (some true) ++ none :: F) a R ha]
      simp
  | x :: xs, k, F, a, R, hLb, ha => by
      have hx : x ≠ none := hLb x (by simp)
      rw [show (x :: xs).length + 1 = 1 + (xs.length + 1) from by
        rw [List.length_cons]; omega]
      rw [DTM.run_add cntWrite 1 (xs.length + 1)]
      simp only [List.cons_append]
      rw [cntWrite_step0_move x (xs ++ none :: List.replicate k (some true) ++ none :: F)
        a R ha]
      rw [cntWrite_walkBlock xs k F x (a :: R)
        (by intro y hy; exact hLb y (by simp [hy])) hx]
      rw [List.reverse_cons]
      simp [List.append_assoc]

/-- **进入计数器（`k ≥ 1`）**：头在分隔空白、状态 0；一步后落到计数器最近格，状态 1。
    Entering the counter (nonempty) from the separator blank, one step. -/
theorem cntWrite_enterCounter (k : Nat) (F P : List Sym) (hk : 1 ≤ k) :
    cntWrite.run 1
      ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk (List.replicate k (some true) ++ none :: F) (none :: P)⟩
      = ⟨(⟨1, by omega⟩ : Fin 5),
          Tape.mk (List.replicate (k - 1) (some true) ++ none :: F) (some true :: none :: P)⟩ := by
  have hrep : List.replicate k (some true)
      = some true :: List.replicate (k - 1) (some true) := by
    match k with
    | 0 => omega
    | _ + 1 => rfl
  rw [hrep]
  simp only [List.cons_append]
  rw [cntWrite_step0_blank]

/-- **越过格块（`k ≥ 1`）**：`|Lb| + 2` 步越过整块并跨分隔，头落在计数器最近的 `some true` 上。
    Crossing the block and separator when the counter is nonempty. -/
theorem cntWrite_walkBlock_pos (Lb : List Sym) (k : Nat) (F : List Sym) (a : Sym)
    (R : List Sym) (hk : 1 ≤ k) (hLb : ∀ x ∈ Lb, x ≠ none) (ha : a ≠ none) :
    cntWrite.run (Lb.length + 2)
      ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk (Lb ++ none :: List.replicate k (some true) ++ none :: F) (a :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 5),
          Tape.mk (List.replicate (k - 1) (some true) ++ none :: F)
            (some true :: none :: Lb.reverse ++ a :: R)⟩ := by
  rw [show Lb.length + 2 = (Lb.length + 1) + 1 from by omega]
  rw [DTM.run_add cntWrite (Lb.length + 1) 1]
  rw [cntWrite_walkBlock Lb k F a R hLb ha]
  simp only [List.cons_append]
  rw [cntWrite_enterCounter k F (Lb.reverse ++ a :: R) hk]

/-- **越过格块（`k = 0`）**：`|Lb| + 2` 步越过整块、跨分隔、再跨掉前沿空白，头在空白上。
    Crossing the block and separator when the counter is empty. -/
theorem cntWrite_walkBlock_zero : ∀ (Lb : List Sym) (F : List Sym) (a : Sym)
    (R : List Sym), (∀ x ∈ Lb, x ≠ none) → a ≠ none →
    cntWrite.run (Lb.length + 2)
      ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk (Lb ++ none :: none :: F) (a :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 5),
          Tape.mk F (none :: none :: Lb.reverse ++ a :: R)⟩
  | [], F, a, R, _, ha => by
      rw [show ([].length + 2 : Nat) = 1 + 1 from rfl, DTM.run_add cntWrite 1 1]
      simp only [List.nil_append]
      rw [cntWrite_step0_move none (none :: F) a R ha]
      simp only [List.cons_append]
      rw [cntWrite_step0_blank none F (a :: R)]
      simp
  | x :: xs, F, a, R, hLb, ha => by
      have hx : x ≠ none := hLb x (by simp)
      rw [show (x :: xs).length + 2 = 1 + (xs.length + 2) from by
        rw [List.length_cons]; omega]
      rw [DTM.run_add cntWrite 1 (xs.length + 2)]
      simp only [List.cons_append]
      rw [cntWrite_step0_move x (xs ++ none :: none :: F) a R ha]
      rw [cntWrite_walkBlock_zero xs F x (a :: R)
        (by intro y hy; exact hLb y (by simp [hy])) hx]
      rw [List.reverse_cons]
      simp [List.append_assoc]

/-- 相同符号的 `cons` 可与 `replicate` 交换位置（`k` 侧）。
    A `cons` of the repeated symbol slides past a `replicate` block (leftward form). -/
theorem rep_cons_swap (k : Nat) (x : Sym) (M : List Sym) :
    x :: List.replicate k x ++ M = List.replicate k x ++ x :: M := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append] at ih ⊢
      rw [ih]

/-- 相同符号的 `cons` 可与 `replicate` 合并（多一个）。
    Merging one repeated symbol with a `replicate` block. -/
theorem rep_cons_merge (k : Nat) (x : Sym) (M : List Sym) :
    List.replicate k x ++ x :: M = List.replicate (k + 1) x ++ M := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [List.cons_append] at ih ⊢
      rw [ih]

/-- **越过计数器并写一个 `true`（`j ≥ 0`）**：状态 1 从计数器最近格出发，`j + 2` 步吃掉
    `j` 个剩余 `true` 与前沿空白、在空白处写 `some true`，进状态 2；右带计数段为 `j+2` 个 `true`。
    Walking over the counter and writing one `true` at the frontier. -/
theorem cntWrite_skipCounter (j : Nat) (F M : List Sym) :
    cntWrite.run (j + 2)
      ⟨(⟨1, by omega⟩ : Fin 5),
        Tape.mk (List.replicate j (some true) ++ none :: F) (some true :: M)⟩
      = ⟨(⟨2, by omega⟩ : Fin 5),
          Tape.mk F (List.replicate (j + 2) (some true) ++ M)⟩ := by
  induction j generalizing F M with
  | zero =>
      rw [show (List.replicate 0 (some true) ++ none :: F) = none :: F from rfl]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add cntWrite 1 1]
      rw [estepCW 1 (by omega) (some true) (⟨1, by omega⟩ : Fin 5) (some true) Dir.left
        (by rfl) _ _ (by omega)]
      etape
      rw [estepCW 1 (by omega) none (⟨2, by omega⟩ : Fin 5) (some true) Dir.stay
        (by rfl) _ _ (by omega)]
      etape
      simp
  | succ j ih =>
      rw [show List.replicate (j + 1) (some true) ++ none :: F
          = some true :: (List.replicate j (some true) ++ none :: F) from rfl]
      rw [show (j + 1 + 2 : Nat) = 1 + (j + 2) from by omega]
      rw [DTM.run_add cntWrite 1 (j + 2)]
      rw [estepCW 1 (by omega) (some true) (⟨1, by omega⟩ : Fin 5) (some true) Dir.left
        (by rfl) _ _ (by omega)]
      etape
      rw [ih F (some true :: M)]
      rw [show 1 + (j + 2) = (j + 2) + 1 from by omega]
      rw [rep_cons_merge (j + 2) (some true) M]

/-- **空计数器时写第一个 `true`**：状态 1 见前沿空白即写 `some true` 进状态 2。
    Writing the first `true` when the counter is empty. -/
theorem cntWrite_write0 (F M : List Sym) :
    cntWrite.run 1 ⟨(⟨1, by omega⟩ : Fin 5), Tape.mk F (none :: M)⟩
      = ⟨(⟨2, by omega⟩ : Fin 5), Tape.mk F (some true :: M)⟩ := by
  rw [estepCW 1 (by omega) none (⟨2, by omega⟩ : Fin 5) (some true) Dir.stay
    (by rfl) _ _ (by omega)]
  etape

/-- **右行越回并跨分隔**：状态 2 右行越过 `m` 个 `some true`，遇空白跨过进状态 3。
    Walking right over the counter and crossing the separator back. -/
theorem cntWrite_skipTrue (m : Nat) (L F : List Sym) :
    cntWrite.run (m + 1)
      ⟨(⟨2, by omega⟩ : Fin 5),
        Tape.mk L (List.replicate m (some true) ++ none :: F)⟩
      = ⟨(⟨3, by omega⟩ : Fin 5),
          Tape.mk (none :: List.replicate m (some true) ++ L) F⟩ := by
  induction m generalizing L F with
  | zero =>
      rw [show List.replicate 0 (some true) ++ none :: F = none :: F from rfl]
      rw [show (0 + 1 : Nat) = 1 from rfl]
      rw [estepCW 2 (by omega) none (⟨3, by omega⟩ : Fin 5) none Dir.right
        (by rfl) _ _ (by omega)]
      etape
      simp
  | succ m ih =>
      rw [show List.replicate (m + 1) (some true) ++ none :: F
          = some true :: (List.replicate m (some true) ++ none :: F) from rfl]
      rw [show (m + 1 + 1 : Nat) = 1 + (m + 1) from by omega]
      rw [DTM.run_add cntWrite 1 (m + 1)]
      rw [estepCW 2 (by omega) (some true) (⟨2, by omega⟩ : Fin 5) (some true) Dir.right
        (by rfl) _ _ (by omega)]
      etape
      rw [ih (some true :: L) F]
      rw [show List.replicate (m + 1) (some true)
          = some true :: List.replicate m (some true) from rfl]
      simp only [List.cons_append]
      rw [← rep_cons_swap m (some true) L]
      simp only [List.cons_append]

/-- **回到相位 0**：状态 3 见非空白符号即回 0（1 步，头不动）。
    Back to phase 0 on a non-blank symbol. -/
theorem cntWrite_step3 (a : Sym) (L R : List Sym) (ha : a ≠ none) :
    cntWrite.run 1 ⟨(⟨3, by omega⟩ : Fin 5), Tape.mk L (a :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk L (a :: R)⟩ := by
  rcases ha' : a with _ | b
  · exact absurd ha' ha
  rw [estepCW 3 (by omega) (some b) (⟨0, by omega⟩ : Fin 5) (some b) Dir.stay
    (by rfl) _ _ (by omega)]
  etape

/-- **回到相位 0（前缀版）**：只要头符号非空白即可，尾部随意。
    The prefix form of `cntWrite_step3`: only the head symbol matters. -/
theorem cntWrite_step3_prefix : ∀ (P : List Sym) (y : Sym) (R : List Sym) (L : List Sym),
    (∀ z ∈ P, z ≠ none) → y ≠ none →
    cntWrite.run 1 ⟨(⟨3, by omega⟩ : Fin 5), Tape.mk L (P ++ y :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk L (P ++ y :: R)⟩
  | [], y, R, L, _, hy => cntWrite_step3 y L R hy
  | x :: xs, y, R, L, hP, _ => cntWrite_step3 x L (xs ++ y :: R) (hP x (by simp))

/-- **计数器复核整段**：`|Lb| + 2k + 6` 步完成「越过格块 → 计数器加一 → 回块左端」；
    计数器 `k ↦ k+1`，头回到格块左端。
    The whole counter-write phase: `|Lb| + 2k + 6` steps add one `true` and return the head
    to the block's left end. -/
theorem cntWrite_run (Lb : List Sym) (k : Nat) (F : List Sym) (a : Sym) (R : List Sym)
    (hLb : ∀ x ∈ Lb, x ≠ none) (ha : a ≠ none) :
    cntWrite.run (Lb.length + 2 * k + 6)
      ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk (Lb ++ none :: List.replicate k (some true) ++ none :: F) (a :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5),
          Tape.mk (none :: List.replicate (k + 1) (some true) ++ F)
            (Lb.reverse ++ a :: R)⟩ := by
  have hrev : ∀ z ∈ Lb.reverse, z ≠ none := by
    intro z hz
    exact hLb z (List.mem_reverse.mp hz)
  rcases k with _ | k
  · -- `k = 0`：越过格块（含前沿空白）→ 写第一个 `true` → 右行越回 → 回相位 0
    rw [show Lb.length + 2 * 0 + 6 = (Lb.length + 2) + (1 + 2 + 1) from by omega]
    rw [DTM.run_add cntWrite (Lb.length + 2) (1 + 2 + 1)]
    rw [List.append_assoc]
    rw [show (none :: List.replicate 0 (some true)) ++ none :: F = none :: none :: F from rfl]
    rw [cntWrite_walkBlock_zero Lb F a R hLb ha]
    rw [DTM.run_add cntWrite 1 (2 + 1)]
    simp only [List.cons_append]
    rw [cntWrite_write0 F (none :: (Lb.reverse ++ a :: R))]
    rw [DTM.run_add cntWrite 2 1]
    rw [← show List.replicate 1 (some true) ++ none :: (Lb.reverse ++ a :: R)
        = some true :: none :: (Lb.reverse ++ a :: R) from rfl]
    rw [cntWrite_skipTrue 1 F (Lb.reverse ++ a :: R)]
    rw [cntWrite_step3_prefix Lb.reverse a R (none :: List.replicate 1 (some true) ++ F)
      hrev ha]
    simp
  · -- `k + 1`：越过格块 → 计数器加一 → 右行越回 → 回相位 0
    rw [show Lb.length + 2 * (k + 1) + 6
        = (Lb.length + 2) + ((k + 2) + ((k + 3) + 1)) from by omega]
    rw [DTM.run_add cntWrite (Lb.length + 2) ((k + 2) + ((k + 3) + 1))]
    rw [cntWrite_walkBlock_pos Lb (k + 1) F a R (by omega) hLb ha]
    rw [show k + 1 - 1 = k from by omega]
    rw [DTM.run_add cntWrite (k + 2) ((k + 3) + 1)]
    simp only [List.cons_append]
    rw [cntWrite_skipCounter k F (none :: (Lb.reverse ++ a :: R))]
    rw [DTM.run_add cntWrite (k + 2 + 1) 1]
    rw [cntWrite_skipTrue (k + 2) F (Lb.reverse ++ a :: R)]
    rw [show k + 1 + 1 = k + 2 from by omega]
    rw [cntWrite_step3_prefix Lb.reverse a R (none :: List.replicate (k + 2) (some true) ++ F)
      hrev ha]
    simp

end DTM

end Pnp
