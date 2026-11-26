/-
  文件：Pnp/Machine/MulCopy.lean
  File: Pnp/Machine/MulCopy.lean

  主题：**unary 乘法的复制遍机 `mulCopy`**——把源块 `A` 从右往左逐格「标记 + 复制」到
        分隔空白之后的副本区，直到 A 全部标记（撞到 `sepB`）为止。
  Topic: the copy pass of unary multiplication. It repeatedly marks the next source cell,
  walks right across the separator to the frontier, writes a copy, and walks back across the
  separator; it halts when every source cell has been marked.

  布局（docs/07「#205 续」）：
    `L ++ [none, none] ++ B ++ [none] ++ A ++ [none] ++ acc ++ [none] ++ blanks ++ R`
                                   ^sepB        ^sepA        ^frontier
  状态：0 读下一个未读源格 / 1 右行跳过已标记格（待跨 sepA）/ 2 右行跳过副本格（待写副本）/
        4 左行跳过副本格（待跨回 sepA）/ 5 左行跳过已标记源格（找下一个源格或 sepB）/
        6 停机（A 已耗尽）。
  States: 0 read the next source cell, 1 skip marked cells rightwards, 2 skip copy cells
  rightwards, 4 skip copy cells leftwards, 5 skip marked source cells leftwards, 6 halt.
-/

import Pnp.Machine.Double
import Pnp.Machine.WalkRC

namespace Pnp

namespace DTM

/-- unary 乘法复制遍机（8 状态，仅用 0/1/2/4/5，6 为停机态）。
    The copy-pass machine; state 6 halts (source exhausted). -/
def mulCopy : DTM 8 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | some true => (⟨1, by omega⟩, some false, Dir.right)
       | _ => (⟨6, by omega⟩, a, Dir.stay))
    | 1 => (match a with
       | none => (⟨2, by omega⟩, none, Dir.right)
       | _ => (⟨1, by omega⟩, a, Dir.right))
    | 2 => (match a with
       | none => (⟨4, by omega⟩, some false, Dir.left)
       | _ => (⟨2, by omega⟩, a, Dir.right))
    | 4 => (match a with
       | some false => (⟨4, by omega⟩, some false, Dir.left)
       | none => (⟨5, by omega⟩, none, Dir.left)
       | some true => (⟨6, by omega⟩, some true, Dir.stay))
    | 5 => (match a with
       | some false => (⟨5, by omega⟩, some false, Dir.left)
       | some true => (⟨0, by omega⟩, some true, Dir.stay)
       | none => (⟨6, by omega⟩, none, Dir.stay))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 6
  reject := 6

/-- 非 6 状态一律不停机。 States other than 6 never halt. -/
theorem mulCopy_halted_ne (st : Nat) (hst : st < 8) (h : st ≠ 6) (t : Tape) :
    mulCopy.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulCopy.accept.val = 6 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulCopy.reject.val = 6 from rfl] at hv
    exact h hv

/-- `mulCopy` 的单步运行套路。 The one-step idiom for `mulCopy`. -/
theorem estepMC (st : Nat) (hst : st < 8) (a : Sym) (q' : Fin 8) (s : Sym) (d : Dir)
    (h : mulCopy.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 6) :
    mulCopy.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (mulCopy_halted_ne st hst hne _)]
  exact stepConfig_of_step mulCopy ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 1 右行跳过 `m` 个 `some false`（不跨空白）。 State 1 skips `m` cells. -/
theorem mulCopy_skip1 : ∀ (m : Nat) (L R : List Sym),
    mulCopy.run m
      ⟨(⟨1, by omega⟩ : Fin 8), Tape.mk L (List.replicate m (some false) ++ R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 8), Tape.mk (List.replicate m (some false) ++ L) R⟩
  | 0, L, R => by
      simp [DTM.run]
  | m + 1, L, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show m + 1 = 1 + m from by omega, DTM.run_add mulCopy 1 m]
      rw [estepMC 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulCopy_skip1 m (some false :: L) R]
      rw [← cons_replicate_append (some false) m L]

/-- 状态 1 读到空白：跨过它（`sepA`）进状态 2。 State 1 crosses the separator blank. -/
theorem mulCopy_cross1 (L : List Sym) (x0 : Sym) (R : List Sym) :
    mulCopy.run 1
      ⟨(⟨1, by omega⟩ : Fin 8), Tape.mk L (none :: x0 :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 8), Tape.mk (none :: L) (x0 :: R)⟩ := by
  rw [estepMC 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 状态 2 右行跳过 `m` 个 `some false`（副本区内部）。 State 2 skips the copy cells. -/
theorem mulCopy_skip2 : ∀ (m : Nat) (L R : List Sym),
    mulCopy.run m
      ⟨(⟨2, by omega⟩ : Fin 8), Tape.mk L (List.replicate m (some false) ++ R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 8), Tape.mk (List.replicate m (some false) ++ L) R⟩
  | 0, L, R => by
      simp [DTM.run]
  | m + 1, L, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show m + 1 = 1 + m from by omega, DTM.run_add mulCopy 1 m]
      rw [estepMC 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulCopy_skip2 m (some false :: L) R]
      rw [← cons_replicate_append (some false) m L]

/-- 状态 2 在前沿空白写一个副本并左移（左邻是副本格）。 State 2 writes the copy at the
    frontier and steps left onto an existing copy cell. -/
theorem mulCopy_write2_some (L' : List Sym) (R : List Sym) :
    mulCopy.run 1
      ⟨(⟨2, by omega⟩ : Fin 8), Tape.mk (some false :: L') (none :: R)⟩
      = ⟨(⟨4, by omega⟩ : Fin 8),
          Tape.mk L' (some false :: (some false :: R))⟩ := by
  rw [estepMC 2 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 状态 2 在前沿空白写一个副本并左移（左邻是 `sepA`，即副本区为空）。
    The same write step when the copy area was empty (the left neighbour is `sepA`). -/
theorem mulCopy_write2_none (L' : List Sym) (R : List Sym) :
    mulCopy.run 1
      ⟨(⟨2, by omega⟩ : Fin 8), Tape.mk (none :: L') (none :: R)⟩
      = ⟨(⟨4, by omega⟩ : Fin 8),
          Tape.mk L' (none :: (some false :: R))⟩ := by
  rw [estepMC 2 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 状态 4 在「左邻为 `some false`」时的一步（写回 `some false` 并左移）。
    The single state-4 step onto a `some false` neighbour. -/
theorem mulCopy_run1_step4 (L : List Sym) (R : List Sym) :
    mulCopy.run 1
      ⟨(⟨4, by omega⟩ : Fin 8), Tape.mk (some false :: L) (some false :: R)⟩
      = ⟨(⟨4, by omega⟩ : Fin 8), Tape.mk L (some false :: (some false :: R))⟩ := by
  rw [estepMC 4 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 状态 4 左行跳过 `m` 个 `some false`（左带里的副本格）。
    State 4 skips `m` copy cells on its left. -/
theorem mulCopy_skip4 : ∀ (m : Nat) (L : List Sym) (R : List Sym),
    mulCopy.run m
      ⟨(⟨4, by omega⟩ : Fin 8), Tape.mk (List.replicate m (some false) ++ L) (some false :: R)⟩
      = ⟨(⟨4, by omega⟩ : Fin 8), Tape.mk L (List.replicate (m + 1) (some false) ++ R)⟩
  | 0, L, R => by
      change mulCopy.run 0 ⟨(⟨4, by omega⟩ : Fin 8),
          Tape.mk L (some false :: R)⟩ = _
      simp [DTM.run, List.replicate_succ, List.cons_append]
  | m + 1, L, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      change mulCopy.run (Nat.succ m)
        ⟨(⟨4, by omega⟩ : Fin 8),
          Tape.mk (some false :: (List.replicate m (some false) ++ L)) (some false :: R)⟩
        = ⟨(⟨4, by omega⟩ : Fin 8),
            Tape.mk L (List.replicate (m + 1 + 1) (some false) ++ R)⟩
      rw [DTM.run_succ_of_not_halted _ m _ (mulCopy_halted_ne 4 (by omega) (by omega) _)]
      have hstep : mulCopy.stepConfig
          ⟨(⟨4, by omega⟩ : Fin 8),
            Tape.mk (some false :: (List.replicate m (some false) ++ L)) (some false :: R)⟩
          = ⟨(⟨4, by omega⟩ : Fin 8),
              Tape.mk (List.replicate m (some false) ++ L) (some false :: (some false :: R))⟩ := by
        have h := mulCopy_run1_step4 (List.replicate m (some false) ++ L) R
        rw [DTM.run, mulCopy_halted_ne 4 (by omega) (by omega) _] at h
        exact h
      rw [hstep]
      rw [mulCopy_skip4 m L (some false :: R)]
      rw [replicate_succ_append (m + 1) (some false) R]

/-- 状态 4 读到空白：跨过它（回到 `sepA` 左侧）进状态 5，头落在左邻格上。
    State 4 crosses `sepA` back; the head lands on the left neighbour. -/
theorem mulCopy_cross4 (x0 : Sym) (X : List Sym) (x1 : Sym) (R : List Sym) :
    mulCopy.run 1
      ⟨(⟨4, by omega⟩ : Fin 8), Tape.mk (x0 :: X) (none :: x1 :: R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 8), Tape.mk X (x0 :: none :: x1 :: R)⟩ := by
  rw [estepMC 4 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 状态 5 跳过 `m` 个已标记源格后停在下一个源格（回状态 0）。
    State 5 skips marked source cells and stops on the next source cell. -/
theorem mulCopy_skip5_true : ∀ (m : Nat) (P R : List Sym),
    mulCopy.run (m + 2)
      ⟨(⟨5, by omega⟩ : Fin 8),
        Tape.mk (List.replicate m (some false) ++ some true :: P) (some false :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 8),
          Tape.mk P (some true :: List.replicate (m + 1) (some false) ++ R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add mulCopy 1 1]
      rw [estepMC 5 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepMC 5 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add mulCopy 1 (m + 2)]
      rw [estepMC 5 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulCopy_skip5_true m P (some false :: R)]
      rw [List.cons_append, replicate_succ_append (m + 1) (some false) R]

/-- 状态 5 跳过 `m` 个已标记源格后读到空白（`sepB`，源耗尽）⇒ 状态 6 停机。
    State 5 skips marked cells and stops on `sepB`: the source is exhausted. -/
theorem mulCopy_skip5_none : ∀ (m : Nat) (P R : List Sym),
    mulCopy.run (m + 2)
      ⟨(⟨5, by omega⟩ : Fin 8),
        Tape.mk (List.replicate m (some false) ++ none :: P) (some false :: R)⟩
      = ⟨(⟨6, by omega⟩ : Fin 8),
          Tape.mk P (none :: List.replicate (m + 1) (some false) ++ R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add mulCopy 1 1]
      rw [estepMC 5 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepMC 5 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add mulCopy 1 (m + 2)]
      rw [estepMC 5 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulCopy_skip5_none m P (some false :: R)]
      rw [List.cons_append, replicate_succ_append (m + 1) (some false) R]

end DTM

end Pnp

namespace Pnp

namespace DTM

/-- 复制遍不变量左带：A 的未读段 + `sepB` + B 区 + 双哨兵 + 外部上下文。
    Left side of the copy-pass invariant. -/
abbrev mulL (a b r i : Nat) (L : List Sym) : List Sym :=
  List.replicate (a - 1 - i) (some true) ++
    (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
      (none :: (none :: L))))

/-- 复制遍不变量右带：当前源格 + 已标记源格 + `sepA` + 副本区（`d` 格）+ 前沿空白 +
    预留空白 + 外部尾。
    Right side of the copy-pass invariant. -/
abbrev mulR (d i w : Nat) (R : List Sym) : List Sym :=
  some true :: (List.replicate i (some false) ++
    (none :: (List.replicate d (some false) ++ (none :: (List.replicate w (none : Sym) ++ R)))))

/-- 跨 `sepA` 回到 A 侧（左邻是 `k + 1` 个 `some false` 的连续块）。
    Cross `sepA` back when the source side starts with a `k + 1` block. -/
theorem mulCopy_cross4_rep (k : Nat) (P : List Sym) (x1 : Sym) (R : List Sym) :
    mulCopy.run 1
      ⟨(⟨4, by omega⟩ : Fin 8),
        Tape.mk (List.replicate (k + 1) (some false) ++ P) (none :: x1 :: R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 8),
          Tape.mk (List.replicate k (some false) ++ P) (some false :: none :: x1 :: R)⟩ := by
  rw [List.replicate_succ, List.cons_append]
  exact mulCopy_cross4 (some false) (List.replicate k (some false) ++ P) x1 R

/-- **第一轮的第一个复制单元**（副本区为空）：`6` 步推进不变量一格。
    The very first copy unit (empty copy area): advance the invariant in 6 steps. -/
theorem mulCopy_first (a b r w : Nat) (ha : 2 ≤ a) (L R : List Sym) :
    mulCopy.run 6
      ⟨(⟨0, by omega⟩ : Fin 8), Tape.mk (mulL a b r 0 L) (mulR 0 0 w R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 8),
          Tape.mk (mulL a b r 1 L) (mulR 1 1 (w - 1) R)⟩ := by
  -- 不变量展开成显式形态
  have hL0 : mulL a b r 0 L = some true :: (List.replicate (a - 1 - 0) (some true) ++
      (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
        (none :: (none :: L))))) := by
    simp only [mulL, List.replicate_zero]
    rfl
  have hR0 : mulR 0 0 w R = some true :: (none :: (none :: (List.replicate w (none : Sym) ++ R))) := by
    simp only [mulR, List.replicate_zero, List.nil_append]
  rw [hL0, hR0]
  -- 6 = 1 + 1 + 1 + 1 + 2
  rw [show (6 : Nat) = 1 + (1 + (1 + (1 + 2))) from by omega]
  rw [DTM.run_add mulCopy 1 (1 + (1 + (1 + 2)))]
  -- 1 步：标记源格
  rw [estepMC 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 1 步：跨 sepA
  rw [DTM.run_add mulCopy 1 (1 + (1 + 2))]
  rw [mulCopy_cross1 (some false :: (List.replicate (a - 1 - 0) (some true) ++
        (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
          (none :: (none :: L)))))) none (List.replicate w (none : Sym) ++ R)]
  -- 1 步：在空副本区前沿写副本
  rw [DTM.run_add mulCopy 1 (1 + 2)]
  rw [mulCopy_write2_none (some false :: (List.replicate (a - 1 - 0) (some true) ++
        (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
          (none :: (none :: L)))))) (List.replicate w (none : Sym) ++ R)]
  -- 1 步：跨回 sepA
  rw [DTM.run_add mulCopy 1 2]
  rw [show List.replicate (0 : Nat) (some false) ++ (some false :: (List.replicate (a - 1 - 0) (some true) ++
        (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
          (none :: (none :: L))))))
      = List.replicate 1 (some false) ++ (List.replicate (a - 1 - 0) (some true) ++
        (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
          (none :: (none :: L))))) from by
    simp only [List.replicate_succ, List.replicate_zero, List.nil_append]]
  rw [mulCopy_cross4 (some false) (List.replicate (a - 1 - 0) (some true) ++
        (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
          (none :: (none :: L))))) (some false) (List.replicate w (none : Sym) ++ R)]
  -- 2 步：读到下一个源格
  rw [mulCopy_skip5_true 0 (List.replicate (a - 1 - 1) (some true) ++
        (none :: (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++
          (none :: (none :: L)))))
      (none :: (some false :: (List.replicate w (none : Sym) ++ R)))]
  -- 形状对齐：`replicate (a - 2) = replicate (a - 1 - 1)`；前沿空白拆一个
  rw [show List.replicate w (none : Sym) = none :: List.replicate (w - 1) (none : Sym) from by
    rw [show w = (w - 1) + 1 from by omega, List.replicate_succ]]
  simp only [mulL, mulR, List.replicate_succ, List.cons_append]

end DTM

end Pnp
