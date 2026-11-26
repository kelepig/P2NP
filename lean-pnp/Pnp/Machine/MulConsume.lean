/-
  文件：Pnp/Machine/MulConsume.lean
  File: Pnp/Machine/MulConsume.lean

  主题：**乘法机的「消费一个 B 格 + 走到 `sepA`」相位机 `mulConsume`**——复制遍结束时头停在
        `sepB` 上（B 区在左、A 区在右）；本机沿 B 向左跳过未消费段，把紧贴已消费段的第一个
        未消费格改成 `some false`（消费标记），再右行越过 B、跨过 `sepB`，穿过整段 A（全
        `some false`），停在 `sepA` 上。
  Topic: the consume phase of the unary multiplication machine. Starting on `sepB` (after the
  copy pass), it walks left over B's unconsumed block, flips the first unconsumed cell next to
  the consumed block, then walks right across B and A and halts on `sepA`.

  布局（与 `mulCopy` 相同）：
    `L ++ [none, none] ++ B ++ [none] ++ A ++ [none] ++ acc ++ …`
                                 ^sepB        ^sepA
  B 的规范形（列表最近优先，即靠近 `sepB` 的一格在前）：`true^u ++ false^r`——**已消费段在远端**
  （`r` 为已消费格数、`u` 为未消费格数），故每轮只翻「未消费段的最后一格」，规范形保持
  （`u ↦ u - 1`、`r ↦ r + 1`）。
  B's canonical form (nearest first) is `true^u ++ false^r`: consumed cells pile up at the far
  end, so each round flips the last unconsumed cell and the form is preserved (`u ↦ u-1`,
  `r ↦ r+1`).

  状态：0 在 `sepB` 上左移进 B / 1 左行跳过 `some true`（越位一格再退回）/ 2 消费该格 /
        3 右行越过 B 并跨过 `sepB` / 4 右行穿过 A / 5 停机（停在 `sepA` 上）。
-/

import Pnp.Machine.MulCopy

namespace Pnp

namespace DTM

/-- 消费相位机（6 状态，5 为停机态）。 The consume-phase machine. -/
def mulConsume : DTM 6 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | none => (⟨1, by omega⟩, none, Dir.left)
       | _ => (⟨5, by omega⟩, a, Dir.stay))
    | 1 => (match a with
       | some true => (⟨1, by omega⟩, some true, Dir.left)
       | some false => (⟨2, by omega⟩, some false, Dir.right)
       | none => (⟨2, by omega⟩, none, Dir.right))
    | 2 => (⟨3, by omega⟩, some false, Dir.right)
    | 3 => (match a with
       | none => (⟨4, by omega⟩, none, Dir.right)
       | _ => (⟨3, by omega⟩, a, Dir.right))
    | 4 => (match a with
       | some false => (⟨4, by omega⟩, some false, Dir.right)
       | _ => (⟨5, by omega⟩, a, Dir.stay))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 5
  reject := 5

/-- 非 5 状态一律不停机。 States other than 5 never halt. -/
theorem mulConsume_halted_ne (st : Nat) (hst : st < 6) (h : st ≠ 5) (t : Tape) :
    mulConsume.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulConsume.accept.val = 5 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulConsume.reject.val = 5 from rfl] at hv
    exact h hv

/-- `mulConsume` 的单步运行套路。 The one-step idiom for `mulConsume`. -/
theorem estepMCn (st : Nat) (hst : st < 6) (a : Sym) (q' : Fin 6) (s : Sym) (d : Dir)
    (h : mulConsume.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 5) :
    mulConsume.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (mulConsume_halted_ne st hst hne _)]
  exact stepConfig_of_step mulConsume ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 1 左行跳过 `m` 个 `some true`（头仍停在最后一个 `some true` 上）。
    State 1 skips `m` trues leftwards and stays on the last one. -/
theorem mulConsume_skipLeft : ∀ (m : Nat) (P R : List Sym),
    mulConsume.run m
      ⟨(⟨1, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m (some true) ++ P) (some true :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk P (List.replicate m (some true) ++ (some true :: R))⟩
  | 0, P, R => by
      simp [DTM.run]
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show m + 1 = 1 + m from by omega]
      rw [DTM.run_add mulConsume 1 m]
      rw [estepMCn 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulConsume_skipLeft m P (some true :: R)]
      rw [replicate_succ_append m (some true) (some true :: R)]

/-- **状态 1 走到待消费格并消费**：左行跳过 `m` 个 `some true`、越位一格再退回，把最后一格
    改成 `some false` 并右移（`m + 3` 步）。
    Walk to the cell to consume and flip it: skip `m` trues, overshoot one cell, step back,
    write `some false` and move right, in `m + 3` steps. -/
theorem mulConsume_toFlip : ∀ (m r : Nat) (L R : List Sym),
    mulConsume.run (m + 3)
      ⟨(⟨1, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m (some true) ++
            (List.replicate r (some false) ++ (none :: (none :: L))))
          (some true :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk (some false ::
              (List.replicate r (some false) ++ (none :: (none :: L))))
            (List.replicate m (some true) ++ R)⟩
  | 0, r, L, R => by
      rw [show (0 + 3 : Nat) = 1 + (1 + 1) from by omega,
        DTM.run_add mulConsume 1 (1 + 1)]
      rcases r with _ | r'
      · -- `r = 0`：远端之外是预留空白
        simp only [List.replicate_zero, List.nil_append]
        rw [estepMCn 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [DTM.run_add mulConsume 1 1]
        rw [estepMCn 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [estepMCn 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
      · -- `r ≥ 1`：远端之外是已消费格
        rw [List.replicate_succ]
        simp only [List.replicate_zero, List.nil_append]
        rw [estepMCn 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [DTM.run_add mulConsume 1 1]
        rw [estepMCn 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [estepMCn 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
  | m + 1, r, L, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
      rw [show m + 1 + 3 = 1 + (m + 3) from by omega, DTM.run_add mulConsume 1 (m + 3)]
      rw [estepMCn 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulConsume_toFlip m r L (some true :: R)]
      rw [replicate_succ_append m (some true) R]

/-- 状态 3 右行越过 B（`m` 个 `some true`）并跨过 `sepB`（`m + 1` 步）。
    State 3 walks right over B's `m` trues and crosses `sepB`. -/
theorem mulConsume_skipR : ∀ (m : Nat) (P R : List Sym),
    mulConsume.run (m + 1)
      ⟨(⟨3, by omega⟩ : Fin 6),
        Tape.mk P (List.replicate m (some true) ++ (none :: R))⟩
      = ⟨(⟨4, by omega⟩ : Fin 6),
          Tape.mk (none :: (List.replicate m (some true) ++ P)) R⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 1 : Nat) = 1 from rfl]
      rw [estepMCn 3 (by omega) none _ _ _ (by rfl) P R (by omega)]
      etape
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
      rw [show m + 1 + 1 = 1 + (m + 1) from by omega, DTM.run_add mulConsume 1 (m + 1)]
      rw [estepMCn 3 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulConsume_skipR m (some true :: P) R]
      rw [replicate_succ_append m (some true) P]

/-- 状态 4 右行穿过 A（`m` 个 `some false`）并停在 `sepA` 上（`m + 1` 步）。
    State 4 walks right through A's `m` falses and halts on `sepA`. -/
theorem mulConsume_skipA : ∀ (m : Nat) (P R : List Sym),
    mulConsume.run (m + 1)
      ⟨(⟨4, by omega⟩ : Fin 6),
        Tape.mk P (List.replicate m (some false) ++ (none :: R))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (List.replicate m (some false) ++ P) (none :: R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 1 : Nat) = 1 from rfl]
      rw [estepMCn 4 (by omega) none _ _ _ (by rfl) P R (by omega)]
      etape
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
      rw [show m + 1 + 1 = 1 + (m + 1) from by omega, DTM.run_add mulConsume 1 (m + 1)]
      rw [estepMCn 4 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulConsume_skipA m (some false :: P) R]
      rw [replicate_succ_append m (some false) P]

/-- **消费一个 B 格并停在 `sepA`**：`a + 2u + 4` 步；未消费段 `u ↦ u - 1`。
    Consume one cell of `B` and halt on `sepA`, in `a + 2u + 4` steps; `u ↦ u-1`. -/
theorem mulConsume_run (a u r : Nat) (h : 1 ≤ u) (L M : List Sym) :
    mulConsume.run (a + 2 * u + 4)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate u (some true) ++
            (List.replicate r (some false) ++ (none :: (none :: L))))
          (none :: (List.replicate a (some false) ++ (none :: M)))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a (some false) ++
              (none :: (List.replicate (u - 1) (some true) ++
                (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))))
            (none :: M)⟩ := by
  rcases u with _ | u'
  · omega
  -- 未消费段非空：拆出首格，剩余 `u'` 格；顺带把已消费段与 `u - 1` 归约到显式形态
  simp only [List.replicate_succ, List.cons_append, Nat.add_sub_cancel]
  rw [show a + 2 * (u' + 1) + 4
      = 1 + ((u' + 3) + ((u' + 1) + (a + 1))) from by omega]
  rw [DTM.run_add mulConsume 1 ((u' + 3) + ((u' + 1) + (a + 1)))]
  -- 状态 0：从 `sepB` 左移进 B 的首格
  rw [estepMCn 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 1—2：走到待消费格并消费
  rw [DTM.run_add mulConsume (u' + 3) ((u' + 1) + (a + 1))]
  rw [mulConsume_toFlip u' r L
    (none :: (List.replicate a (some false) ++ (none :: M)))]
  -- 状态 3：越过 B 并跨过 `sepB`
  rw [DTM.run_add mulConsume (u' + 1) (a + 1)]
  rw [mulConsume_skipR u'
    (some false :: (List.replicate r (some false) ++ (none :: (none :: L))))
    (List.replicate a (some false) ++ (none :: M))]
  -- 状态 4：穿过 A 停在 `sepA` 上
  rw [mulConsume_skipA a
    (none :: (List.replicate u' (some true) ++
      (some false :: (List.replicate r (some false) ++ (none :: (none :: L)))))) M]

end DTM

end Pnp
