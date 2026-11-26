/-
  文件：Pnp/Machine/WalkLC.lean
  File: Pnp/Machine/WalkLC.lean

  主题：**跨一个空白的左走找标记机 `walkLC`**——连续左移跳过 `some false`，遇到一个空白就
        「跨过」它继续跳过 `some false`，最终停在 `some true`（状态 1）或第二个空白（状态 3）。
  Topic: a left-walker that skips `some false`, CROSSES exactly one blank, keeps skipping
  `some false`, and halts on `some true` (state 1) or on a second blank (state 3).

  用途（docs/07 补记「#203 续」的 unary 乘法机）：乘法布局把源块与副本区用分隔空白隔开，
  「向左走回下一个未读源格」必须跨过这个分隔空白；`walkLT` 只能「遇空白即停」。
  Use: the unary multiplication machine separates the source block from the copy area by a
  blank; walking back to the next unread source cell must cross that blank.
-/

import Pnp.Machine.WalkLT

namespace Pnp

namespace DTM

/-- **跨一个空白的左走机**：状态 0 跳过 `some false`，遇空白跨过（左移）进状态 2；
    状态 2 继续跳过 `some false`，遇 `some true` ⇒ 状态 1（找到），遇空白 ⇒ 状态 3（耗尽）。
    Left-walker that crosses one blank; state 1 = found a `some true`, state 3 = exhausted. -/
def walkLC : DTM 6 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | some false => (⟨0, by omega⟩, some false, Dir.left)
       | some true => (⟨1, by omega⟩, some true, Dir.stay)
       | none => (⟨2, by omega⟩, none, Dir.left))
    | 2 => (match a with
       | some false => (⟨2, by omega⟩, some false, Dir.left)
       | some true => (⟨1, by omega⟩, some true, Dir.stay)
       | none => (⟨3, by omega⟩, none, Dir.stay))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 1
  reject := 3

/-- 非 1/3 状态一律不停机。 States other than 1/3 never halt. -/
theorem walkLC_halted_ne (st : Nat) (hst : st < 6) (h1 : st ≠ 1) (h3 : st ≠ 3)
    (t : Tape) : walkLC.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkLC.accept.val = 1 from rfl] at hv
    exact h1 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkLC.reject.val = 3 from rfl] at hv
    exact h3 hv

/-- `walkLC` 的单步运行套路。 The one-step idiom for `walkLC`. -/
theorem estepLC (st : Nat) (hst : st < 6) (a : Sym) (q' : Fin 6) (s : Sym) (d : Dir)
    (h : walkLC.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 1)
    (hne3 : st ≠ 3) :
    walkLC.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (walkLC_halted_ne st hst hne hne3 _)]
  exact stepConfig_of_step walkLC ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **跨空白的左行段**：左带 `m1` 个 `some false` 之后是空白，`m1 + 2` 步后跨过该空白，
    头落在空白左侧的 `x0` 上并进入状态 2。
    The crossing segment: skip `m1` cells, cross the blank, end on the cell left of it. -/
theorem walkLC_cross : ∀ (m1 : Nat) (x0 : Sym) (X' R : List Sym),
    walkLC.run (m1 + 2)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m1 (some false) ++ none :: x0 :: X') (some false :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 6),
          Tape.mk X' (x0 :: (none :: (List.replicate (m1 + 1) (some false) ++ R)))⟩
  | 0, x0, X', R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add walkLC 1 1]
      rw [estepLC 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [estepLC 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      simp
  | m1 + 1, x0, X', R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m1 + 1 + 2 : Nat) = 1 + (m1 + 2) from by omega,
        DTM.run_add walkLC 1 (m1 + 2)]
      rw [estepLC 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkLC_cross m1 x0 X' (some false :: R)]
      rw [replicate_succ_append (m1 + 1) (some false) R]

/-- **跨空白后走到 `some true`**：状态 2 跳过 `m2` 个 `some false`，`m2 + 2` 步后停在
    下一个 `some true` 上并接受（状态 1）。
    After crossing: skip `m2` cells and stop on the next `some true`. -/
theorem walkLC_skip_true : ∀ (m2 : Nat) (P R : List Sym),
    walkLC.run (m2 + 2)
      ⟨(⟨2, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m2 (some false) ++ some true :: P) (some false :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk P (some true :: (List.replicate (m2 + 1) (some false) ++ R))⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add walkLC 1 1]
      rw [estepLC 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [estepLC 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      simp
  | m2 + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m2 + 1 + 2 : Nat) = 1 + (m2 + 2) from by omega,
        DTM.run_add walkLC 1 (m2 + 2)]
      rw [estepLC 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkLC_skip_true m2 P (some false :: R)]
      rw [replicate_succ_append (m2 + 1) (some false) R]

/-- **跨空白后走到第二个空白（耗尽）**：状态 2 跳过 `m2` 个 `some false` 后读到空白，
    `m2 + 2` 步后停在空白上并进入状态 3。
    After crossing: skip `m2` cells and stop on the second blank (exhausted). -/
theorem walkLC_skip_none : ∀ (m2 : Nat) (P R : List Sym),
    walkLC.run (m2 + 2)
      ⟨(⟨2, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m2 (some false) ++ none :: P) (some false :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk P (none :: (List.replicate (m2 + 1) (some false) ++ R))⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add walkLC 1 1]
      rw [estepLC 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [estepLC 2 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      simp
  | m2 + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m2 + 1 + 2 : Nat) = 1 + (m2 + 2) from by omega,
        DTM.run_add walkLC 1 (m2 + 2)]
      rw [estepLC 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkLC_skip_none m2 P (some false :: R)]
      rw [replicate_succ_append (m2 + 1) (some false) R]

/-- **跨过去第一格就是目标**：状态 2 读到 `some true` 即一步接受。
    The single accept step when the cell after the separator is itself the target. -/
theorem walkLC_hit_true (P R : List Sym) :
    walkLC.run 1
      ⟨(⟨2, by omega⟩ : Fin 6), Tape.mk P (some true :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 6), Tape.mk P (some true :: R)⟩ := by
  rw [estepLC 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape

/-- **跨过去第一格就是空白**：状态 2 读到空白即一步进入状态 3（耗尽）。
    The single exhausted step when the cell after the separator is a blank. -/
theorem walkLC_hit_none (P R : List Sym) :
    walkLC.run 1
      ⟨(⟨2, by omega⟩ : Fin 6), Tape.mk P (none :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 6), Tape.mk P (none :: R)⟩ := by
  rw [estepLC 2 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape

/-- **整段（找到源格，源区上一格紧邻分隔）**：跨过分隔空白后第一格就是 `some true`。
    The whole crossing walk when the target is the first cell after the separator. -/
theorem walkLC_run_true0 (m1 : Nat) (P R : List Sym) :
    walkLC.run (m1 + 3)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m1 (some false) ++ none :: (some true :: P)) (some false :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk P (some true :: (none :: (List.replicate (m1 + 1) (some false) ++ R)))⟩ := by
  rw [show m1 + 3 = (m1 + 2) + 1 from by omega, DTM.run_add walkLC (m1 + 2) 1]
  rw [walkLC_cross m1 (some true) P R]
  rw [walkLC_hit_true P (none :: (List.replicate (m1 + 1) (some false) ++ R))]

/-- **整段（找到源格，源区至少一格已读）**：跨过分隔空白后先跳过 `m2 + 1 ≥ 1` 个
    `some false`，再停在 `some true` 上。
    The whole crossing walk with at least one `some false` after the separator. -/
theorem walkLC_run_true (m2 m1 : Nat) (P R : List Sym) :
    walkLC.run ((m1 + 2) + (m2 + 2))
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m1 (some false) ++
            none :: (List.replicate (m2 + 1) (some false) ++ some true :: P)) (some false :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk P (some true :: (List.replicate (m2 + 1) (some false) ++
            (none :: (List.replicate (m1 + 1) (some false) ++ R))))⟩ := by
  -- 把分隔后的 `m2 + 1` 个 `some false` 拆成「首格 + 其余」，才能套跨空白段
  have hsplit : List.replicate (m2 + 1) (some false)
      = some false :: List.replicate m2 (some false) := by
    rw [List.replicate_succ]
  rw [DTM.run_add walkLC (m1 + 2) (m2 + 2)]
  rw [hsplit, List.cons_append]
  rw [walkLC_cross m1 (some false) (List.replicate m2 (some false) ++ some true :: P) R]
  rw [walkLC_skip_true m2 P (none :: (List.replicate (m1 + 1) (some false) ++ R))]
  rw [← List.cons_append, ← hsplit]
  simp only [List.cons_append]

/-- **整段（源已耗尽，源区上一格紧邻分隔）**：跨过分隔空白后第一格就是第二个空白。
    The whole crossing walk ending on the blank right after the separator. -/
theorem walkLC_run_none0 (m1 : Nat) (P R : List Sym) :
    walkLC.run (m1 + 3)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m1 (some false) ++ none :: (none :: P)) (some false :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk P (none :: (none :: (List.replicate (m1 + 1) (some false) ++ R)))⟩ := by
  rw [show m1 + 3 = (m1 + 2) + 1 from by omega, DTM.run_add walkLC (m1 + 2) 1]
  rw [walkLC_cross m1 none P R]
  rw [walkLC_hit_none P (none :: (List.replicate (m1 + 1) (some false) ++ R))]

/-- **整段（源已耗尽，源区至少一格已读）**：跨过分隔空白后跳过 `m2 + 1 ≥ 1` 个
    `some false`，再停在第二个空白上（状态 3）。
    The whole crossing walk ending on a second blank with at least one cell between. -/
theorem walkLC_run_none (m2 m1 : Nat) (P R : List Sym) :
    walkLC.run ((m1 + 2) + (m2 + 2))
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m1 (some false) ++
            none :: (List.replicate (m2 + 1) (some false) ++ none :: P)) (some false :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk P (none :: (List.replicate (m2 + 1) (some false) ++
            (none :: (List.replicate (m1 + 1) (some false) ++ R))))⟩ := by
  have hsplit : List.replicate (m2 + 1) (some false)
      = some false :: List.replicate m2 (some false) := by
    rw [List.replicate_succ]
  rw [DTM.run_add walkLC (m1 + 2) (m2 + 2)]
  rw [hsplit, List.cons_append]
  rw [walkLC_cross m1 (some false) (List.replicate m2 (some false) ++ none :: P) R]
  rw [walkLC_skip_none m2 P (none :: (List.replicate (m1 + 1) (some false) ++ R))]
  rw [← List.cons_append, ← hsplit]
  simp only [List.cons_append]

end DTM

end Pnp
