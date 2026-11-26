/-
  文件：Pnp/Machine/MulRestore.lean
  File: Pnp/Machine/MulRestore.lean

  主题：**乘法机的「恢复 A + 回起点」相位机 `mulRestore`**——消费遍结束时头停在 `sepA` 上、
        A 整段已标记（全 `some false`）；本机左行把 A 的每格改回 `some true`，再右行回到 A 的
        最右格（即下一轮复制遍的起点）。
  Topic: the restore phase of the unary multiplication machine. After the consume phase the head
  sits on `sepA` and all of A is marked (`some false`); this machine walks left flipping every
  cell of A back to `some true`, then walks right to A's rightmost cell, the start of the next
  copy pass.

  布局（与 `mulCopy` 相同）：
    `L ++ [none, none] ++ B ++ [none] ++ A ++ [none] ++ acc ++ …`
                                 ^sep1        ^sepA
  状态：0 在 `sepA` 上左移进 A / 1 左行逐格把 `some false` 改回 `some true` /
        2 右行跳过 A 的 `some true` / 3 停机（头落在 A 的最右格上）。
-/

import Pnp.Machine.MulConsume

namespace Pnp

namespace DTM

/-- 恢复相位机（4 状态，3 为停机态）。 The restore-phase machine. -/
def mulRestore : DTM 5 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | none => (⟨1, by omega⟩, none, Dir.left)
       | _ => (⟨3, by omega⟩, a, Dir.stay))
    | 1 => (match a with
       | some false => (⟨1, by omega⟩, some true, Dir.left)
       | none => (⟨2, by omega⟩, none, Dir.right)
       | some true => (⟨3, by omega⟩, some true, Dir.stay))
    | 2 => (match a with
       | some true => (⟨2, by omega⟩, some true, Dir.right)
       | none => (⟨3, by omega⟩, none, Dir.left)
       | some false => (⟨3, by omega⟩, some false, Dir.stay))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 4
  reject := 4

/-- 非 3 状态一律不停机。 States other than 3 never halt. -/
theorem mulRestore_halted_ne (st : Nat) (hst : st < 5) (h : st ≠ 4) (t : Tape) :
    mulRestore.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulRestore.accept.val = 4 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulRestore.reject.val = 4 from rfl] at hv
    exact h hv

/-- `mulRestore` 的单步运行套路。 The one-step idiom for `mulRestore`. -/
theorem estepMR (st : Nat) (hst : st < 5) (a : Sym) (q' : Fin 5) (s : Sym) (d : Dir)
    (h : mulRestore.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 4) :
    mulRestore.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (mulRestore_halted_ne st hst hne _)]
  exact stepConfig_of_step mulRestore ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 1 左行把 `m` 个 `some false` 逐格改回 `some true`（头停在下一个待改格上）。
    State 1 walks left flipping `m` falses back to trues. -/
theorem mulRestore_flip : ∀ (m : Nat) (P R : List Sym),
    mulRestore.run m
      ⟨(⟨1, by omega⟩ : Fin 5),
        Tape.mk (List.replicate m (some false) ++ P) (some false :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 5),
          Tape.mk P (some false :: (List.replicate m (some true) ++ R))⟩
  | 0, P, R => by
      simp [DTM.run]
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show m + 1 = 1 + m from by omega]
      rw [DTM.run_add mulRestore 1 m]
      rw [estepMR 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulRestore_flip m P (some true :: R)]
      rw [replicate_succ_append m (some true) R]

/-- 状态 2 右行跳过 A 的 `some true`（左带已累积 `m` 格、右带首格显式给出 + `m'` 格），
    读 `sepA` 后左移回 A 的最右格（`m' + 2` 步）。
    State 2 skips A's trues (`m` already on the left, one explicit plus `m'` on the right) and,
    on reading `sepA`, steps back onto A's rightmost cell, in `m' + 2` steps. -/
theorem mulRestore_skipT : ∀ (m m' : Nat) (P Q : List Sym),
    mulRestore.run (m' + 2)
      ⟨(⟨2, by omega⟩ : Fin 5),
        Tape.mk (List.replicate m (some true) ++ (none :: P))
          (some true :: (List.replicate m' (some true) ++ (none :: Q)))⟩
      = ⟨(⟨3, by omega⟩ : Fin 5),
          Tape.mk (List.replicate (m + m') (some true) ++ (none :: P))
            (some true :: (none :: Q))⟩
  | m, 0, P, Q => by
      rw [show (0 + 2 : Nat) = 1 + 1 from by omega, DTM.run_add mulRestore 1 1]
      rw [estepMR 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp only [List.replicate_zero, List.nil_append]
      rw [estepMR 2 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp only [List.replicate_zero, List.nil_append, Nat.add_zero]
  | m, m' + 1, P, Q => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
      rw [show (m' + 1 + 2 : Nat) = 1 + (m' + 2) from by omega,
        DTM.run_add mulRestore 1 (m' + 2)]
      rw [estepMR 2 (by omega) (some true) _ _ _ (by rfl)
        (List.replicate m (some true) ++ (none :: P))
        (some true :: (List.replicate m' (some true) ++ (none :: Q))) (by omega)]
      etape
      rw [cons_replicate_append (some true) m (none :: P)]
      rw [replicate_succ_append m (some true) (none :: P)]
      rw [mulRestore_skipT (m + 1) m' P Q]
      rw [show m + 1 + m' = m + (m' + 1) from by omega]

/-- **恢复 A 并回到起点**：`2a + 3` 步；头最后落在 A 的最右格上（下一轮复制遍的起点）。
    Restore A and return to the start, in `2a + 3` steps; the head ends on A's rightmost cell. -/
theorem mulRestore_run (a : Nat) (h : 1 ≤ a) (P Q : List Sym) :
    mulRestore.run (2 * a + 3)
      ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk (List.replicate a (some false) ++ (none :: P)) (none :: Q)⟩
      = ⟨(⟨3, by omega⟩ : Fin 5),
          Tape.mk (List.replicate (a - 1) (some true) ++ (none :: P))
            (some true :: (none :: Q))⟩ := by
  rcases a with _ | a'
  · omega
  simp only [List.replicate_succ, List.cons_append, Nat.add_sub_cancel]
  -- 步数分解：1 + a' + 1 + 1 + (a' + 2)
  rw [show 2 * (a' + 1) + 3 = 1 + (a' + (1 + (1 + (a' + 2)))) from by omega]
  rw [DTM.run_add mulRestore 1 (a' + (1 + (1 + (a' + 2))))]
  -- 状态 0：从 `sepA` 左移进 A 的最右格
  rw [estepMR 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 1：把 A 的 `a'` 格改回 `some true`（还剩最左一格）
  rw [DTM.run_add mulRestore a' (1 + (1 + (a' + 2)))]
  rw [mulRestore_flip a' (none :: P) (none :: Q)]
  -- 状态 1：改回最后一格并左移跨上 `sep1`
  rw [DTM.run_add mulRestore 1 (1 + (a' + 2))]
  rw [estepMR 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 1 读到 `sep1` 空白：右移进 A 的最左格
  rw [DTM.run_add mulRestore 1 (a' + 2)]
  rw [estepMR 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 2：右行回到 A 的最右格
  conv =>
    lhs
    rw [show (none :: P : List Sym) = List.replicate 0 (some true) ++ (none :: P) from by
      simp]
  rw [mulRestore_skipT 0 a' P Q]
  simp only [Nat.zero_add]

end DTM

end Pnp
