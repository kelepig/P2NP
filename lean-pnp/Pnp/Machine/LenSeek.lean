/-
  文件：Pnp/Machine/LenSeek.lean
  File: Pnp/Machine/LenSeek.lean

  主题：**按 3 对齐的找标记机 `seekMark3`**——在格编码块（每格 3 个符号，第 3 个是标记位）
        上从块首逐格右行，找到**第一个标记位为 `some true` 的格**并把该标记翻成
        `some false`（状态 3，接受）；整块标记都是 `some false` 时撞到块尾空白，
        进入状态 4（耗尽）。
  Topic: a 3-aligned marker seeker `seekMark3` over a cell-coded block (3 symbols per cell,
  the third being the marker). It walks right cell by cell, flips the first `some true`
  marker to `some false` (state 3), or hits the trailing blank when all markers are
  `some false` (state 4, exhausted).

  用途（#215，`T = |w|^k + k` 机内计算的「记 n = |w|」段）：unary 计数器逐格加一，
  每轮从块首重新扫描、消费一个「未计数」格的标记位；整块扫完后由别的相位把标记恢复。
  Use: the in-machine `n = |w|` counter — each round restarts at the block head, consumes one
  uncounted marker; markers are restored by a later phase.

  本文件给出：
    - 机器 `seekMark3 : DTM 5`（0/1/2 = 格内相位 1/2/3，3 = 找到，4 = 耗尽）；
    - 单格套路 `seekMark3_skip_cell`（标记 false ⇒ 3 步回到相位 0）与
      `seekMark3_hit_cell`（标记 true ⇒ 3 步翻成 false 并停）；
    - 整段扫描 `seekMark3_scan_false`（`3·|cs|` 步走完全 false 块，相位 0 停在块尾）、
      `seekMark3_scan_to_true`（跳过若干全 false 格后命中第一个 true 格）。
  This file gives the machine and its single-cell / whole-block run specs.
-/

import Pnp.Machine.SeekMark
import Pnp.Machine.CopyBlock
import Pnp.Machine.SimRound

namespace Pnp

namespace DTM

/-- **按 3 对齐的找标记机**：相位 0/1/2 依次读格内第 1/2/3 个符号；相位 2 读到标记
    `some true` 时写 `some false` 并进状态 3（接受）；任何相位读到空白进状态 4（耗尽）。
    A 3-aligned marker seeker; phases 0/1/2 read the three symbols of a cell in turn.
    A `some true` marker at phase 2 flips to `some false` and halts in state 3; a blank in
    any phase ends in state 4 (exhausted). -/
def seekMark3 : DTM 5 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | none => (⟨4, by omega⟩, none, Dir.stay)
       | some x => (⟨1, by omega⟩, some x, Dir.right))
    | 1 => (match a with
       | none => (⟨4, by omega⟩, none, Dir.stay)
       | some x => (⟨2, by omega⟩, some x, Dir.right))
    | 2 => (match a with
       | none => (⟨4, by omega⟩, none, Dir.stay)
       | some true => (⟨3, by omega⟩, some false, Dir.stay)
       | some false => (⟨0, by omega⟩, some false, Dir.right))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨3, by omega⟩
  reject := ⟨4, by omega⟩

/-- 非终止状态（既非 3 也非 4）一律不停机。 States other than 3/4 never halt. -/
theorem seekMark3_halted_ne (st : Nat) (hst : st < 5) (h3 : st ≠ 3) (h4 : st ≠ 4)
    (t : Tape) : seekMark3.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show seekMark3.accept.val = 3 from rfl] at hv
    exact h3 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show seekMark3.reject.val = 4 from rfl] at hv
    exact h4 hv

/-- `seekMark3` 的单步运行套路。 The one-step idiom for `seekMark3`. -/
theorem estepSK (st : Nat) (hst : st < 5) (a : Sym) (q' : Fin 5) (s : Sym) (d : Dir)
    (h : seekMark3.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 3)
    (hne2 : st ≠ 4) :
    seekMark3.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (seekMark3_halted_ne st hst hne hne2 _)]
  exact stepConfig_of_step seekMark3 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **跳过一格**：标记为 `some false` 的格，3 步后相位回到 0、头到下一格首符号；
    左带按「扫过符号的逆序」累积（`cellRev`）。
    Skipping a cell whose marker is `some false`: 3 steps return to phase 0; the left tape
    accumulates the reversed cell triple `cellRev`. -/
theorem seekMark3_skip_cell (a : Sym) (L R : List Sym) :
    seekMark3.run 3 ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk L (codeFst a :: codeSnd a :: some false :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L) R⟩ := by
  rcases hf : codeFst a with _ | b
  · exact absurd hf (codeFst_ne_none a)
  rcases hg : codeSnd a with _ | c
  · exact absurd hg (codeSnd_ne_none a)
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl, DTM.run_add seekMark3 1 (1 + 1)]
  rw [estepSK 0 (by omega) (some b) (⟨1, by omega⟩ : Fin 5) (some b) Dir.right
    (by rfl) _ _ (by omega) (by omega)]
  etape
  rw [show (1 + 1 : Nat) = 1 + 1 from rfl, DTM.run_add seekMark3 1 1]
  rw [estepSK 1 (by omega) (some c) (⟨2, by omega⟩ : Fin 5) (some c) Dir.right
    (by rfl) _ _ (by omega) (by omega)]
  etape
  rw [estepSK 2 (by omega) (some false) (⟨0, by omega⟩ : Fin 5) (some false) Dir.right
    (by rfl) _ _ (by omega) (by omega)]
  etape

/-- **命中的一格**：标记为 `some true` 的格，3 步后标记翻成 `some false`、状态 3、
    头停在该标记上；左带为 `[codeSnd, codeFst] ++ L`。
    Hitting a cell whose marker is `some true`: 3 steps flip the marker to `some false`
    and halt in state 3 with the head on the marker. -/
theorem seekMark3_hit_cell (a : Sym) (L R : List Sym) :
    seekMark3.run 3 ⟨(⟨0, by omega⟩ : Fin 5),
        Tape.mk L (codeFst a :: codeSnd a :: some true :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 5),
          Tape.mk (codeSnd a :: codeFst a :: L) (some false :: R)⟩ := by
  rcases hf : codeFst a with _ | b
  · exact absurd hf (codeFst_ne_none a)
  rcases hg : codeSnd a with _ | c
  · exact absurd hg (codeSnd_ne_none a)
  show seekMark3.run (1 + (1 + 1))
      ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk L (some b :: some c :: some true :: R)⟩
    = ⟨(⟨3, by omega⟩ : Fin 5), Tape.mk (some c :: some b :: L) (some false :: R)⟩
  rw [DTM.run_add seekMark3 1 (1 + 1)]
  rw [estepSK 0 (by omega) (some b) (⟨1, by omega⟩ : Fin 5) (some b) Dir.right
    (by rfl) _ _ (by omega) (by omega)]
  etape
  show seekMark3.run (1 + 1)
      ⟨(⟨1, by omega⟩ : Fin 5), Tape.mk (some b :: L) (some c :: some true :: R)⟩
    = ⟨(⟨3, by omega⟩ : Fin 5), Tape.mk (some c :: some b :: L) (some false :: R)⟩
  rw [DTM.run_add seekMark3 1 1]
  rw [estepSK 1 (by omega) (some c) (⟨2, by omega⟩ : Fin 5) (some c) Dir.right
    (by rfl) _ _ (by omega) (by omega)]
  etape
  rw [estepSK 2 (by omega) (some true) (⟨3, by omega⟩ : Fin 5) (some false) Dir.stay
    (by rfl) _ _ (by omega) (by omega)]
  etape

/-- 单格编码按标记位的显式形态。 Cell code by marker value. -/
theorem cellCode_false_form (a : Sym) :
    cellCode (a, false) = codeFst a :: codeSnd a :: some false :: [] := by
  rw [cellCode_false, symCode_eq]
  rfl

theorem cellCode_true_form (a : Sym) :
    cellCode (a, true) = codeFst a :: codeSnd a :: some true :: [] := by
  rw [cellCode_true, symCode_eq]
  rfl

/-- **整段全 false 扫描**：`3·|cs|` 步走完全 false 的格块，相位 0 停在块尾；
    左带为「扫过符号的逆序」`(codeCells cs).reverse ++ L`。
    Scanning a whole all-`false` block: `3·|cs|` steps leave phase 0 at the block end,
    with the reversed code on the left tape. -/
theorem seekMark3_scan_false : ∀ (cs : List (Sym × Bool)) (L P : List Sym),
    (∀ c ∈ cs, c.2 = false) →
    seekMark3.run (3 * cs.length)
      ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk L (codeCells cs ++ P)⟩
      = ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk ((codeCells cs).reverse ++ L) P⟩
  | [], L, P, _ => by
      simp [codeCells, DTM.run]
  | (a, m) :: cs, L, P, h => by
      have hm : m = false := by
        have := h (a, m) (by simp)
        simpa using this
      subst hm
      have hsplit : codeCells ((a, false) :: cs) ++ P
          = codeFst a :: codeSnd a :: some false :: (codeCells cs ++ P) := by
        rw [codeCells_cons, cellCode_false_form]
        simp
      rw [hsplit]
      rw [show 3 * ((a, false) :: cs).length = 3 + 3 * cs.length from by
        simp [List.length_cons]; omega]
      rw [DTM.run_add seekMark3 3 (3 * cs.length)]
      rw [seekMark3_skip_cell a L (codeCells cs ++ P)]
      rw [seekMark3_scan_false cs (some false :: codeSnd a :: codeFst a :: L) P
        (by intro c' hc'; exact h c' (by simp [hc']))]
      rw [show codeCells ((a, false) :: cs) = cellCode (a, false) ++ codeCells cs from
        codeCells_cons _ _]
      rw [cellCode_false_form]
      simp [List.reverse_append, List.append_assoc]

/-- **扫描到第一个 true 格**：前缀 `ps` 全 false，其后是标记 `some true` 的格 `a`；
    `3·|ps| + 3` 步后状态 3、`a` 的标记翻成 `some false`。
    Scanning past an all-`false` prefix `ps` to the first `true`-marked cell `a`:
    `3·|ps| + 3` steps end in state 3 with the marker flipped. -/
theorem seekMark3_scan_to_true : ∀ (ps : List (Sym × Bool)) (a : Sym)
    (L R : List Sym),
    (∀ p ∈ ps, p.2 = false) →
    seekMark3.run (3 * ps.length + 3)
      ⟨(⟨0, by omega⟩ : Fin 5), Tape.mk L (codeCells ps ++ cellCode (a, true) ++ R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 5),
          Tape.mk (codeSnd a :: codeFst a :: ((codeCells ps).reverse ++ L))
            (some false :: R)⟩
  | [], a, L, R, _ => by
      rw [show codeCells ([] : List (Sym × Bool)) = [] from rfl]
      simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add]
      rw [cellCode_true_form]
      simp only [List.cons_append, List.nil_append]
      rw [seekMark3_hit_cell a L R]
      simp
  | (b, m) :: ps, a, L, R, h => by
      have hm : m = false := by
        have := h (b, m) (by simp)
        simpa using this
      subst hm
      have hsplit : codeCells ((b, false) :: ps) ++ cellCode (a, true) ++ R
          = codeFst b :: codeSnd b :: some false ::
              (codeCells ps ++ cellCode (a, true) ++ R) := by
        rw [codeCells_cons, cellCode_false_form]
        simp
      rw [hsplit]
      rw [show 3 * ((b, false) :: ps).length + 3 = 3 + (3 * ps.length + 3) from by
        simp [List.length_cons]; omega]
      rw [DTM.run_add seekMark3 3 (3 * ps.length + 3)]
      rw [seekMark3_skip_cell b L (codeCells ps ++ cellCode (a, true) ++ R)]
      rw [seekMark3_scan_to_true ps a (some false :: codeSnd b :: codeFst b :: L) R
        (by intro p' hp'; exact h p' (by simp [hp']))]
      rw [show codeCells ((b, false) :: ps) = cellCode (b, false) ++ codeCells ps from
        codeCells_cons _ _]
      rw [cellCode_false_form]
      simp [List.reverse_append, List.append_assoc]

end DTM

end Pnp
