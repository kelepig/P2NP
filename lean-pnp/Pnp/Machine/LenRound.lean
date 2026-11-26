/-
  文件：Pnp/Machine/LenRound.lean
  File: Pnp/Machine/LenRound.lean

  主题：**长度计数的一轮组合机 `lenRound`**——把「找下一个未计数格」(`seekMark3`) 与
        「计数器 +1」(`cntWrite`) 装成一臺机器，供外层逐轮驱动（每轮消耗一个标记、计数器加一）。
  Topic: the length-counting round machine `lenRound`, combining the marker seeker `seekMark3`
  with the counter-write phase `cntWrite` into one machine driven round by round.

  状态布局（共 11 态）：
    0/1/2 = `seekMark3` 的格内相位；3 = 找到标记（改接到 cnt 入口 5）；4 = 块耗尽（改接到 10 = 停机）；
    5/6/7/8 = `cntWrite` 的 0/1/2/3 相位；8 见非空白 ⇒ 直接回 0（seek 起点，即一轮结束）；
    10 = 接受 = 拒绝（耗尽停机）；9 未使用。
  Layout (11 states): 0/1/2 = the seek phases; 3 = marker hit (redirect to 5); 4 = block exhausted
  (redirect to the halting state 10); 5/6/7/8 = the counter-write phases; 8 on a non-blank returns
  to 0 (round end); 10 = accept = reject (exhausted halt).

  本文件给出：
    - 机器 `lenRound : DTM 11`；
    - 单步套路 `lenRound_halted_ne` / `estepLR` 与三个改接步 `lenRound_switch` /
      `lenRound_exhaust` / `lenRound_back`；
    - seek 段的组合机版扫描：`lenRound_skip_cell` / `lenRound_hit_cell` /
      `lenRound_scan_false` / `lenRound_scan_to_true`，以及「扫描 + 改接」`lenRound_seek_hit`。
  This file gives the machine, the one-step idiom, the three redirect steps, and the seek-phase
  scan lemmas at the composite level.
-/

import Pnp.Machine.LenCount

namespace Pnp

namespace DTM

/-- **长度计数一轮组合机**：0–2 seek 相位；3 命中 ⇒ 5；4 耗尽 ⇒ 10（停机）；5–8 cnt 相位；
    8 见非空白 ⇒ 回 0（一轮结束）。9 未使用。
    The round machine: seek phases 0–2, hit 3 → 5, exhausted 4 → 10 (halt), counter phases 5–8,
    and 8 on a non-blank → 0 (round end). -/
def lenRound : DTM 11 where
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
    | 3 => (⟨5, by omega⟩, a, Dir.stay)
    | 4 => (⟨10, by omega⟩, a, Dir.stay)
    | 5 => (match a with
       | none => (⟨6, by omega⟩, none, Dir.left)
       | some x => (⟨5, by omega⟩, some x, Dir.left))
    | 6 => (match a with
       | some true => (⟨6, by omega⟩, some true, Dir.left)
       | _ => (⟨7, by omega⟩, some true, Dir.stay))
    | 7 => (match a with
       | some true => (⟨7, by omega⟩, some true, Dir.right)
       | _ => (⟨8, by omega⟩, none, Dir.right))
    | 8 => (match a with
       | none => (⟨8, by omega⟩, none, Dir.right)
       | some x => (⟨0, by omega⟩, some x, Dir.stay))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨10, by omega⟩
  reject := ⟨10, by omega⟩

/-- 组合机在 10 以外的状态上不停机。 The composite never halts outside state 10. -/
theorem lenRound_halted_ne (st : Nat) (hst : st < 11) (h10 : st ≠ 10) (t : Tape) :
    lenRound.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show lenRound.accept.val = 10 from rfl] at hv
    exact h10 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show lenRound.reject.val = 10 from rfl] at hv
    exact h10 hv

/-- `lenRound` 的单步套路。 The one-step idiom for `lenRound`. -/
theorem estepLR (st : Nat) (hst : st < 11) (a : Sym) (q' : Fin 11) (s : Sym) (d : Dir)
    (h : lenRound.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 10) :
    lenRound.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (lenRound_halted_ne st hst hne _)]
  exact stepConfig_of_step lenRound ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **命中改接**：seek 的命中态 3 一步转入 cnt 入口 5（纸带不动）。
    The hit redirect: state 3 steps into the counter entry 5 (tape unchanged). -/
theorem lenRound_switch (a : Sym) (M R : List Sym) :
    lenRound.run 1 ⟨(⟨3, by omega⟩ : Fin 11), Tape.mk M (a :: R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 11), Tape.mk M (a :: R)⟩ := by
  rw [estepLR 3 (by omega) a (⟨5, by omega⟩ : Fin 11) a Dir.stay (by rfl) M R (by omega)]
  etape

/-- **耗尽改接**：seek 的耗尽态 4 一步进入停机态 10（纸带不动）。
    The exhaustion redirect: state 4 steps into the halting state 10 (tape unchanged). -/
theorem lenRound_exhaust (a : Sym) (M R : List Sym) :
    lenRound.run 1 ⟨(⟨4, by omega⟩ : Fin 11), Tape.mk M (a :: R)⟩
      = ⟨(⟨10, by omega⟩ : Fin 11), Tape.mk M (a :: R)⟩ := by
  rw [estepLR 4 (by omega) a (⟨10, by omega⟩ : Fin 11) a Dir.stay (by rfl) M R (by omega)]
  etape

/-- **一轮结束**：cnt 相位 8 见非空白即回 seek 起点 0（纸带不动，一步同时完成 cnt 的回相位）。
    The round end: the counter phase 8 on a non-blank returns to the seek start 0 (tape unchanged). -/
theorem lenRound_back (x : Sym) (L R : List Sym) (hx : x ≠ none) :
    lenRound.run 1 ⟨(⟨8, by omega⟩ : Fin 11), Tape.mk L (x :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk L (x :: R)⟩ := by
  rcases hx' : x with _ | y
  · exact absurd hx' hx
  rw [estepLR 8 (by omega) (some y) (⟨0, by omega⟩ : Fin 11) (some y) Dir.stay
    (by rfl) L R (by omega)]
  etape

/-- **组合机跳过一格**：标记为 `some false` 的格，3 步后相位回到 0、头到下一格首符号；
    左带按扫过符号的逆序累积。
    Skipping a cell whose marker is `some false`: 3 steps return to phase 0. -/
theorem lenRound_skip_cell (a : Sym) (L R : List Sym) :
    lenRound.run 3 ⟨(⟨0, by omega⟩ : Fin 11),
        Tape.mk L (codeFst a :: codeSnd a :: some false :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 11),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L) R⟩ := by
  rcases hf : codeFst a with _ | b
  · exact absurd hf (codeFst_ne_none a)
  rcases hg : codeSnd a with _ | c
  · exact absurd hg (codeSnd_ne_none a)
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl, DTM.run_add lenRound 1 (1 + 1)]
  rw [estepLR 0 (by omega) (some b) (⟨1, by omega⟩ : Fin 11) (some b) Dir.right
    (by rfl) _ _ (by omega)]
  etape
  rw [show (1 + 1 : Nat) = 1 + 1 from rfl, DTM.run_add lenRound 1 1]
  rw [estepLR 1 (by omega) (some c) (⟨2, by omega⟩ : Fin 11) (some c) Dir.right
    (by rfl) _ _ (by omega)]
  etape
  rw [estepLR 2 (by omega) (some false) (⟨0, by omega⟩ : Fin 11) (some false) Dir.right
    (by rfl) _ _ (by omega)]
  etape

/-- **组合机命中的一格**：标记为 `some true` 的格，3 步后标记翻成 `some false`、状态 3。
    Hitting a cell whose marker is `some true`: 3 steps flip the marker and end in state 3. -/
theorem lenRound_hit_cell (a : Sym) (L R : List Sym) :
    lenRound.run 3 ⟨(⟨0, by omega⟩ : Fin 11),
        Tape.mk L (codeFst a :: codeSnd a :: some true :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 11),
          Tape.mk (codeSnd a :: codeFst a :: L) (some false :: R)⟩ := by
  rcases hf : codeFst a with _ | b
  · exact absurd hf (codeFst_ne_none a)
  rcases hg : codeSnd a with _ | c
  · exact absurd hg (codeSnd_ne_none a)
  show lenRound.run (1 + (1 + 1))
      ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk L (some b :: some c :: some true :: R)⟩
    = ⟨(⟨3, by omega⟩ : Fin 11), Tape.mk (some c :: some b :: L) (some false :: R)⟩
  rw [DTM.run_add lenRound 1 (1 + 1)]
  rw [estepLR 0 (by omega) (some b) (⟨1, by omega⟩ : Fin 11) (some b) Dir.right
    (by rfl) _ _ (by omega)]
  etape
  show lenRound.run (1 + 1)
      ⟨(⟨1, by omega⟩ : Fin 11), Tape.mk (some b :: L) (some c :: some true :: R)⟩
    = ⟨(⟨3, by omega⟩ : Fin 11), Tape.mk (some c :: some b :: L) (some false :: R)⟩
  rw [DTM.run_add lenRound 1 1]
  rw [estepLR 1 (by omega) (some c) (⟨2, by omega⟩ : Fin 11) (some c) Dir.right
    (by rfl) _ _ (by omega)]
  etape
  rw [estepLR 2 (by omega) (some true) (⟨3, by omega⟩ : Fin 11) (some false) Dir.stay
    (by rfl) _ _ (by omega)]
  etape

/-- **组合机整段全 false 扫描**：`3·|cs|` 步走完全 false 块，相位 0 停在块尾；
    左带为扫过符号的逆序。
    Scanning a whole all-`false` block: `3·|cs|` steps leave phase 0 at the block end. -/
theorem lenRound_scan_false : ∀ (cs : List (Sym × Bool)) (L P : List Sym),
    (∀ c ∈ cs, c.2 = false) →
    lenRound.run (3 * cs.length)
      ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk L (codeCells cs ++ P)⟩
      = ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk ((codeCells cs).reverse ++ L) P⟩
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
      rw [DTM.run_add lenRound 3 (3 * cs.length)]
      rw [lenRound_skip_cell a L (codeCells cs ++ P)]
      rw [lenRound_scan_false cs (some false :: codeSnd a :: codeFst a :: L) P
        (by intro c' hc'; exact h c' (by simp [hc']))]
      rw [show codeCells ((a, false) :: cs) = cellCode (a, false) ++ codeCells cs from
        codeCells_cons _ _]
      rw [cellCode_false_form]
      simp [List.reverse_append, List.append_assoc]

/-- **组合机扫描到第一个 true 格**：前缀 `ps` 全 false，其后是标记 `some true` 的格 `a`；
    `3·|ps| + 3` 步后状态 3（命中）、`a` 的标记翻成 `some false`。
    Scanning past an all-`false` prefix to the first `true`-marked cell, ending in state 3. -/
theorem lenRound_scan_to_true : ∀ (ps : List (Sym × Bool)) (a : Sym) (L R : List Sym),
    (∀ p ∈ ps, p.2 = false) →
    lenRound.run (3 * ps.length + 3)
      ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk L (codeCells ps ++ cellCode (a, true) ++ R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 11),
          Tape.mk (codeSnd a :: codeFst a :: ((codeCells ps).reverse ++ L))
            (some false :: R)⟩
  | [], a, L, R, _ => by
      rw [show codeCells ([] : List (Sym × Bool)) = [] from rfl]
      simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add]
      rw [cellCode_true_form]
      simp only [List.cons_append, List.nil_append]
      rw [lenRound_hit_cell a L R]
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
      rw [DTM.run_add lenRound 3 (3 * ps.length + 3)]
      rw [lenRound_skip_cell b L (codeCells ps ++ cellCode (a, true) ++ R)]
      rw [lenRound_scan_to_true ps a (some false :: codeSnd b :: codeFst b :: L) R
        (by intro p' hp'; exact h p' (by simp [hp']))]
      rw [show codeCells ((b, false) :: ps) = cellCode (b, false) ++ codeCells ps from
        codeCells_cons _ _]
      rw [cellCode_false_form]
      simp [List.reverse_append, List.append_assoc]

/-- **扫描 + 命中改接**：`3·|ps| + 4` 步后进入 cnt 入口 5，左带为已扫格的逆序码。
    Scan plus hit redirect: after `3·|ps| + 4` steps the machine sits in the counter entry 5. -/
theorem lenRound_seek_hit (ps : List (Sym × Bool)) (a : Sym) (L R : List Sym)
    (hps : ∀ p ∈ ps, p.2 = false) :
    lenRound.run (3 * ps.length + 3 + 1)
      ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk L (codeCells ps ++ cellCode (a, true) ++ R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 11),
          Tape.mk (codeSnd a :: codeFst a :: ((codeCells ps).reverse ++ L))
            (some false :: R)⟩ := by
  rw [DTM.run_add lenRound (3 * ps.length + 3) 1]
  rw [lenRound_scan_to_true ps a L R hps]
  rw [lenRound_switch (some false) _ R]

/-! ### cnt 半段：组合机版的计数器相位（状态 5/6/7/8） -/

/-- 状态 5 读非空白：左移一格。
    State 5 on a non-blank moves left. -/
theorem lenRound_step5_move (x : Sym) (L' : List Sym) (a : Sym) (R : List Sym)
    (ha : a ≠ none) :
    lenRound.run 1 ⟨(⟨5, by omega⟩ : Fin 11), Tape.mk (x :: L') (a :: R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 11), Tape.mk L' (x :: a :: R)⟩ := by
  rcases ha' : a with _ | b
  · exact absurd ha' ha
  rw [estepLR 5 (by omega) (some b) (⟨5, by omega⟩ : Fin 11) (some b) Dir.left
    (by rfl) _ _ (by omega)]
  etape

/-- 状态 5 读空白：跨分隔进状态 6。
    State 5 on a blank crosses the separator into state 6. -/
theorem lenRound_step5_blank (x : Sym) (L' : List Sym) (R : List Sym) :
    lenRound.run 1 ⟨(⟨5, by omega⟩ : Fin 11), Tape.mk (x :: L') (none :: R)⟩
      = ⟨(⟨6, by omega⟩ : Fin 11), Tape.mk L' (x :: none :: R)⟩ := by
  rw [estepLR 5 (by omega) none (⟨6, by omega⟩ : Fin 11) none Dir.left
    (by rfl) _ _ (by omega)]
  etape

/-- **组合机越过格块到分隔空白**：`|Lb|+1` 步，状态仍在 5。
    Crossing the block up to the separator, `|Lb|+1` steps, still in state 5. -/
theorem lenRound_walkBlock : ∀ (Lb : List Sym) (k : Nat) (F : List Sym) (a : Sym)
    (R : List Sym), (∀ x ∈ Lb, x ≠ none) → a ≠ none →
    lenRound.run (Lb.length + 1)
      ⟨(⟨5, by omega⟩ : Fin 11),
        Tape.mk (Lb ++ none :: List.replicate k (some true) ++ none :: F) (a :: R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 11),
          Tape.mk (List.replicate k (some true) ++ none :: F) (none :: Lb.reverse ++ a :: R)⟩
  | [], k, F, a, R, _, ha => by
      rw [show ([].length + 1 : Nat) = 1 from rfl]
      simp only [List.nil_append, List.cons_append]
      rw [lenRound_step5_move none (List.replicate k (some true) ++ none :: F) a R ha]
      simp
  | x :: xs, k, F, a, R, hLb, ha => by
      have hx : x ≠ none := hLb x (by simp)
      rw [show (x :: xs).length + 1 = 1 + (xs.length + 1) from by
        rw [List.length_cons]; omega]
      rw [DTM.run_add lenRound 1 (xs.length + 1)]
      simp only [List.cons_append]
      rw [lenRound_step5_move x
        (xs ++ none :: List.replicate k (some true) ++ none :: F) a R ha]
      rw [lenRound_walkBlock xs k F x (a :: R)
        (by intro y hy; exact hLb y (by simp [hy])) hx]
      rw [List.reverse_cons]
      simp [List.append_assoc]

/-- **组合机进入计数器（`k ≥ 1`）**：状态 5 → 6，一步。
    Entering a nonempty counter: one step from state 5 to 6. -/
theorem lenRound_enterCounter (k : Nat) (F P : List Sym) (hk : 1 ≤ k) :
    lenRound.run 1
      ⟨(⟨5, by omega⟩ : Fin 11),
        Tape.mk (List.replicate k (some true) ++ none :: F) (none :: P)⟩
      = ⟨(⟨6, by omega⟩ : Fin 11),
          Tape.mk (List.replicate (k - 1) (some true) ++ none :: F) (some true :: none :: P)⟩ := by
  have hrep : List.replicate k (some true)
      = some true :: List.replicate (k - 1) (some true) := by
    match k with
    | 0 => omega
    | _ + 1 => rfl
  rw [hrep]
  simp only [List.cons_append]
  rw [lenRound_step5_blank]

/-- **组合机越过格块（`k ≥ 1`）**：`|Lb|+2` 步，落在计数器最近的 `some true` 上（状态 6）。
    Crossing the block and separator with a nonempty counter, `|Lb|+2` steps. -/
theorem lenRound_walkBlock_pos (Lb : List Sym) (k : Nat) (F : List Sym) (a : Sym)
    (R : List Sym) (hk : 1 ≤ k) (hLb : ∀ x ∈ Lb, x ≠ none) (ha : a ≠ none) :
    lenRound.run (Lb.length + 2)
      ⟨(⟨5, by omega⟩ : Fin 11),
        Tape.mk (Lb ++ none :: List.replicate k (some true) ++ none :: F) (a :: R)⟩
      = ⟨(⟨6, by omega⟩ : Fin 11),
          Tape.mk (List.replicate (k - 1) (some true) ++ none :: F)
            (some true :: none :: Lb.reverse ++ a :: R)⟩ := by
  rw [show Lb.length + 2 = (Lb.length + 1) + 1 from by omega]
  rw [DTM.run_add lenRound (Lb.length + 1) 1]
  rw [lenRound_walkBlock Lb k F a R hLb ha]
  simp only [List.cons_append]
  rw [lenRound_enterCounter k F (Lb.reverse ++ a :: R) hk]

/-- **组合机越过格块（`k = 0`）**：`|Lb|+2` 步，跨过分隔与前沿空白（状态 6）。
    Crossing the block and separator with an empty counter, `|Lb|+2` steps. -/
theorem lenRound_walkBlock_zero : ∀ (Lb : List Sym) (F : List Sym) (a : Sym)
    (R : List Sym), (∀ x ∈ Lb, x ≠ none) → a ≠ none →
    lenRound.run (Lb.length + 2)
      ⟨(⟨5, by omega⟩ : Fin 11), Tape.mk (Lb ++ none :: none :: F) (a :: R)⟩
      = ⟨(⟨6, by omega⟩ : Fin 11),
          Tape.mk F (none :: none :: Lb.reverse ++ a :: R)⟩
  | [], F, a, R, _, ha => by
      rw [show ([].length + 2 : Nat) = 1 + 1 from rfl, DTM.run_add lenRound 1 1]
      simp only [List.nil_append]
      rw [lenRound_step5_move none (none :: F) a R ha]
      simp only [List.cons_append]
      rw [lenRound_step5_blank none F (a :: R)]
      simp
  | x :: xs, F, a, R, hLb, ha => by
      have hx : x ≠ none := hLb x (by simp)
      rw [show (x :: xs).length + 2 = 1 + (xs.length + 2) from by
        rw [List.length_cons]; omega]
      rw [DTM.run_add lenRound 1 (xs.length + 2)]
      simp only [List.cons_append]
      rw [lenRound_step5_move x (xs ++ none :: none :: F) a R ha]
      rw [lenRound_walkBlock_zero xs F x (a :: R)
        (by intro y hy; exact hLb y (by simp [hy])) hx]
      rw [List.reverse_cons]
      simp [List.append_assoc]

/-- **组合机越过计数器并写一个 `true`**：状态 6 → 7，`j+2` 步。
    Walking over the counter and writing one `true`: state 6 → 7 in `j+2` steps. -/
theorem lenRound_skipCounter (j : Nat) (F M : List Sym) :
    lenRound.run (j + 2)
      ⟨(⟨6, by omega⟩ : Fin 11),
        Tape.mk (List.replicate j (some true) ++ none :: F) (some true :: M)⟩
      = ⟨(⟨7, by omega⟩ : Fin 11),
          Tape.mk F (List.replicate (j + 2) (some true) ++ M)⟩ := by
  induction j generalizing F M with
  | zero =>
      rw [show (List.replicate 0 (some true) ++ none :: F) = none :: F from rfl]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add lenRound 1 1]
      rw [estepLR 6 (by omega) (some true) (⟨6, by omega⟩ : Fin 11) (some true) Dir.left
        (by rfl) _ _ (by omega)]
      etape
      rw [estepLR 6 (by omega) none (⟨7, by omega⟩ : Fin 11) (some true) Dir.stay
        (by rfl) _ _ (by omega)]
      etape
      simp
  | succ j ih =>
      rw [show List.replicate (j + 1) (some true) ++ none :: F
          = some true :: (List.replicate j (some true) ++ none :: F) from rfl]
      rw [show (j + 1 + 2 : Nat) = 1 + (j + 2) from by omega]
      rw [DTM.run_add lenRound 1 (j + 2)]
      rw [estepLR 6 (by omega) (some true) (⟨6, by omega⟩ : Fin 11) (some true) Dir.left
        (by rfl) _ _ (by omega)]
      etape
      rw [ih F (some true :: M)]
      rw [show 1 + (j + 2) = (j + 2) + 1 from by omega]
      rw [rep_cons_merge (j + 2) (some true) M]

/-- **组合机在空计数器上写第一个 `true`**：状态 6 → 7，一步。
    Writing the first `true` on an empty counter: one step, state 6 → 7. -/
theorem lenRound_write0 (F M : List Sym) :
    lenRound.run 1 ⟨(⟨6, by omega⟩ : Fin 11), Tape.mk F (none :: M)⟩
      = ⟨(⟨7, by omega⟩ : Fin 11), Tape.mk F (some true :: M)⟩ := by
  rw [estepLR 6 (by omega) none (⟨7, by omega⟩ : Fin 11) (some true) Dir.stay
    (by rfl) _ _ (by omega)]
  etape

/-- **组合机右行越回并跨分隔**：状态 7 → 8，`m+1` 步。
    Walking right over the counter and crossing the separator: state 7 → 8 in `m+1` steps. -/
theorem lenRound_skipTrue (m : Nat) (L F : List Sym) :
    lenRound.run (m + 1)
      ⟨(⟨7, by omega⟩ : Fin 11),
        Tape.mk L (List.replicate m (some true) ++ none :: F)⟩
      = ⟨(⟨8, by omega⟩ : Fin 11),
          Tape.mk (none :: List.replicate m (some true) ++ L) F⟩ := by
  induction m generalizing L F with
  | zero =>
      rw [show List.replicate 0 (some true) ++ none :: F = none :: F from rfl]
      rw [show (0 + 1 : Nat) = 1 from rfl]
      rw [estepLR 7 (by omega) none (⟨8, by omega⟩ : Fin 11) none Dir.right
        (by rfl) _ _ (by omega)]
      etape
      simp
  | succ m ih =>
      rw [show List.replicate (m + 1) (some true) ++ none :: F
          = some true :: (List.replicate m (some true) ++ none :: F) from rfl]
      rw [show (m + 1 + 1 : Nat) = 1 + (m + 1) from by omega]
      rw [DTM.run_add lenRound 1 (m + 1)]
      rw [estepLR 7 (by omega) (some true) (⟨7, by omega⟩ : Fin 11) (some true) Dir.right
        (by rfl) _ _ (by omega)]
      etape
      rw [ih (some true :: L) F]
      rw [show List.replicate (m + 1) (some true)
          = some true :: List.replicate m (some true) from rfl]
      simp only [List.cons_append]
      rw [← rep_cons_swap m (some true) L]
      simp only [List.cons_append]

/-- **回相位 0（前缀版）**：只看头符号是否非空白，头左侧已扫符号可非空。
    前缀内符号须非空白（用于块内位置任意时的最后一步）。
    The prefix form of `lenRound_back`: only the head symbol matters; the already-scanned prefix
    may be nonempty (all its symbols must be non-blank). -/
theorem lenRound_back_prefix (P : List Sym) (y : Sym) (R L : List Sym)
    (hP : ∀ z ∈ P, z ≠ none) (hy : y ≠ none) :
    lenRound.run 1 ⟨(⟨8, by omega⟩ : Fin 11), Tape.mk L (P ++ y :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 11), Tape.mk L (P ++ y :: R)⟩ := by
  cases P with
  | nil => exact lenRound_back y L R hy
  | cons x xs => exact lenRound_back x L (xs ++ y :: R) (hP x (by simp))

/-- **长度计数的一整轮**：`3r + 4 + (2 + 3r + 2k + 6)` 步内
    （a）扫描跳过全 `false` 前缀、把第一个 `some true` 标记格改写成 `some false`；
    （b）越过块与分隔空白，计数器 `k ↦ k+1`，右行越回；
    终态 `⟨0, 块左端, 计数器 ++ 空白〉`，块与计数器的形状保持，故可逐轮迭代。
    One whole length-counting round: scan past the all-`false` prefix, flip the first `true`
    marker to `false`, grow the counter by one, and walk back to the block's left end.
    The block and counter shapes are preserved, so rounds compose. -/
theorem lenRound_run (ps : List (Sym × Bool)) (k : Nat) (F : List Sym) (a : Sym)
    (R : List Sym) (hps : ∀ p ∈ ps, p.2 = false) :
    lenRound.run (3 * ps.length + 4 + ((2 + 3 * ps.length) + 2 * k + 6))
      ⟨(⟨0, by omega⟩ : Fin 11),
        Tape.mk (none :: List.replicate k (some true) ++ none :: F)
          (codeCells ps ++ cellCode (a, true) ++ R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 11),
          Tape.mk (none :: List.replicate (k + 1) (some true) ++ F)
            (codeCells ps ++ cellCode (a, false) ++ R)⟩ := by
  -- 块头两格码与已扫格编码都非空白（walkBlock / back 的前提）
  have hcells : ∀ x ∈ codeCells ps, x ≠ none := codeCells_ne_none ps
  have hLb : ∀ x ∈ (codeSnd a :: codeFst a :: (codeCells ps).reverse), x ≠ none := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with h | h | h
    · rw [h]; exact codeSnd_ne_none a
    · rw [h]; exact codeFst_ne_none a
    · exact hcells x (List.mem_reverse.mp h)
  have hrev : ∀ z ∈ (codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse, z ≠ none := by
    intro z hz
    exact hLb z (List.mem_reverse.mp hz)
  have hcf : some false ≠ none := by decide
  -- 块头码的长度：两格头码 + 已扫格的 3 倍长编码
  have hLblen : (codeSnd a :: codeFst a :: (codeCells ps).reverse).length
      = 2 + 3 * ps.length := by
    rw [List.length_cons, List.length_cons, List.length_reverse, codeCells_length]
    omega
  -- 终态右带归一：块头两格的反向码 + 命中格的标记 = 原格编码（标记已翻 false）
  have hfin : (codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
        ++ some false :: R = codeCells ps ++ cellCode (a, false) ++ R := by
    rw [List.reverse_cons, List.reverse_cons, List.reverse_reverse, cellCode_false_form]
    simp [List.append_assoc]
  -- 1) seek 半段：扫描到第一个 some true 格、改接进状态 5
  rw [show 3 * ps.length + 4 + ((2 + 3 * ps.length) + 2 * k + 6)
      = (3 * ps.length + 3 + 1) + ((2 + 3 * ps.length) + 2 * k + 6) from by omega]
  rw [DTM.run_add lenRound (3 * ps.length + 3 + 1) ((2 + 3 * ps.length) + 2 * k + 6)]
  rw [lenRound_seek_hit ps a (none :: List.replicate k (some true) ++ none :: F) R hps]
  -- 左带整理成「块头码 ++ 分隔空白 ++ 计数器 ++ 分隔空白」的左结合形态
  rw [show codeSnd a :: codeFst a :: ((codeCells ps).reverse
        ++ (none :: List.replicate k (some true) ++ none :: F))
      = ((codeSnd a :: codeFst a :: (codeCells ps).reverse)
          ++ (none :: List.replicate k (some true))) ++ (none :: F) from by
    simp only [List.cons_append, List.append_assoc]]
  rcases k with _ | k
  · -- `k = 0`：越过格块（含前沿空白）→ 写第一个 true → 右行越回 → 回相位 0
    rw [show (2 + 3 * ps.length) + 2 * 0 + 6
        = ((2 + 3 * ps.length) + 2) + (1 + 2 + 1) from by omega]
    rw [DTM.run_add lenRound ((2 + 3 * ps.length) + 2) (1 + 2 + 1)]
    rw [List.append_assoc]
    rw [show (none :: List.replicate 0 (some true)) ++ none :: F = none :: none :: F from rfl]
    rw [show 2 + 3 * ps.length + 2
        = (codeSnd a :: codeFst a :: (codeCells ps).reverse).length + 2 from by
      rw [hLblen]]
    rw [lenRound_walkBlock_zero (codeSnd a :: codeFst a :: (codeCells ps).reverse) F
      (some false) R hLb hcf]
    rw [DTM.run_add lenRound 1 (2 + 1)]
    simp only [List.cons_append]
    rw [lenRound_write0 F (none :: ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
      ++ some false :: R))]
    rw [DTM.run_add lenRound 2 1]
    rw [← show List.replicate 1 (some true)
          ++ none :: ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
              ++ some false :: R)
        = some true :: none :: ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
              ++ some false :: R) from rfl]
    rw [lenRound_skipTrue 1 F ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
      ++ some false :: R)]
    rw [show (0 : Nat) + 1 = 1 from rfl]
    rw [lenRound_back_prefix ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse)
      (some false) R (none :: List.replicate 1 (some true) ++ F) hrev hcf]
    rw [hfin]
    rfl
  · -- `k + 1`：越过格块 → 计数器加一 → 右行越回 → 回相位 0
    rw [show (2 + 3 * ps.length) + 2 * (k + 1) + 6
        = ((2 + 3 * ps.length) + 2) + ((k + 2) + ((k + 3) + 1)) from by omega]
    rw [DTM.run_add lenRound ((2 + 3 * ps.length) + 2) ((k + 2) + ((k + 3) + 1))]
    rw [show 2 + 3 * ps.length + 2
        = (codeSnd a :: codeFst a :: (codeCells ps).reverse).length + 2 from by
      rw [hLblen]]
    rw [lenRound_walkBlock_pos (codeSnd a :: codeFst a :: (codeCells ps).reverse) (k + 1) F
      (some false) R (by omega) hLb hcf]
    rw [show k + 1 - 1 = k from by omega]
    rw [DTM.run_add lenRound (k + 2) ((k + 3) + 1)]
    simp only [List.cons_append]
    rw [lenRound_skipCounter k F (none :: ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
      ++ some false :: R))]
    rw [DTM.run_add lenRound (k + 2 + 1) 1]
    rw [lenRound_skipTrue (k + 2) F ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse
      ++ some false :: R)]
    rw [show (k + 1) + 1 = k + 2 from by omega]
    rw [lenRound_back_prefix ((codeSnd a :: codeFst a :: (codeCells ps).reverse).reverse)
      (some false) R (none :: List.replicate (k + 2) (some true) ++ F) hrev hcf]
    rw [hfin]
    rfl

end DTM

end Pnp
