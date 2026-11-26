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

end DTM

end Pnp
