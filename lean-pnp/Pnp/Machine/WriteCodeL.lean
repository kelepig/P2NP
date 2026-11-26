/-
  文件：Pnp/Machine/WriteCodeL.lean
  File: Pnp/Machine/WriteCodeL.lean

  主题：符号相关的左向格编码写入机——读当前格符号 `a`，把它的格编码
        `[codeFst a, codeSnd a, m]` 写到左侧连续三格（`m` 为给定标记符号），
        读写头停在标记格上。
  Topic: a symbol-dependent writer that reads the current symbol `a` and writes its cell
  code `[codeFst a, codeSnd a, m]` into the three cells to the left, ending on the mark.

  机制：左向写入必须「先左移、再写入」交替进行（同一格写+移会把旧符号夹进写入串）。
  读到的符号通过状态编码记住：状态 `6c + k` 表示「已记住第 `c` 种情形、处于第 `k` 步」。
  Mechanism: leftward writes alternate move-then-write so that written symbols stay
  contiguous. The read symbol is remembered in the state (`6c + k`, case `c`, step `k`).

  本文件给出：
    - `symCase` / `caseSym`（符号的三种情形编码与反查）与 `caseSym_symCase`；
    - `writeCodeL`（机器定义，32 状态：工作态 `0–14`、入口 `24`、停机 `31`）；
    - `stepConfig_of_lit`（显式状态/符号下的一步归约）与 `writeCodeL_run`（6 步后的纸带形态）。
  This file gives the case encoding, the machine, an explicit one-step reduction lemma,
  and its exact run shape.
-/

import Pnp.Machine.WriteCell

namespace Pnp

namespace DTM

/-- 符号的三情形编号：空白 0、`some false` 1、`some true` 2。 -/
abbrev symCase : Sym → Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- 情形编号反查符号（`symCase` 的左逆）；越界返回空白。 -/
abbrev caseSym : Nat → Sym
  | 0 => none
  | 1 => some false
  | 2 => some true
  | _ => none

/-- 反查后回到原符号。 -/
theorem caseSym_symCase (a : Sym) : caseSym (symCase a) = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- 情形编号不超过 2。 -/
theorem symCase_le (a : Sym) : symCase a ≤ 2 := by
  cases a with
  | none => simp [symCase]
  | some b => cases b <;> simp [symCase]

/-- **左向格编码写入机**：读当前符号 `a`，向左写 `codeFst a`、`codeSnd a`、`m` 三个符号，
    停在标记格 `m` 上。状态布局：`0–14` 为工作态 `6c + k`（`c` 情形、`k` 步数），
    `24` 为入口（记住符号情形并左移），`31` 为停机态。
    Leftward cell-code writer: writes `codeFst a`, `codeSnd a`, `m` into the three cells
    to the left and halts on the mark. States: `6c+k` work, `24` entry, `31` halt. -/
def writeCodeL (m : Sym) : DTM 32 where
  step := fun st a =>
    if _h1 : st.val = 24 then
      -- 入口：记住符号情形，写回原符号并左移
      (⟨6 * symCase a, by have := symCase_le a; omega⟩, a, Dir.left)
    else if _h2 : st.val = 31 then
      (st, a, Dir.stay)
    else if h3 : st.val % 6 = 0 then
      -- 写编码首符号（离头最远的那个）
      (⟨st.val + 1, by have := st.isLt; omega⟩,
        codeFst (caseSym (st.val / 6)), Dir.stay)
    else if _h4 : st.val % 6 = 1 then
      (⟨st.val + 1, by have := st.isLt; omega⟩, a, Dir.left)
    else if _h5 : st.val % 6 = 2 then
      (⟨st.val + 1, by have := st.isLt; omega⟩,
        codeSnd (caseSym (st.val / 6)), Dir.stay)
    else if _h6 : st.val % 6 = 3 then
      (⟨st.val + 1, by have := st.isLt; omega⟩, a, Dir.left)
    else
      (⟨31, by omega⟩, m, Dir.stay)
  start := ⟨24, by omega⟩
  accept := ⟨31, by omega⟩
  reject := ⟨31, by omega⟩

/-- **单步转移的显式形态**：状态与读入符号都写成显式值时，一步转移可按定义直接归约。
    这条引理把投影（`c.state`、`c.tape`）换成显式值，避开核归约在「投影套 `dite`」上的停滞。
    Explicit one-step form: with explicit state and read symbol, `stepConfig` reduces by
    definition. It replaces projections by their values, which kernel reduction handles. -/
theorem stepConfig_of_lit {q : Nat} (M : DTM q) (st : Fin q) (a : Sym) (L R : List Sym)
    (q' : Fin q) (s : Sym) (d : Dir) (T : Tape)
    (h : M.step st a = (q', s, d))
    (hT : ((Tape.mk L (a :: R)).write s).move d = T) :
    M.stepConfig ⟨st, Tape.mk L (a :: R)⟩ = ⟨q', T⟩ := by
  simp only [DTM.stepConfig, Tape.read, List.headD, h, hT]

/-- **写入机的运行结果**：读头处符号为 `a`、左侧至少三格时，6 步后左侧三格已写成
    格编码（`m` 在最靠里、`codeSnd a` 居中、`codeFst a` 最靠外），头停在标记格。
    Exact run shape: after 6 steps the cell code of `a` sits in the three cells to the
    left and the head rests on the mark. -/
theorem writeCodeL_run (m a : Sym) (l0 l1 l2 : Sym) (L'' R : List Sym) :
    (writeCodeL m).run 6 ⟨(writeCodeL m).start, Tape.mk (l0 :: l1 :: l2 :: L'') (a :: R)⟩
      = ⟨(writeCodeL m).accept, Tape.mk L'' (m :: codeSnd a :: codeFst a :: a :: R)⟩ := by
  -- 按符号三情形展开：状态编号与写入符号此时全是字面量，每步给一次显式转移；
  -- 停机判定与纸带演化（写 + 移）都由 `rfl` 直接归约。
  -- Unfold the three cases; states and symbols are literals, so every step is explicit
  -- and both the halting check and the tape evolution reduce by `rfl`.
  cases a with
  | none =>
      -- 空白：状态 24 → 0 → 1 → 2 → 3 → 4 → 31
      rw [DTM.run_succ_of_not_halted _ 5 _ (by rfl)]
      rw [stepConfig_of_lit _ (writeCodeL m).start (none) (l0 :: l1 :: l2 :: L'') (R) ⟨0, by omega⟩
            (none) Dir.left (Tape.mk (l1 :: l2 :: L'') (l0 :: none :: R)) (by rfl)
            (by rfl : ((Tape.mk (l0 :: l1 :: l2 :: L'') (none :: R)).write (none)).move Dir.left
              = Tape.mk (l1 :: l2 :: L'') (l0 :: none :: R))]
      rw [DTM.run_succ_of_not_halted _ 4 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨0, by omega⟩ (l0) (l1 :: l2 :: L'') (none :: R) ⟨1, by omega⟩
            (codeFst (none)) Dir.stay (Tape.mk (l1 :: l2 :: L'') (codeFst (none) :: none :: R)) (by rfl)
            (by rfl : ((Tape.mk (l1 :: l2 :: L'') (l0 :: none :: R)).write (codeFst (none))).move Dir.stay
              = Tape.mk (l1 :: l2 :: L'') (codeFst (none) :: none :: R))]
      rw [DTM.run_succ_of_not_halted _ 3 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨1, by omega⟩ (codeFst (none)) (l1 :: l2 :: L'') (none :: R) ⟨2, by omega⟩
            (codeFst (none)) Dir.left (Tape.mk (l2 :: L'') (l1 :: codeFst (none) :: none :: R)) (by rfl)
            (by rfl : ((Tape.mk (l1 :: l2 :: L'') (codeFst (none) :: none :: R)).write (codeFst (none))).move Dir.left
              = Tape.mk (l2 :: L'') (l1 :: codeFst (none) :: none :: R))]
      rw [DTM.run_succ_of_not_halted _ 2 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨2, by omega⟩ (l1) (l2 :: L'') (codeFst (none) :: none :: R) ⟨3, by omega⟩
            (codeSnd (none)) Dir.stay (Tape.mk (l2 :: L'') (codeSnd (none) :: codeFst (none) :: none :: R)) (by rfl)
            (by rfl : ((Tape.mk (l2 :: L'') (l1 :: codeFst (none) :: none :: R)).write (codeSnd (none))).move Dir.stay
              = Tape.mk (l2 :: L'') (codeSnd (none) :: codeFst (none) :: none :: R))]
      rw [DTM.run_succ_of_not_halted _ 1 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨3, by omega⟩ (codeSnd (none)) (l2 :: L'') (codeFst (none) :: none :: R) ⟨4, by omega⟩
            (codeSnd (none)) Dir.left (Tape.mk L'' (l2 :: codeSnd (none) :: codeFst (none) :: none :: R)) (by rfl)
            (by rfl : ((Tape.mk (l2 :: L'') (codeSnd (none) :: codeFst (none) :: none :: R)).write (codeSnd (none))).move Dir.left
              = Tape.mk L'' (l2 :: codeSnd (none) :: codeFst (none) :: none :: R))]
      rw [DTM.run_succ_of_not_halted _ 0 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨4, by omega⟩ (l2) (L'') (codeSnd (none) :: codeFst (none) :: none :: R) ⟨31, by omega⟩
            (m) Dir.stay (Tape.mk L'' (m :: codeSnd (none) :: codeFst (none) :: none :: R)) (by rfl)
            (by rfl : ((Tape.mk L'' (l2 :: codeSnd (none) :: codeFst (none) :: none :: R)).write (m)).move Dir.stay
              = Tape.mk L'' (m :: codeSnd (none) :: codeFst (none) :: none :: R))]
      rfl
  | some b =>
      cases b with
      | false =>
          -- `some false`：状态 24 → 6 → 7 → 8 → 9 → 10 → 31
      rw [DTM.run_succ_of_not_halted _ 5 _ (by rfl)]
      rw [stepConfig_of_lit _ (writeCodeL m).start (some false) (l0 :: l1 :: l2 :: L'') (R) ⟨6, by omega⟩
            (some false) Dir.left (Tape.mk (l1 :: l2 :: L'') (l0 :: some false :: R)) (by rfl)
            (by rfl : ((Tape.mk (l0 :: l1 :: l2 :: L'') (some false :: R)).write (some false)).move Dir.left
              = Tape.mk (l1 :: l2 :: L'') (l0 :: some false :: R))]
      rw [DTM.run_succ_of_not_halted _ 4 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨6, by omega⟩ (l0) (l1 :: l2 :: L'') (some false :: R) ⟨7, by omega⟩
            (codeFst (some false)) Dir.stay (Tape.mk (l1 :: l2 :: L'') (codeFst (some false) :: some false :: R)) (by rfl)
            (by rfl : ((Tape.mk (l1 :: l2 :: L'') (l0 :: some false :: R)).write (codeFst (some false))).move Dir.stay
              = Tape.mk (l1 :: l2 :: L'') (codeFst (some false) :: some false :: R))]
      rw [DTM.run_succ_of_not_halted _ 3 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨7, by omega⟩ (codeFst (some false)) (l1 :: l2 :: L'') (some false :: R) ⟨8, by omega⟩
            (codeFst (some false)) Dir.left (Tape.mk (l2 :: L'') (l1 :: codeFst (some false) :: some false :: R)) (by rfl)
            (by rfl : ((Tape.mk (l1 :: l2 :: L'') (codeFst (some false) :: some false :: R)).write (codeFst (some false))).move Dir.left
              = Tape.mk (l2 :: L'') (l1 :: codeFst (some false) :: some false :: R))]
      rw [DTM.run_succ_of_not_halted _ 2 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨8, by omega⟩ (l1) (l2 :: L'') (codeFst (some false) :: some false :: R) ⟨9, by omega⟩
            (codeSnd (some false)) Dir.stay (Tape.mk (l2 :: L'') (codeSnd (some false) :: codeFst (some false) :: some false :: R)) (by rfl)
            (by rfl : ((Tape.mk (l2 :: L'') (l1 :: codeFst (some false) :: some false :: R)).write (codeSnd (some false))).move Dir.stay
              = Tape.mk (l2 :: L'') (codeSnd (some false) :: codeFst (some false) :: some false :: R))]
      rw [DTM.run_succ_of_not_halted _ 1 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨9, by omega⟩ (codeSnd (some false)) (l2 :: L'') (codeFst (some false) :: some false :: R) ⟨10, by omega⟩
            (codeSnd (some false)) Dir.left (Tape.mk L'' (l2 :: codeSnd (some false) :: codeFst (some false) :: some false :: R)) (by rfl)
            (by rfl : ((Tape.mk (l2 :: L'') (codeSnd (some false) :: codeFst (some false) :: some false :: R)).write (codeSnd (some false))).move Dir.left
              = Tape.mk L'' (l2 :: codeSnd (some false) :: codeFst (some false) :: some false :: R))]
      rw [DTM.run_succ_of_not_halted _ 0 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨10, by omega⟩ (l2) (L'') (codeSnd (some false) :: codeFst (some false) :: some false :: R) ⟨31, by omega⟩
            (m) Dir.stay (Tape.mk L'' (m :: codeSnd (some false) :: codeFst (some false) :: some false :: R)) (by rfl)
            (by rfl : ((Tape.mk L'' (l2 :: codeSnd (some false) :: codeFst (some false) :: some false :: R)).write (m)).move Dir.stay
              = Tape.mk L'' (m :: codeSnd (some false) :: codeFst (some false) :: some false :: R))]
      rfl
      | true =>
          -- `some true`：状态 24 → 12 → 13 → 14 → 15 → 16 → 31
      rw [DTM.run_succ_of_not_halted _ 5 _ (by rfl)]
      rw [stepConfig_of_lit _ (writeCodeL m).start (some true) (l0 :: l1 :: l2 :: L'') (R) ⟨12, by omega⟩
            (some true) Dir.left (Tape.mk (l1 :: l2 :: L'') (l0 :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (l0 :: l1 :: l2 :: L'') (some true :: R)).write (some true)).move Dir.left
              = Tape.mk (l1 :: l2 :: L'') (l0 :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 4 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨12, by omega⟩ (l0) (l1 :: l2 :: L'') (some true :: R) ⟨13, by omega⟩
            (codeFst (some true)) Dir.stay (Tape.mk (l1 :: l2 :: L'') (codeFst (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (l1 :: l2 :: L'') (l0 :: some true :: R)).write (codeFst (some true))).move Dir.stay
              = Tape.mk (l1 :: l2 :: L'') (codeFst (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 3 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨13, by omega⟩ (codeFst (some true)) (l1 :: l2 :: L'') (some true :: R) ⟨14, by omega⟩
            (codeFst (some true)) Dir.left (Tape.mk (l2 :: L'') (l1 :: codeFst (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (l1 :: l2 :: L'') (codeFst (some true) :: some true :: R)).write (codeFst (some true))).move Dir.left
              = Tape.mk (l2 :: L'') (l1 :: codeFst (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 2 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨14, by omega⟩ (l1) (l2 :: L'') (codeFst (some true) :: some true :: R) ⟨15, by omega⟩
            (codeSnd (some true)) Dir.stay (Tape.mk (l2 :: L'') (codeSnd (some true) :: codeFst (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (l2 :: L'') (l1 :: codeFst (some true) :: some true :: R)).write (codeSnd (some true))).move Dir.stay
              = Tape.mk (l2 :: L'') (codeSnd (some true) :: codeFst (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 1 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨15, by omega⟩ (codeSnd (some true)) (l2 :: L'') (codeFst (some true) :: some true :: R) ⟨16, by omega⟩
            (codeSnd (some true)) Dir.left (Tape.mk L'' (l2 :: codeSnd (some true) :: codeFst (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (l2 :: L'') (codeSnd (some true) :: codeFst (some true) :: some true :: R)).write (codeSnd (some true))).move Dir.left
              = Tape.mk L'' (l2 :: codeSnd (some true) :: codeFst (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 0 _ (by rfl)]
      rw [stepConfig_of_lit _ ⟨16, by omega⟩ (l2) (L'') (codeSnd (some true) :: codeFst (some true) :: some true :: R) ⟨31, by omega⟩
            (m) Dir.stay (Tape.mk L'' (m :: codeSnd (some true) :: codeFst (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk L'' (l2 :: codeSnd (some true) :: codeFst (some true) :: some true :: R)).write (m)).move Dir.stay
              = Tape.mk L'' (m :: codeSnd (some true) :: codeFst (some true) :: some true :: R))]
      rfl

end DTM

end Pnp
