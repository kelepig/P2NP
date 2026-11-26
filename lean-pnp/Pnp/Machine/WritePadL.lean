/-
  文件：Pnp/Machine/WritePadL.lean
  File: Pnp/Machine/WritePadL.lean

  主题：区域左半部分的**标记相位**机器——在读写头所在格写头标记 `some true`，
        再向左写当前格的 `codeSnd`、`codeFst` 两个编码符号（5 步，14 状态）。
  Topic: the marker phase of the left half of a region: writes the head marker
  `some true` in the current cell, then `codeSnd` and `codeFst` of the cell's symbol to
  the left (14 states, 5 steps).

  与 `writeStrL`（左向常量串写入机，#148）组合即得完整的「左半区域」写入机：
  本机写标记与当前格两符号码，`writeStrL (padStr T)` 续写 `3(T+1)` 个空白编码符号。
  Composed with `writeStrL (padStr T)` this yields the full left-half region writer; the
  composition is left to `seqComp` (#149 记录拆分理由)。

  状态布局：0 入口；`4c+1 … 4c+4`（`c = symCase a` 为符号情形）；13 停机。
  States: 0 entry; `4c+1 … 4c+4` for case `c`; 13 halts.
-/

import Pnp.Machine.WriteStrL

namespace Pnp

namespace DTM

/-- 区域左侧预留空白段的符号串：`3(T+1)` 个编码空白符号（留给 `writeStrL` 续写）。 -/
def padStr (T : Nat) : List Sym := List.replicate (3 * (T + 1)) (some false)

/-- **标记相位机**：写头标记，向左写当前符号的两个编码符号；14 状态、5 步。
    Marker phase: marker, then the symbol's two code symbols to the left. -/
def writeMarkFstSnd : DTM 14 where
  step := fun st a =>
    if _ : st.val = 0 then
      -- 入口：在当前格写标记并左移；状态编码符号情形（4c+1）
      (⟨4 * symCase a + 1, by have := symCase_le a; omega⟩, some true, Dir.left)
    else if _ : st.val = 1 then (⟨2, by omega⟩, codeSnd (caseSym 0), Dir.stay)
    else if _ : st.val = 2 then (⟨3, by omega⟩, a, Dir.left)
    else if _ : st.val = 3 then (⟨4, by omega⟩, codeFst (caseSym 0), Dir.stay)
    else if _ : st.val = 4 then (⟨13, by omega⟩, a, Dir.stay)
    else if _ : st.val = 5 then (⟨6, by omega⟩, codeSnd (caseSym 1), Dir.stay)
    else if _ : st.val = 6 then (⟨7, by omega⟩, a, Dir.left)
    else if _ : st.val = 7 then (⟨8, by omega⟩, codeFst (caseSym 1), Dir.stay)
    else if _ : st.val = 8 then (⟨13, by omega⟩, a, Dir.stay)
    else if _ : st.val = 9 then (⟨10, by omega⟩, codeSnd (caseSym 2), Dir.stay)
    else if _ : st.val = 10 then (⟨11, by omega⟩, a, Dir.left)
    else if _ : st.val = 11 then (⟨12, by omega⟩, codeFst (caseSym 2), Dir.stay)
    else if _ : st.val = 12 then (⟨13, by omega⟩, a, Dir.stay)
    else (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨13, by omega⟩
  reject := ⟨13, by omega⟩


/-- **标记相位机的运行结果**：头左侧有两格可用时，5 步后纸带右带为
    `[codeFst a][codeSnd a][some true]…`（原头格符号被标记覆盖），头停在左数第二格（`codeFst a` 所在格）。
    Exact run shape: 5 steps produce `[codeFst a][codeSnd a][some true]…`（原头格符号被标记覆盖） to the right
    with the head on `codeFst a`. -/
theorem writeMarkFstSnd_run (a x1 x2 : Sym) (ls2 L R : List Sym) :
    (writeMarkFstSnd).run 5
      ⟨(writeMarkFstSnd).start, Tape.mk (x1 :: x2 :: ls2 ++ L) (a :: R)⟩
      = ⟨(writeMarkFstSnd).accept,
          Tape.mk (ls2 ++ L) (codeFst a :: codeSnd a :: some true :: R)⟩ := by
  -- 按符号三情形展开；状态与写入符号都是字面量
  cases a with
  | none =>
      rw [DTM.run_succ_of_not_halted _ 4 _ (by rfl)]
      rw [stepConfig_of_lit _ (writeMarkFstSnd).start (none)
            (x1 :: x2 :: ls2 ++ L) (R) ⟨1, by omega⟩ (some true) Dir.left (Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x1 :: x2 :: ls2 ++ L) (none :: R)).write (some true)).move Dir.left = Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 3 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨1, by omega⟩ : Fin 14) (x1)
            (x2 :: ls2 ++ L) (some true :: R) ⟨2, by omega⟩ (codeSnd (none)) Dir.stay (Tape.mk (x2 :: ls2 ++ L) (codeSnd (none) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)).write (codeSnd (none))).move Dir.stay = Tape.mk (x2 :: ls2 ++ L) (codeSnd (none) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 2 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨2, by omega⟩ : Fin 14) (codeSnd (none))
            (x2 :: ls2 ++ L) (some true :: R) ⟨3, by omega⟩ (codeSnd (none)) Dir.left (Tape.mk (ls2 ++ L) (x2 :: codeSnd (none) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x2 :: ls2 ++ L) (codeSnd (none) :: some true :: R)).write (codeSnd (none))).move Dir.left = Tape.mk (ls2 ++ L) (x2 :: codeSnd (none) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 1 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨3, by omega⟩ : Fin 14) (x2)
            (ls2 ++ L) (codeSnd (none) :: some true :: R) ⟨4, by omega⟩ (codeFst (none)) Dir.stay (Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls2 ++ L) (x2 :: codeSnd (none) :: some true :: R)).write (codeFst (none))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 0 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨4, by omega⟩ : Fin 14) (codeFst (none))
            (ls2 ++ L) (codeSnd (none) :: some true :: R) ⟨13, by omega⟩ (codeFst (none)) Dir.stay (Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)).write (codeFst (none))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R))]
      rfl
  | some b =>
      cases b with
      | false =>
      rw [DTM.run_succ_of_not_halted _ 4 _ (by rfl)]
      rw [stepConfig_of_lit _ (writeMarkFstSnd).start (some false)
            (x1 :: x2 :: ls2 ++ L) (R) ⟨5, by omega⟩ (some true) Dir.left (Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x1 :: x2 :: ls2 ++ L) (some false :: R)).write (some true)).move Dir.left = Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 3 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨5, by omega⟩ : Fin 14) (x1)
            (x2 :: ls2 ++ L) (some true :: R) ⟨6, by omega⟩ (codeSnd (some false)) Dir.stay (Tape.mk (x2 :: ls2 ++ L) (codeSnd (some false) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)).write (codeSnd (some false))).move Dir.stay = Tape.mk (x2 :: ls2 ++ L) (codeSnd (some false) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 2 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨6, by omega⟩ : Fin 14) (codeSnd (some false))
            (x2 :: ls2 ++ L) (some true :: R) ⟨7, by omega⟩ (codeSnd (some false)) Dir.left (Tape.mk (ls2 ++ L) (x2 :: codeSnd (some false) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x2 :: ls2 ++ L) (codeSnd (some false) :: some true :: R)).write (codeSnd (some false))).move Dir.left = Tape.mk (ls2 ++ L) (x2 :: codeSnd (some false) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 1 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨7, by omega⟩ : Fin 14) (x2)
            (ls2 ++ L) (codeSnd (some false) :: some true :: R) ⟨8, by omega⟩ (codeFst (some false)) Dir.stay (Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls2 ++ L) (x2 :: codeSnd (some false) :: some true :: R)).write (codeFst (some false))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 0 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨8, by omega⟩ : Fin 14) (codeFst (some false))
            (ls2 ++ L) (codeSnd (some false) :: some true :: R) ⟨13, by omega⟩ (codeFst (some false)) Dir.stay (Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)).write (codeFst (some false))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R))]
      rfl
      | true =>
      rw [DTM.run_succ_of_not_halted _ 4 _ (by rfl)]
      rw [stepConfig_of_lit _ (writeMarkFstSnd).start (some true)
            (x1 :: x2 :: ls2 ++ L) (R) ⟨9, by omega⟩ (some true) Dir.left (Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x1 :: x2 :: ls2 ++ L) (some true :: R)).write (some true)).move Dir.left = Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 3 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨9, by omega⟩ : Fin 14) (x1)
            (x2 :: ls2 ++ L) (some true :: R) ⟨10, by omega⟩ (codeSnd (some true)) Dir.stay (Tape.mk (x2 :: ls2 ++ L) (codeSnd (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)).write (codeSnd (some true))).move Dir.stay = Tape.mk (x2 :: ls2 ++ L) (codeSnd (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 2 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨10, by omega⟩ : Fin 14) (codeSnd (some true))
            (x2 :: ls2 ++ L) (some true :: R) ⟨11, by omega⟩ (codeSnd (some true)) Dir.left (Tape.mk (ls2 ++ L) (x2 :: codeSnd (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (x2 :: ls2 ++ L) (codeSnd (some true) :: some true :: R)).write (codeSnd (some true))).move Dir.left = Tape.mk (ls2 ++ L) (x2 :: codeSnd (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 1 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨11, by omega⟩ : Fin 14) (x2)
            (ls2 ++ L) (codeSnd (some true) :: some true :: R) ⟨12, by omega⟩ (codeFst (some true)) Dir.stay (Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls2 ++ L) (x2 :: codeSnd (some true) :: some true :: R)).write (codeFst (some true))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R))]
      rw [DTM.run_succ_of_not_halted _ 0 _ (by rfl)]
      rw [stepConfig_of_lit _ (⟨12, by omega⟩ : Fin 14) (codeFst (some true))
            (ls2 ++ L) (codeSnd (some true) :: some true :: R) ⟨13, by omega⟩ (codeFst (some true)) Dir.stay (Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)) (by rfl)
            (by rfl : ((Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)).write (codeFst (some true))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R))]
      rfl

end DTM

end Pnp
