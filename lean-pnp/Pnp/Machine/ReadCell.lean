/-
  文件：Pnp/Machine/ReadCell.lean
  主题：在标记格读取当前符号，并回到标记格。

  模拟区每格编码为 `symCode 符号 ++ [标记]`。`seekMark` 把读写头带到标记位后，
  需要读出这一格的符号（它决定查哪一行转移表），且读完后纸带必须原样恢复，
  以免影响后续步骤。

  提供的机器 `readCell`（13 状态，4 步）：

    state 0：在标记位，向左（到第二编码符号）；
    state 1：读到第二编码符号，按符号编号进入 state 2/3/4，向左；
    state 2..4：在第一个编码符号上，用两个符号解码出原符号，进入 5..7，向右；
    state 5..7：回到第二编码符号，向右，进入 state 8..10；
    state 8..10：停在标记位，状态编号携带解码出的符号（`8 + symIdx s`）。

  关键结论 `readCell_run`：纸带左、右两侧都完全恢复原样，只有状态变了。
  这保证它可以插在 `seekMark` 与 `writeCell` 之间而不破坏布局。

  注意：`readCell` 的 accept/reject 都设为 12（不使用），因此 4 步内不会提前停机。
-/

import Pnp.Machine.WriteCell

namespace Pnp

namespace DTM

/-- 符号的编号：none ↦ 0，some false ↦ 1，some true ↦ 2。 -/
def symIdx : Sym → Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- 编号还原符号（越界时给 none，仅为让函数全定义）。 -/
def symOfIdx : Nat → Sym
  | 0 => none
  | 1 => some false
  | 2 => some true
  | _ => none

/-- 符号编号总是小于 3。 -/
theorem symIdx_lt (s : Sym) : symIdx s < 3 := by
  cases s with
  | none => decide
  | some b => cases b <;> decide

/-- 编号与还原在范围内互逆。 -/
theorem symIdx_symOfIdx {i : Nat} (h : i < 3) : symIdx (symOfIdx i) = i := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

/-- 由两个编码符号解码出原符号（解码失败时给 none，仅为让函数全定义）。 -/
def symDecodePair (b0 b1 : Sym) : Sym :=
  match symDecode [b0, b1] with
  | some s => s
  | none => none

/-- 两个编码符号还原出的符号的编号。 -/
def symIdxOfCode (b0 b1 : Sym) : Nat := symIdx (symDecodePair b0 b1)

/-- 成对解码与编码互逆。 -/
theorem symDecodePair_symCode (s : Sym) : symDecodePair (codeFst s) (codeSnd s) = s := by
  rw [symDecodePair, ← symCode_eq s]
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- 两个编码符号的编号就是原符号的编号。 -/
theorem symIdxOfCode_symCode (s : Sym) : symIdxOfCode (codeFst s) (codeSnd s) = symIdx s := by
  rw [symIdxOfCode, symDecodePair_symCode]

/-- 解码编号总是小于 3。 -/
theorem symIdxOfCode_lt (b0 b1 : Sym) : symIdxOfCode b0 b1 < 3 :=
  symIdx_lt _

/-- 读到符号后停留的状态：编号 8 加符号编号。 -/
def readDone (s : Sym) : Fin 13 :=
  ⟨8 + symIdx s, by have := symIdx_lt s; omega⟩

/-- 读符号机（13 状态，4 步）。 -/
def readCell : DTM 13 where
  step := fun st a =>
    if h0 : st.val = 0 then (⟨1, by omega⟩, a, Dir.left)
    else if _h1 : st.val = 1 then
      (⟨2 + symIdx a, by have := symIdx_lt a; omega⟩, a, Dir.left)
    else if _h2 : st.val < 5 then
      (⟨5 + symIdxOfCode a (symOfIdx (st.val - 2)),
        by have := symIdxOfCode_lt a (symOfIdx (st.val - 2)); omega⟩, a, Dir.right)
    else if _h3 : st.val < 8 then
      (⟨8 + (st.val - 5), by have := st.isLt; omega⟩, a, Dir.right)
    else (st, a, Dir.stay)
  start := 0
  accept := 12
  reject := 12

/-- 读符号：从标记格出发，4 步后回到标记格，纸带原样恢复，状态携带符号编号。 -/
theorem readCell_run (s : Sym) (pre rest : List (Sym × Bool)) (L : List Sym) :
    readCell.run 4
      (Config.mk (0 : Fin 13)
        (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
                 (some true :: codeCells rest))) =
    Config.mk (readDone s)
      (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
               (some true :: codeCells rest)) := by
  have hleft : List.reverse (codeCells pre ++ symCode s) ++ L
      = codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L) := by
    rw [symCode_eq s, List.reverse_append]
    simp
  rw [hleft]
  cases s with
  | none =>
      -- b0 = some false，b1 = some false，符号编号 0
      simp only [symCode, codeFst, codeSnd, symIdx, readDone, List.headD, List.drop,
        List.length_cons]
      rw [DTM.run_succ_of_not_halted readCell 3 _ (by rfl),
        show readCell.stepConfig
          (Config.mk (0 : Fin 13)
            (Tape.mk (some false :: some false :: (List.reverse (codeCells pre) ++ L))
                     (some true :: codeCells rest)))
          = Config.mk (1 : Fin 13)
            (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                     (some false :: some true :: codeCells rest)) from rfl]
      rw [DTM.run_succ_of_not_halted readCell 2 _ (by rfl),
        show readCell.stepConfig
          (Config.mk (1 : Fin 13)
            (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                     (some false :: some true :: codeCells rest)))
          = Config.mk (3 : Fin 13)
            (Tape.mk (List.reverse (codeCells pre) ++ L)
                     (some false :: some false :: some true :: codeCells rest)) from rfl]
      rw [DTM.run_succ_of_not_halted readCell 1 _ (by rfl),
        show readCell.stepConfig
          (Config.mk (3 : Fin 13)
            (Tape.mk (List.reverse (codeCells pre) ++ L)
                     (some false :: some false :: some true :: codeCells rest)))
          = Config.mk (5 : Fin 13)
            (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                     (some false :: some true :: codeCells rest)) from rfl]
      rw [DTM.run_succ_of_not_halted readCell 0 _ (by rfl),
        show readCell.stepConfig
          (Config.mk (5 : Fin 13)
            (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                     (some false :: some true :: codeCells rest)))
          = Config.mk (8 : Fin 13)
            (Tape.mk (some false :: some false :: (List.reverse (codeCells pre) ++ L))
                     (some true :: codeCells rest)) from rfl]
      simp [DTM.run]
  | some b =>
      cases b with
      | false =>
          -- b0 = some false，b1 = some true，符号编号 1
          simp only [symCode, codeFst, codeSnd, symIdx, symIdxOfCode, symDecodePair,
            symDecode, readDone, List.headD, List.drop, List.length_cons]
          rw [DTM.run_succ_of_not_halted readCell 3 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (0 : Fin 13)
                (Tape.mk (some true :: some false :: (List.reverse (codeCells pre) ++ L))
                         (some true :: codeCells rest)))
              = Config.mk (1 : Fin 13)
                (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)) from rfl]
          rw [DTM.run_succ_of_not_halted readCell 2 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (1 : Fin 13)
                (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)))
              = Config.mk (4 : Fin 13)
                (Tape.mk (List.reverse (codeCells pre) ++ L)
                         (some false :: some true :: some true :: codeCells rest)) from rfl]
          rw [DTM.run_succ_of_not_halted readCell 1 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (4 : Fin 13)
                (Tape.mk (List.reverse (codeCells pre) ++ L)
                         (some false :: some true :: some true :: codeCells rest)))
              = Config.mk (6 : Fin 13)
                (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)) from rfl]
          rw [DTM.run_succ_of_not_halted readCell 0 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (6 : Fin 13)
                (Tape.mk (some false :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)))
              = Config.mk (9 : Fin 13)
                (Tape.mk (some true :: some false :: (List.reverse (codeCells pre) ++ L))
                         (some true :: codeCells rest)) from rfl]
          simp [DTM.run]
      | true =>
          -- b0 = some true，b1 = some true，符号编号 2
          simp only [symCode, codeFst, codeSnd, symIdx, symIdxOfCode, symDecodePair,
            symDecode, readDone, List.headD, List.drop, List.length_cons]
          rw [DTM.run_succ_of_not_halted readCell 3 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (0 : Fin 13)
                (Tape.mk (some true :: some true :: (List.reverse (codeCells pre) ++ L))
                         (some true :: codeCells rest)))
              = Config.mk (1 : Fin 13)
                (Tape.mk (some true :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)) from rfl]
          rw [DTM.run_succ_of_not_halted readCell 2 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (1 : Fin 13)
                (Tape.mk (some true :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)))
              = Config.mk (4 : Fin 13)
                (Tape.mk (List.reverse (codeCells pre) ++ L)
                         (some true :: some true :: some true :: codeCells rest)) from rfl]
          rw [DTM.run_succ_of_not_halted readCell 1 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (4 : Fin 13)
                (Tape.mk (List.reverse (codeCells pre) ++ L)
                         (some true :: some true :: some true :: codeCells rest)))
              = Config.mk (7 : Fin 13)
                (Tape.mk (some true :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)) from rfl]
          rw [DTM.run_succ_of_not_halted readCell 0 _ (by rfl),
            show readCell.stepConfig
              (Config.mk (7 : Fin 13)
                (Tape.mk (some true :: (List.reverse (codeCells pre) ++ L))
                         (some true :: some true :: codeCells rest)))
              = Config.mk (10 : Fin 13)
                (Tape.mk (some true :: some true :: (List.reverse (codeCells pre) ++ L))
                         (some true :: codeCells rest)) from rfl]
          simp [DTM.run]

end DTM

end Pnp
