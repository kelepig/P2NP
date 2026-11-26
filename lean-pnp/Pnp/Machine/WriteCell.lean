/-
  文件：Pnp/Machine/WriteCell.lean
  主题：模拟区「改写当前格 + 移动头标记」机 `writeCell`。

  单带模拟器找到头标记后，需要执行被模拟机的一步转移：

    - 把当前格的符号编码改写成新符号的编码（2 个符号）；
    - 把当前格的头标记清掉（写成 `some false`）；
    - 在相邻格（左或右，由被模拟机决定的移动方向）重新打上头标记。

  本文件给出固定的「动作脚本」机（9 个状态，8 步完成）：

    state 0：位于标记格，向左一格（到第二编码符号）；
    state 1：写入新编码第二符号，向左；
    state 2：写入新编码第一符号，向右；
    state 3：向右（回到标记格）；
    state 4：把标记写成 `some false`，按方向移动；
    state 5/6：沿方向再走两格（走过相邻格的编码）；
    state 7：在相邻格写上头标记 `some true`，进入接受态 8。

  左移与右移的差别只在 state 4/5/6 的移动方向，因此用参数 `d` 区分。

  已证（前提都在语句里写明，没有隐藏假设）：

    - `writeCell_run_right`：标记右移，接受后停在新的标记格上；
    - `writeCell_run_left`：标记左移（要求左侧还有一格；相邻格标记位为 `some false`）；
    - 两个结论的左侧都写成 `reverse (codeCells … ++ symCode …)` 的形式，
      与 `seekMark_run` 的结论完全同形，可直接串接。

  证明方式：先把两边纸带化成显式符号串，再把 8 步逐格展开；
  每一步的状态与写入符号都是具体值，所以 `rfl` 即可算出单步结果。
-/

import Pnp.Classes
import Pnp.Machine.SeekMark

namespace Pnp

namespace DTM

/-- 符号编码的第一个符号。 -/
def codeFst (s : Sym) : Sym := (symCode s).headD none

/-- 符号编码的第二个符号。 -/
def codeSnd (s : Sym) : Sym := ((symCode s).drop 1).headD none

/-- 编码展开成两个符号。 -/
theorem symCode_eq (s : Sym) : symCode s = [codeFst s, codeSnd s] := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- 标记位是 0 的格的编码展开成两个编码符号 + 标记。 -/
theorem cellCode_of_false (p : Sym × Bool) (h : p.2 = false) :
    cellCode p = [codeFst p.1, codeSnd p.1, some false] := by
  simp [cellCode, h, symCode_eq p.1]

/-- 标记位是 0 的单格编码展开成两个编码符号 + 标记。 -/
theorem codeCells_pair_false (s : Sym) :
    codeCells [(s, false)] = [codeFst s, codeSnd s, some false] := by
  simp [codeCells, cellCode, symCode_eq s]

/-- 改写一格并移动头标记的脚本机（9 状态，8 步完成）。 -/
def writeCell (s' : Sym) (d : Dir) : DTM 9 where
  step := fun st a =>
    if st.val = 0 then (1, a, Dir.left)
    else if st.val = 1 then (2, codeSnd s', Dir.left)
    else if st.val = 2 then (3, codeFst s', Dir.right)
    else if st.val = 3 then (4, a, Dir.right)
    else if st.val = 4 then (5, some false, d)
    else if st.val = 5 then (6, a, d)
    else if st.val = 6 then (7, a, d)
    else if st.val = 7 then (8, some true, Dir.stay)
    else (st, a, Dir.stay)
  start := 0
  accept := 8
  reject := 8

/-- 标记右移：把当前格改写成 `s'`，标记移到右侧相邻格。
    前提：右侧至少还有一格（`p`），且该格标记位是 `some false`。 -/
theorem writeCell_run_right (s' s : Sym) (pre : List (Sym × Bool)) (p : Sym × Bool)
    (post' : List (Sym × Bool)) (L : List Sym) (hp : p.2 = false) :
    (writeCell s' Dir.right).run 8
      { state := (0 : Fin 9),
        tape := { left := List.reverse (codeCells pre ++ symCode s) ++ L,
                  right := some true :: codeCells (p :: post') } } =
    { state := (8 : Fin 9),
      tape := { left := List.reverse (codeCells (pre ++ [(s', false)]) ++ symCode p.1) ++ L,
                right := some true :: codeCells post' } } := by
  have hleft : List.reverse (codeCells pre ++ symCode s) ++ L
      = codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L) := by
    rw [symCode_eq s, List.reverse_append]
    simp
  have hright : codeCells (p :: post')
      = codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post' := by
    rw [show codeCells (p :: post') = cellCode p ++ codeCells post' from by simp [codeCells],
      cellCode_of_false p hp]
    rfl
  have hgoal : List.reverse (codeCells (pre ++ [(s', false)]) ++ symCode p.1) ++ L
      = codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' ::
        (List.reverse (codeCells pre) ++ L) := by
    rw [codeCells_append, codeCells_pair_false s', symCode_eq p.1,
      List.reverse_append, List.reverse_append]
    simp [List.append_assoc]
  rw [hleft, hright, hgoal]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 7 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (0 : Fin 9)
   (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (1 : Fin 9)
   (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 6 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (1 : Fin 9)
   (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (2 : Fin 9)
   (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 5 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (2 : Fin 9)
   (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (3 : Fin 9)
   (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 4 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (3 : Fin 9)
   (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (4 : Fin 9)
   (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 3 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (4 : Fin 9)
   (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (5 : Fin 9)
   (Tape.mk (some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 2 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (5 : Fin 9)
   (Tape.mk (some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (6 : Fin 9)
   (Tape.mk (codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 1 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (6 : Fin 9)
   (Tape.mk (codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: some false :: codeCells post')))
    = (Config.mk (7 : Fin 9)
   (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post'))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.right) 0 _ (by rfl),
    show (writeCell s' Dir.right).stepConfig
(Config.mk (7 : Fin 9)
   (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post')))
    = (Config.mk (8 : Fin 9)
   (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post'))) from rfl]
  simp [DTM.run]

/-- 标记左移：把当前格改写成 `s'`，标记移到左侧相邻格。
    前提：左侧至少还有一格（`p`，即 `pre = pre' ++ [p]`），其标记位是 `some false`。 -/
theorem writeCell_run_left (s' s : Sym) (pre' : List (Sym × Bool)) (p : Sym × Bool)
    (post : List (Sym × Bool)) (L : List Sym) (hp : p.2 = false) :
    (writeCell s' Dir.left).run 8
      { state := (0 : Fin 9),
        tape := { left := List.reverse (codeCells (pre' ++ [p]) ++ symCode s) ++ L,
                  right := some true :: codeCells post } } =
    { state := (8 : Fin 9),
      tape := { left := List.reverse (codeCells pre' ++ symCode p.1) ++ L,
                right := some true :: codeCells ([(s', false)] ++ post) } } := by
  have hleft : List.reverse (codeCells (pre' ++ [p]) ++ symCode s) ++ L
      = codeSnd s :: codeFst s :: some false :: codeSnd p.1 :: codeFst p.1 ::
        (List.reverse (codeCells pre') ++ L) := by
    rw [codeCells_append,
      show codeCells [p] = cellCode p from by simp [codeCells],
      cellCode_of_false p hp, symCode_eq s,
      List.reverse_append, List.reverse_append]
    simp [List.append_assoc]
  have hgoal : List.reverse (codeCells pre' ++ symCode p.1) ++ L
      = codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L) := by
    rw [symCode_eq p.1, List.reverse_append]
    simp
  have hright : codeCells ([(s', false)] ++ post)
      = codeFst s' :: codeSnd s' :: some false :: codeCells post := by
    rw [codeCells_append, codeCells_pair_false s']
    rfl
  rw [hleft, hright, hgoal]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 7 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (0 : Fin 9)
   (Tape.mk (codeSnd s :: codeFst s :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeCells post)))
    = (Config.mk (1 : Fin 9)
   (Tape.mk (codeFst s :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: some true :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 6 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (1 : Fin 9)
   (Tape.mk (codeFst s :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: some true :: codeCells post)))
    = (Config.mk (2 : Fin 9)
   (Tape.mk (some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s' :: some true :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 5 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (2 : Fin 9)
   (Tape.mk (some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s' :: some true :: codeCells post)))
    = (Config.mk (3 : Fin 9)
   (Tape.mk (codeFst s' :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: some true :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 4 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (3 : Fin 9)
   (Tape.mk (codeFst s' :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: some true :: codeCells post)))
    = (Config.mk (4 : Fin 9)
   (Tape.mk (codeSnd s' :: codeFst s' :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 3 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (4 : Fin 9)
   (Tape.mk (codeSnd s' :: codeFst s' :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeCells post)))
    = (Config.mk (5 : Fin 9)
   (Tape.mk (codeFst s' :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: some false :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 2 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (5 : Fin 9)
   (Tape.mk (codeFst s' :: some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: some false :: codeCells post)))
    = (Config.mk (6 : Fin 9)
   (Tape.mk (some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: some false :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 1 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (6 : Fin 9)
   (Tape.mk (some false :: codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: some false :: codeCells post)))
    = (Config.mk (7 : Fin 9)
   (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (some false :: codeFst s' :: codeSnd s' :: some false :: codeCells post))) from rfl]
  rw [DTM.run_succ_of_not_halted (writeCell s' Dir.left) 0 _ (by rfl),
    show (writeCell s' Dir.left).stepConfig
(Config.mk (7 : Fin 9)
   (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (some false :: codeFst s' :: codeSnd s' :: some false :: codeCells post)))
    = (Config.mk (8 : Fin 9)
   (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeFst s' :: codeSnd s' :: some false :: codeCells post))) from rfl]
  simp [DTM.run]

end DTM

end Pnp
