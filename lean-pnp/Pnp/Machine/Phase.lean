/-
  文件：Pnp/Machine/Phase.lean
  主题：倍增循环的两个相位——「走到右端标副本」与「回扫到数据区左端」。

  相位机器 `toEndBack` 有 5 个状态：
    - 0（toEnd）：向右跨过全部非空白格；遇到空白就写 `some false`
      （在副本区末尾追加一格），转入状态 1 并左移；
    - 1（back）：向左回扫；越过全部非空白格后（读到左侧人工空白）
      转入状态 2 并右移一格，停在数据区第一格；
    - 2（ready，非终止）；3 接受；4 拒绝。

  本文件先完成 toEnd 相位：
    - `toEnd_run`：对任意左内容 L 与非空白块 blk，
      `|blk|+1` 步后状态为 1，内容末尾多出一个 `some false`。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 5 状态相位机：0 向右标副本，1 向左回扫，2 就绪，3/4 为终止状态。 -/
def toEndBack : DTM 5 where
  step := fun s a =>
    if s.val = 0 then
      if a = none then (1, some false, Dir.left) else (0, a, Dir.right)
    else if s.val = 1 then
      if a = none then (2, a, Dir.right) else (1, a, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 3
  reject := 4

/-- toEnd 相位：从状态 0、右内容为「非空白块 blk 后接一个空白」出发，
    `|blk|+1` 步后停在状态 1，并在内容末尾写入一个 `some false`。 -/
theorem toEnd_run (L blk : List Sym) (hne : ∀ x ∈ blk, x ≠ none) :
    toEndBack.run (blk.length + 1)
      { state := (0 : Fin 5), tape := { left := L, right := blk ++ [none] } } =
    { state := (1 : Fin 5),
      tape := { left := (blk.reverse ++ L).tail,
                right := (blk.reverse ++ L).headD none :: [some false] } } := by
  induction blk generalizing L with
  | nil =>
      -- 已是空白：写 false、左移一格
      have hhalt : toEndBack.halted
          { state := (0 : Fin 5),
            tape := { left := L, right := ([] : List Sym) ++ [none] } } = false := by
        simp [DTM.halted, toEndBack]
      have hstep : toEndBack.stepConfig
          { state := (0 : Fin 5),
            tape := { left := L, right := ([] : List Sym) ++ [none] } }
          = { state := (1 : Fin 5),
              tape := { left := L.tail,
                        right := L.headD none :: [some false] } } := by
        cases L with
        | nil => simp [DTM.stepConfig, toEndBack, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        | cons l ls =>
            simp [DTM.stepConfig, toEndBack, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      simp only [List.length_nil]
      rw [DTM.run_succ_of_not_halted toEndBack 0 _ hhalt, hstep]
      simp [DTM.run]
  | cons x xs ih =>
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      -- 第一步：读到非空白 x，原样写回并右移
      have hhalt : toEndBack.halted
          { state := (0 : Fin 5),
            tape := { left := L, right := (x :: xs) ++ [none] } } = false := by
        simp [DTM.halted, toEndBack]
      have hstep : toEndBack.stepConfig
          { state := (0 : Fin 5),
            tape := { left := L, right := (x :: xs) ++ [none] } }
          = { state := (0 : Fin 5),
              tape := { left := x :: L, right := xs ++ [none] } } := by
        simp [DTM.stepConfig, toEndBack, Tape.read, Tape.write, Tape.move, Tape.moveRight, hx]
      simp only [List.length_cons]
      rw [DTM.run_succ_of_not_halted toEndBack (xs.length + 1) _ hhalt, hstep]
      rw [ih (x :: L) hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- back 相位：状态 1 从「非空白块 P 之后再往左一个空白」出发，
    左移越过 P 后碰到空白，右移一格转入状态 2；
    共 `|P|+2` 步，内容不变，左端只留下一个空白。 -/
theorem back_run (P r : List Sym) (x : Sym)
    (hP : ∀ y ∈ P, y ≠ none) (hx : x ≠ none) :
    toEndBack.run (P.length + 2)
      { state := (1 : Fin 5), tape := { left := P ++ [none], right := x :: r } } =
    { state := (2 : Fin 5),
      tape := { left := [none], right := P.reverse ++ x :: r } } := by
  induction P generalizing r x with
  | nil =>
      -- 已贴着空白：左移一次踩上空白，再右移回到 x
      have h0 : toEndBack.halted
          { state := (1 : Fin 5),
            tape := { left := ([] : List Sym) ++ [none], right := x :: r } } = false := by
        simp [DTM.halted, toEndBack]
      have hstep1 : toEndBack.stepConfig
          { state := (1 : Fin 5),
            tape := { left := ([] : List Sym) ++ [none], right := x :: r } }
          = { state := (1 : Fin 5),
              tape := { left := ([] : List Sym), right := none :: x :: r } } := by
        simp [DTM.stepConfig, toEndBack, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, hx]
      have h1 : toEndBack.halted
          { state := (1 : Fin 5),
            tape := { left := ([] : List Sym), right := none :: x :: r } } = false := by
        simp [DTM.halted, toEndBack]
      have hstep2 : toEndBack.stepConfig
          { state := (1 : Fin 5),
            tape := { left := ([] : List Sym), right := none :: x :: r } }
          = { state := (2 : Fin 5),
              tape := { left := [none], right := x :: r } } := by
        simp [DTM.stepConfig, toEndBack, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
      change toEndBack.run ((0 + 1) + 1) _ = _
      rw [DTM.run_succ_of_not_halted toEndBack (0 + 1) _ h0, hstep1,
          DTM.run_succ_of_not_halted toEndBack 0 _ h1, hstep2]
      simp [DTM.run]
  | cons p ps ih =>
      have hp : p ≠ none := hP p List.mem_cons_self
      have hps : ∀ y ∈ ps, y ≠ none :=
        fun y hy => hP y (List.mem_cons_of_mem _ hy)
      -- 第一步：当前读 x（非空白），左移把 p 推到右侧
      have hhalt : toEndBack.halted
          { state := (1 : Fin 5),
            tape := { left := (p :: ps) ++ [none], right := x :: r } } = false := by
        simp [DTM.halted, toEndBack]
      have hstep : toEndBack.stepConfig
          { state := (1 : Fin 5),
            tape := { left := (p :: ps) ++ [none], right := x :: r } }
          = { state := (1 : Fin 5),
              tape := { left := ps ++ [none], right := p :: x :: r } } := by
        simp [DTM.stepConfig, toEndBack, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, hx]
      simp only [List.length_cons]
      change toEndBack.run (((ps.length + 1) + 1) + 1) _ = _
      rw [DTM.run_succ_of_not_halted toEndBack ((ps.length + 1) + 1) _ hhalt, hstep]
      change toEndBack.run (ps.length + 2) _ = _
      rw [ih (x :: r) p hps hp]
      simp [List.reverse_cons, List.append_assoc]

/-- 相位机整段运行：从状态 0、左内容 `Q ++ [none]`、右内容 `blk ++ [none]`
    出发（`Q`、`blk` 全非空白，且 `blk.reverse ++ Q` 非空），
    先到右端追加一个 `some false`，再回扫到左端并右移一格，
    最终停在状态 2；内容为原内容末尾多一个 `some false`。 -/
theorem toEndBack_run (Q blk : List Sym)
    (hQ : ∀ y ∈ Q, y ≠ none) (hb : ∀ y ∈ blk, y ≠ none)
    (hU : blk.reverse ++ Q ≠ []) :
    toEndBack.run ((blk.length + 1) + (((blk.reverse ++ Q).tail).length + 2))
      { state := (0 : Fin 5),
        tape := { left := Q ++ [none], right := blk ++ [none] } } =
    { state := (2 : Fin 5),
      tape := { left := [none],
                right := ((blk.reverse ++ Q).tail).reverse ++
                           (blk.reverse ++ Q).headD none :: [some false] } } := by
  -- 全非空白：blk.reverse ++ Q 的任何元素都非空白
  have hAll : ∀ y ∈ blk.reverse ++ Q, y ≠ none := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hb y (List.mem_reverse.mp h)
    · exact hQ y h
  have hP : ∀ y ∈ (blk.reverse ++ Q).tail, y ≠ none :=
    fun y hy => hAll y (List.mem_of_mem_tail hy)
  have hx : (blk.reverse ++ Q).headD none ≠ none := by
    cases hU' : blk.reverse ++ Q with
    | nil => exact absurd hU' hU
    | cons a as =>
        have ha : a ≠ none := hAll a (by rw [hU']; exact List.mem_cons_self)
        simpa [hU'] using ha
  -- 把 toEnd 的终态改写成 back_run 需要的形状
  have hleft : (blk.reverse ++ (Q ++ [none])).tail =
      (blk.reverse ++ Q).tail ++ [none] := by
    rw [← List.append_assoc, List.tail_append_of_ne_nil hU]
  have hhead : (blk.reverse ++ (Q ++ [none])).headD none =
      (blk.reverse ++ Q).headD none := by
    rw [← List.append_assoc]
    cases hU' : blk.reverse ++ Q with
    | nil => simp
    | cons a as => simp
  rw [DTM.run_add, toEnd_run (Q ++ [none]) blk hb, hleft, hhead]
  exact back_run ((blk.reverse ++ Q).tail) [some false]
    ((blk.reverse ++ Q).headD none) hP hx

end DTM

end Pnp
