/-
  文件：Pnp/Machine/Double.lean
  主题：unary 倍增循环的合并状态机与一次迭代。

  数据约定：纸带上有一段非空白块，内容形如
    `false^k ++ true^(n-k) ++ false^k`
  （左侧 k 个已处理源格与 k 个已写副本，中间尚未处理的源格全是 `some true`）。
  读写头初始在块的第一格，机器每跑一轮把块变成
    `false^(k+1) ++ true^(n-k-1) ++ false^(k+1)`，
  即多消耗一个源格、多写一个副本；全部消耗完后块变成 `false^n ++ false^n`，
  再由恢复机统一改写成 `some true`，完成「长度翻倍」`n ↦ 2n`。

  状态（共 4 个）：
    - 0：向右找第一个 `some true`（源格），找到就改写成 `some false` 并右移，进入状态 1；
         遇到空白说明源格耗尽，进入状态 3（终止，交给外层恢复阶段）；
    - 1：继续右扫到块尾，遇空白写 `some false`（副本区加一格），左移进入状态 2；
    - 2：向左回扫到左端人工空白，右移一格回到块首，转入状态 0 开始下一轮；
    - 3：终止状态（源格耗尽）。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 倍增循环机：0 找源格、1 扫到尾并写副本、2 回扫，3 为源耗尽后的终止状态。 -/
def doubleStep : DTM 4 where
  step := fun s a =>
    if s.val = 0 then
      if a = some true then (1, some false, Dir.right)
      else if a = some false then (0, a, Dir.right)
      else (3, a, Dir.stay)
    else if s.val = 1 then
      if a = none then (2, some false, Dir.left) else (1, a, Dir.right)
    else if s.val = 2 then
      if a = none then (0, a, Dir.right) else (2, a, Dir.left)
    else (s, a, Dir.stay)
  start := 0
  accept := 3
  reject := 3

/-- 阶段一：跳过 `k` 个已处理格后找到第一个源格，`k+1` 步把它标成已处理并右移。
    `rest` 可以是任意剩余内容（含尾部空白有无皆可）。 -/
theorem double_seek_block (L : List Sym) (k : Nat) (rest : List Sym) :
    doubleStep.run (k + 1)
      { state := (0 : Fin 4),
        tape := { left := L,
                  right := List.replicate k (some false) ++ some true :: rest } } =
    { state := (1 : Fin 4),
      tape := { left := List.replicate (k + 1) (some false) ++ L, right := rest } } := by
  induction k generalizing L with
  | zero =>
      have hhalt : doubleStep.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate 0 (some false) ++ some true :: rest } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate 0 (some false) ++ some true :: rest } }
          = { state := (1 : Fin 4), tape := { left := some false :: L, right := rest } } := by
        rfl
      rw [DTM.run_succ_of_not_halted doubleStep 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ k ih =>
      have hhalt : doubleStep.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (k + 1) (some false) ++ some true :: rest } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (k + 1) (some false) ++ some true :: rest } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate k (some false) ++ some true :: rest } } := by
        rfl
      rw [DTM.run_succ_of_not_halted doubleStep (k + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 阶段一（源耗尽）：只剩 `m` 个已处理格与纸带末端，`m+1` 步进入终止状态 3。
    纸带末端 `e` 允许是空列表或单个空白（二者读出均为 `none`）；
    终止时最后一步把空白写回，纸带右侧统一为 `[none]`。 -/
theorem double_seek_end (L : List Sym) (m : Nat) (e : List Sym)
    (he : e = [] ∨ e = [none]) :
    doubleStep.run (m + 1)
      { state := (0 : Fin 4),
        tape := { left := L, right := List.replicate m (some false) ++ e } } =
    { state := (3 : Fin 4),
      tape := { left := List.replicate m (some false) ++ L, right := [none] } } := by
  induction m generalizing L with
  | zero =>
      have hhalt : doubleStep.halted
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate 0 (some false) ++ e } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate 0 (some false) ++ e } }
          = { state := (3 : Fin 4),
              tape := { left := L, right := [none] } } := by
        rcases he with rfl | rfl <;>
          simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move, List.replicate]
      rw [DTM.run_succ_of_not_halted doubleStep 0 _ hhalt, hstep]
      simp [DTM.run, List.replicate]
  | succ m ih =>
      have hhalt : doubleStep.halted
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := List.replicate (m + 1) (some false) ++ e } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (0 : Fin 4),
            tape := { left := L, right := List.replicate (m + 1) (some false) ++ e } }
          = { state := (0 : Fin 4),
              tape := { left := some false :: L,
                        right := List.replicate m (some false) ++ e } } := by
        rfl
      rw [DTM.run_succ_of_not_halted doubleStep (m + 1) _ hhalt, hstep]
      rw [ih (some false :: L)]
      simp [List.replicate_succ', List.append_assoc]

/-- 阶段二：从块内某格继续右扫，把每格原样保留，遇末端空白写一个 `some false` 后左移。
    末端 `e` 允许是空列表或单个空白；结果与 `e` 无关。 -/
theorem double_toEnd (L blk : List Sym) (hne : ∀ x ∈ blk, x ≠ none)
    (e : List Sym) (he : e = [] ∨ e = [none]) :
    doubleStep.run (blk.length + 1)
      { state := (1 : Fin 4), tape := { left := L, right := blk ++ e } } =
    { state := (2 : Fin 4),
      tape := { left := (blk.reverse ++ L).tail,
                right := (blk.reverse ++ L).headD none :: [some false] } } := by
  induction blk generalizing L with
  | nil =>
      have hhalt : doubleStep.halted
          { state := (1 : Fin 4),
            tape := { left := L, right := ([] : List Sym) ++ e } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (1 : Fin 4),
            tape := { left := L, right := ([] : List Sym) ++ e } }
          = { state := (2 : Fin 4),
              tape := { left := L.tail,
                        right := L.headD none :: [some false] } } := by
        rcases he with rfl | rfl
        · cases L <;>
            simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
        · cases L <;>
            simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      change doubleStep.run (0 + 1) _ = _
      rw [DTM.run_succ_of_not_halted doubleStep 0 _ hhalt, hstep]
      simp [DTM.run]
  | cons x xs ih =>
      have hx : x ≠ none := hne x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≠ none :=
        fun y hy => hne y (List.mem_cons_of_mem _ hy)
      have hhalt : doubleStep.halted
          { state := (1 : Fin 4),
            tape := { left := L, right := (x :: xs) ++ e } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (1 : Fin 4),
            tape := { left := L, right := (x :: xs) ++ e } }
          = { state := (1 : Fin 4),
              tape := { left := x :: L, right := xs ++ e } } := by
        simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move,
              Tape.moveRight, hx]
      simp only [List.length_cons]
      rw [DTM.run_succ_of_not_halted doubleStep (xs.length + 1) _ hhalt, hstep]
      rw [ih (x :: L) hxs]
      simp [List.reverse_cons, List.append_assoc]

/-- 阶段三：从块内回扫到左端人工空白，再右移一格回到块首，
    结束于状态 0，为下一轮做准备；内容不变。 -/
theorem double_back (P r : List Sym) (x : Sym)
    (hP : ∀ y ∈ P, y ≠ none) (hx : x ≠ none) :
    doubleStep.run (P.length + 2)
      { state := (2 : Fin 4), tape := { left := P ++ [none], right := x :: r } } =
    { state := (0 : Fin 4),
      tape := { left := [none], right := P.reverse ++ x :: r } } := by
  induction P generalizing r x with
  | nil =>
      have h0 : doubleStep.halted
          { state := (2 : Fin 4),
            tape := { left := ([] : List Sym) ++ [none], right := x :: r } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep1 : doubleStep.stepConfig
          { state := (2 : Fin 4),
            tape := { left := ([] : List Sym) ++ [none], right := x :: r } }
          = { state := (2 : Fin 4),
              tape := { left := ([] : List Sym), right := none :: x :: r } } := by
        simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, hx]
      have h1 : doubleStep.halted
          { state := (2 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: x :: r } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep2 : doubleStep.stepConfig
          { state := (2 : Fin 4),
            tape := { left := ([] : List Sym), right := none :: x :: r } }
          = { state := (0 : Fin 4),
              tape := { left := [none], right := x :: r } } := by
        simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move,
              Tape.moveRight]
      change doubleStep.run ((0 + 1) + 1) _ = _
      rw [DTM.run_succ_of_not_halted doubleStep (0 + 1) _ h0, hstep1,
          DTM.run_succ_of_not_halted doubleStep 0 _ h1, hstep2]
      simp [DTM.run]
  | cons p ps ih =>
      have hp : p ≠ none := hP p List.mem_cons_self
      have hps : ∀ y ∈ ps, y ≠ none :=
        fun y hy => hP y (List.mem_cons_of_mem _ hy)
      have hhalt : doubleStep.halted
          { state := (2 : Fin 4),
            tape := { left := (p :: ps) ++ [none], right := x :: r } } = false := by
        simp [DTM.halted, doubleStep]
      have hstep : doubleStep.stepConfig
          { state := (2 : Fin 4),
            tape := { left := (p :: ps) ++ [none], right := x :: r } }
          = { state := (2 : Fin 4),
              tape := { left := ps ++ [none], right := p :: x :: r } } := by
        simp [DTM.stepConfig, doubleStep, Tape.read, Tape.write, Tape.move,
              Tape.moveLeft, hx]
      simp only [List.length_cons]
      change doubleStep.run (((ps.length + 1) + 1) + 1) _ = _
      rw [DTM.run_succ_of_not_halted doubleStep ((ps.length + 1) + 1) _ hhalt, hstep]
      change doubleStep.run (ps.length + 2) _ = _
      rw [ih (x :: r) p hps hp]
      simp [List.reverse_cons, List.append_assoc]

/-- 辅助：把一个元素移到等值 `replicate` 块的左侧是安全的。 -/
theorem cons_replicate_append (a : Sym) (k : Nat) (X : List Sym) :
    a :: (List.replicate k a ++ X) = List.replicate k a ++ (a :: X) := by
  induction k generalizing X with
  | zero => simp
  | succ k ih => simp [List.replicate_succ', List.append_assoc, ih]

/-- 辅助：非空列表的「去掉头再反向、接上原头」等于整表反向。 -/
theorem back_cat (U : List Sym) (hU : U ≠ []) :
    U.tail.reverse ++ U.headD none :: [some false] = U.reverse ++ [some false] := by
  cases U with
  | nil => exact absurd rfl hU
  | cons a as => simp [List.reverse_cons]

/-- 一次迭代所需步数：找源格 `k+1` 步 + 扫到尾部写副本 + 回扫。 -/
def doubleIterSteps (m k : Nat) : Nat :=
  let blk := List.replicate m (some true) ++ List.replicate k (some false)
  (k + 1) + ((blk.length + 1) +
    (((blk.reverse ++ List.replicate (k + 1) (some false)).tail).length + 2))

/-- 一次完整迭代：从状态 0、块首出发，
    `false^k ++ true^(m+1) ++ false^k`（末端 `e` 可为空或一个空白）
    在若干步后变回状态 0、块首，块变为 `false^(k+1) ++ true^m ++ false^(k+1)`。
    注意结果末端不再带空白：块尾空白被写成了新副本。 -/
theorem double_iter (m k : Nat) (e : List Sym) (he : e = [] ∨ e = [none]) :
    doubleStep.run (doubleIterSteps m k)
      { state := (0 : Fin 4),
        tape := { left := [none],
                  right := List.replicate k (some false) ++ some true ::
                           (List.replicate m (some true) ++ List.replicate k (some false) ++ e) } } =
    { state := (0 : Fin 4),
      tape := { left := [none],
                right := List.replicate (k + 1) (some false) ++
                         List.replicate m (some true) ++
                         List.replicate (k + 1) (some false) } } := by
  dsimp only [doubleIterSteps]
  -- 块内元素全非空白
  have hblk : ∀ y ∈ List.replicate m (some true) ++ List.replicate k (some false),
      y ≠ none := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · rw [List.mem_replicate] at h
      rcases h with ⟨_, rfl⟩
      simp
    · rw [List.mem_replicate] at h
      rcases h with ⟨_, rfl⟩
      simp
  have hR : List.replicate (k + 1) (some false) ≠ [] := by simp
  have hU : ((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false)) ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ hR
  -- U 的展开式
  have hUexp : ((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false)) =
      List.replicate k (some false) ++ List.replicate m (some true) ++
        List.replicate (k + 1) (some false) := by
    simp [List.append_assoc]
  -- U 的元素全非空白
  have hAll : ∀ y ∈ ((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false)), y ≠ none := by
    intro y hy
    rw [hUexp] at hy
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · rw [List.mem_replicate] at hy
        rcases hy with ⟨_, rfl⟩
        simp
      · rw [List.mem_replicate] at hy
        rcases hy with ⟨_, rfl⟩
        simp
    · rw [List.mem_replicate] at hy
      rcases hy with ⟨_, rfl⟩
      simp
  have hP : ∀ y ∈ (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false))).tail, y ≠ none :=
    fun y hy => hAll y (List.mem_of_mem_tail hy)
  have hx : (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false))).headD none ≠ none := by
    cases h : ((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
        List.replicate (k + 1) (some false)) with
    | nil => exact absurd h hU
    | cons a as =>
        have ha : a ≠ none := hAll a (by rw [h]; exact List.mem_cons_self)
        simpa [h] using ha
  -- toEnd 终态与 back 入口的形状换算
  have hleft : (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      (List.replicate (k + 1) (some false) ++ [none])).tail) =
      (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
        List.replicate (k + 1) (some false)).tail) ++ [none] := by
    rw [← List.append_assoc, List.tail_append_of_ne_nil hU]
  have hhead : (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      (List.replicate (k + 1) (some false) ++ [none])).headD none) =
      (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
        List.replicate (k + 1) (some false)).headD none) := by
    rw [← List.append_assoc]
    cases h : ((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
        List.replicate (k + 1) (some false)) with
    | nil => simp
    | cons a as => simp
  -- 三段拼接
  rw [DTM.run_add]
  rw [double_seek_block [none] k
      (List.replicate m (some true) ++ List.replicate k (some false) ++ e)]
  rw [DTM.run_add]
  rw [double_toEnd (List.replicate (k + 1) (some false) ++ [none])
      (List.replicate m (some true) ++ List.replicate k (some false)) hblk e he]
  rw [hleft, hhead]
  rw [double_back (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false)).tail) [some false]
      (((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
        List.replicate (k + 1) (some false)).headD none) hP hx]
  rw [back_cat ((List.replicate m (some true) ++ List.replicate k (some false)).reverse ++
      List.replicate (k + 1) (some false)) hU]
  rw [hUexp]
  simp [List.reverse_append, List.append_assoc, List.replicate_succ', cons_replicate_append]

/-- 循环总步数：处理 `r` 个剩余源格的累计步数（`k` 为已处理格数）。 -/
def doubleLoopSteps : Nat → Nat → Nat
  | 0, _ => 0
  | r + 1, k => doubleIterSteps r k + doubleLoopSteps r (k + 1)

/-- 倍增主循环：块 `false^k ++ true^r ++ false^k`（无尾部空白）经 `r` 次迭代后
    变成 `false^(k+r) ++ false^(k+r)`，状态回到 0、头回到块首。 -/
theorem double_loop (r k : Nat) :
    doubleStep.run (doubleLoopSteps r k)
      { state := (0 : Fin 4),
        tape := { left := [none],
                  right := List.replicate k (some false) ++ List.replicate r (some true) ++
                           List.replicate k (some false) } } =
    { state := (0 : Fin 4),
      tape := { left := [none],
                right := List.replicate (k + r) (some false) ++
                         List.replicate (k + r) (some false) } } := by
  induction r generalizing k with
  | zero =>
      simp [doubleLoopSteps, DTM.run]
  | succ r ih =>
      -- 把输入改写成 double_iter 的入口形状
      have hshape : List.replicate k (some false) ++ List.replicate (r + 1) (some true) ++
          List.replicate k (some false) =
          List.replicate k (some false) ++ some true ::
            (List.replicate r (some true) ++ List.replicate k (some false) ++ ([] : List Sym)) := by
        simp only [List.replicate_succ', List.singleton_append, List.append_assoc,
          List.append_nil]
        rw [cons_replicate_append]
      rw [hshape]
      rw [show doubleLoopSteps (r + 1) k = doubleIterSteps r k + doubleLoopSteps r (k + 1)
        from rfl]
      rw [DTM.run_add, double_iter r k [] (Or.inl rfl), ih (k + 1)]
      simp [Nat.add_comm, Nat.add_left_comm]

end DTM

end Pnp
