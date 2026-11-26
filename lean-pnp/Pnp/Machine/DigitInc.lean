/-
  文件：Pnp/Machine/DigitInc.lean
  File: Pnp/Machine/DigitInc.lean

  主题：数字区右端的**一位加一（含单次进位）**整机 `incDigit`。
  Topic: a single machine `incDigit` doing "add one to the rightmost digit, with one carry".

  用途（B5 外层枚举 E）：E 的 B 进制计数器每轮给最右块加一；值满 `B-1` 时把该块弹掉
  （块首 `some false` 改写为 `none`，成为新的终止空白），进位留待下一轮——右侧旧块变成
  垃圾，而观察机只读终止空白之前的块，故出口规格是「左侧上下文精确 + 右侧任意」。
  Purpose (E): each round increments the rightmost block; a full block (`B-1`) is popped by
  overwriting its head with a blank, leaving the carry to the next round.

  整机是 `readDigitBack`（状态 0..B+1 计数）与 `growBlock`（状态 B+3..B+5 相位）的并表，
  状态 `B+2` 承担进位决策、`B+6` 是终止态。入口/出口同形（头都在终止空白上），可自循环。
  The machine merges the counting table of `readDigitBack` with the growth phases of
  `growBlock`; state `B+2` takes the carry decision, `B+6` halts. Entry and exit shapes
  coincide (head on the trailing blank), so it composes with itself.

  依状态值的分叉用 **dite 链**；零依赖下 `omega` 看不见 `↑⟨B+3, …⟩`，故相位单步引理把状态
  传成 `Fin` 变量并带 `hval : st.val = B+3`，`omega` 便能以 `hval` 作约束。
  Value-dependent dispatch uses a dite chain; since zero-dependency `omega` cannot see
  `↑⟨B+3, …⟩`, the phase lemmas pass the state as a `Fin` variable with `hval`.
-/

import Pnp.Machine.DigitGrow

namespace Pnp

namespace DTM

/-- 一位加一（含单次进位）机。Rightmost-digit incrementer with one carry step. -/
def incDigit (B : Nat) : DTM (B + 7) where
  step := fun st a =>
    if st.val = 0 then (⟨1, by omega⟩, a, Dir.left)
    else if h1 : st.val < B + 2 then
      (match a with
       | some true => (⟨st.val + 1, by omega⟩, a, Dir.left)
       | some false => (⟨B + 3, by omega⟩, a, Dir.stay)
       | none => (⟨B + 6, by omega⟩, a, Dir.stay))
    else if h2 : st.val = B + 2 then
      (match a with
       | some false => (⟨B + 6, by omega⟩, none, Dir.stay)
       | _ => (⟨B + 6, by omega⟩, a, Dir.stay))
    else if h3 : st.val = B + 3 then
      (match a with
       | none => (⟨B + 4, by omega⟩, a, Dir.stay)
       | _ => (⟨B + 3, by omega⟩, a, Dir.right))
    else if h4 : st.val = B + 4 then (⟨B + 5, by omega⟩, some true, Dir.right)
    else (⟨B + 6, by omega⟩, none, Dir.stay)
  start := 0
  accept := ⟨B + 6, by omega⟩
  reject := ⟨B + 6, by omega⟩

/-- 状态值小于 `B+6` 一律不停机。 States below `B+6` never halt. -/
theorem incDigit_halted_false (B s : Nat) (hs : s < B + 6) (t : Tape) :
    (incDigit B).halted (Config.mk (⟨s, by omega⟩ : Fin (B + 7)) t) = false := by
  have hne : (⟨s, by omega⟩ : Fin (B + 7)) ≠ (⟨B + 6, by omega⟩ : Fin (B + 7)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  unfold DTM.halted incDigit
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 起始步：状态 0 一律左移一格。 First step: state 0 moves left. -/
theorem incDigit_step_start (B : Nat) (a : Sym) (X R : List Sym) :
    (incDigit B).stepConfig
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: X) (none :: R))) =
      Config.mk (⟨1, by omega⟩ : Fin (B + 7)) (Tape.mk X (a :: none :: R)) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  simp

/-- 计数步：非起始状态读到真格就左移一格、状态加一。 Counting step on a true cell. -/
theorem incDigit_step_true (B s : Nat) (hs0 : s ≠ 0) (hs : s < B + 2)
    (a : Sym) (X R : List Sym) :
    (incDigit B).stepConfig
        (Config.mk (⟨s, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: X) (some true :: R))) =
      Config.mk (⟨s + 1, by omega⟩ : Fin (B + 7)) (Tape.mk X (a :: some true :: R)) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg hs0, dif_pos hs]

/-- 决策步（块未满）：计数状态读到块首 `some false`，转入成长相位（原地）。
    Decision step (not full): a counting state on the block head switches to growth. -/
theorem incDigit_step_false (B s : Nat) (hs0 : s ≠ 0) (hs : s < B + 2)
    (L R : List Sym) :
    (incDigit B).stepConfig
        (Config.mk (⟨s, by omega⟩ : Fin (B + 7)) (Tape.mk L (some false :: R))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (some false :: R)) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg hs0, dif_pos hs]

/-- 决策步（块满）：进位判定态读到块首 `some false`，改写为空白并停机（弹块）。
    Decision step (full): the carry state blanks the block head and halts (pop). -/
theorem incDigit_step_carry (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 2)
    (L R : List Sym) :
    (incDigit B).stepConfig (Config.mk st (Tape.mk L (some false :: R))) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R)) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]

/-- 成长相位 1：非空白格右移一格。 Growth phase 1: move right over a non-blank cell. -/
theorem incDigit_step_walk (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 3)
    (L : List Sym) (a : Sym) (ha : a ≠ none) (R : List Sym) :
    (incDigit B).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: L) R) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]

/-- 成长相位 1：见空白转入相位 2。 Growth phase 1: the blank switches to phase 2. -/
theorem incDigit_step_walk_stop (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 3)
    (L R : List Sym) :
    (incDigit B).stepConfig (Config.mk st (Tape.mk L (none :: R))) =
      Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R)) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]

/-- 成长相位 2：在终止空白处写 `some true` 并右移。 Phase 2: write `some true`, move right. -/
theorem incDigit_step_two (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 4)
    (L R : List Sym) :
    (incDigit B).stepConfig (Config.mk st (Tape.mk L (none :: R))) =
      Config.mk (⟨B + 5, by omega⟩ : Fin (B + 7)) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_left (by omega)]

/-- 成长相位 3：写新终止空白并停机。 Phase 3: write the new trailing blank and halt. -/
theorem incDigit_step_three (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 5)
    (L R : List Sym) :
    (incDigit B).stepConfig (Config.mk st (Tape.mk L R)) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R.tail)) := by
  simp only [DTM.stepConfig, incDigit, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega)]

/-- 连续读 `m` 个真格：状态 `s` 变 `s + m`。 Reading `m` true cells. -/
theorem incDigit_count (B : Nat) :
    ∀ (m s : Nat), (hs0 : s ≠ 0) → (hs : s + m < B + 2) → ∀ (X R : List Sym),
      (incDigit B).run m
        (Config.mk (⟨s, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate m (some true) ++ X) (some true :: R))) =
      Config.mk (⟨s + m, by omega⟩ : Fin (B + 7))
        (Tape.mk X (List.replicate m (some true) ++ some true :: R)) := by
  intro m
  induction m with
  | zero =>
      intro s _ _ X R
      rfl
  | succ m ih =>
      intro s hs0 hs X R
      have hs2 : s < B + 2 := by omega
      have hhalt : (incDigit B).halted
          (Config.mk (⟨s, by omega⟩ : Fin (B + 7))
            (Tape.mk (some true :: (List.replicate m (some true) ++ X)) (some true :: R)))
          = false := incDigit_halted_false B s (by omega) _
      rw [show List.replicate (m + 1) (some true) ++ X
          = some true :: (List.replicate m (some true) ++ X) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt]
      rw [incDigit_step_true B s hs0 hs2 (some true) (List.replicate m (some true) ++ X) R]
      rw [ih (s + 1) (by omega) (by omega) X (some true :: R)]
      rw [replicate_append_cons]
      rw [List.replicate_succ, List.cons_append]
      simp only [Nat.add_comm, Nat.add_left_comm]

/-- **读块段**：`d+3` 步从区尾空白走到块首。 Reading leg: `d+3` steps to the block head. -/
theorem incDigit_read_block (B d : Nat) (hd : d < B) (L R : List Sym) :
    (incDigit B).run (d + 3)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 2) (some true) ++ some false :: L) (none :: R))) =
      Config.mk (⟨d + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk L (blockCode d ++ none :: R)) := by
  rw [show List.replicate (d + 2) (some true) ++ some false :: L
      = some true :: (List.replicate (d + 1) (some true) ++ some false :: L) from by
    rw [show d + 2 = d + 1 + 1 from by omega, List.replicate_succ, List.cons_append]]
  have hhalt0 : (incDigit B).halted
      (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
        (Tape.mk (some true :: (List.replicate (d + 1) (some true) ++ some false :: L))
          (none :: R)))
      = false := incDigit_halted_false B 0 (by omega) _
  rw [DTM.run_succ_of_not_halted _ (d + 2) _ hhalt0]
  rw [incDigit_step_start B (some true)
    (List.replicate (d + 1) (some true) ++ some false :: L) R]
  have haux := incDigit_count B (d + 1) 1 (by omega) (by omega)
    (some false :: L) (none :: R)
  have hhalt1 : (incDigit B).halted
      ((incDigit B).run (d + 1)
        (Config.mk (⟨1, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 1) (some true) ++ some false :: L)
            (some true :: none :: R)))) = false := by
    rw [haux]
    exact incDigit_halted_false B (1 + (d + 1)) (by omega) _
  rw [DTM.run_succ_last _ (d + 1) _ hhalt1]
  rw [haux]
  rw [show List.replicate (d + 1) (some true) ++ some true :: none :: R
      = some true :: (List.replicate d (some true) ++ some true :: none :: R) from by
    rw [List.replicate_succ, List.cons_append]]
  rw [incDigit_step_true B (1 + (d + 1)) (by omega) (by omega) (some false) L
    (List.replicate d (some true) ++ some true :: none :: R)]
  rw [replicate_append_cons]
  simp only [blockCode, show d + 2 = d + 1 + 1 from by omega, List.replicate_succ,
    List.cons_append]
  simp only [Nat.add_comm, Nat.add_left_comm]

/-- 成长相位掠过整段非空白块：`|l|+1` 步后停在块后空白、状态 `B+4`。
    The growth phase walks over a non-blank block in `|l|+1` steps. -/
theorem incDigit_walk : ∀ (B : Nat) (l : List Sym), (∀ y ∈ l, y ≠ none) →
    ∀ (L R : List Sym),
      (incDigit B).run (l.length + 1)
        (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (l ++ none :: R))) =
      Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk (l.reverse ++ L) (none :: R))
  | B, [], _, L, R => by
      show (incDigit B).run 1
          (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))
      rw [DTM.run_succ_of_not_halted _ 0 _
        (incDigit_halted_false B (B + 3) (by omega) _)]
      show (incDigit B).stepConfig
          (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))
      exact incDigit_step_walk_stop B (⟨B + 3, by omega⟩) rfl L R
  | B, a :: t, hl, L, R => by
      have ha : a ≠ none := hl a List.mem_cons_self
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (List.mem_cons_of_mem _ hy)
      show (incDigit B).run ((t.length + 1) + 1)
          (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (a :: (t ++ none :: R)))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
          (Tape.mk ((a :: t).reverse ++ L) (none :: R))
      rw [DTM.run_succ_of_not_halted _ (t.length + 1) _
        (incDigit_halted_false B (B + 3) (by omega) _)]
      show (incDigit B).run (t.length + 1)
          ((incDigit B).stepConfig
            (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
              (Tape.mk L (a :: (t ++ none :: R))))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
          (Tape.mk ((a :: t).reverse ++ L) (none :: R))
      rw [incDigit_step_walk B (⟨B + 3, by omega⟩) rfl L a ha]
      rw [incDigit_walk B t ht (a :: L) R]
      rw [show (a :: t).reverse ++ L = t.reverse ++ (a :: L) from by
        simp [List.reverse_cons, List.append_assoc]]

/-- **读块 + 决策（不进位）**：`d+4` 步从区尾空白走到块首并进入成长相位。
    Read + decide (no carry). -/
theorem incDigit_read_decide (B d : Nat) (hd : d + 1 < B) (L R : List Sym) :
    (incDigit B).run (d + 4)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 2) (some true) ++ some false :: L) (none :: R))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk L (blockCode d ++ none :: R)) := by
  have hread := incDigit_read_block B d (by omega) L R
  have hhalt : (incDigit B).halted
      (Config.mk (⟨d + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk L (blockCode d ++ none :: R))) = false :=
    incDigit_halted_false B (d + 3) (by omega) _
  rw [show d + 4 = (d + 3) + 1 from by omega]
  rw [DTM.run_add]
  rw [hread]
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt]
  rw [show blockCode d ++ none :: R
      = some false :: (List.replicate (d + 2) (some true) ++ none :: R) from by
    simp only [blockCode, List.cons_append]]
  rw [incDigit_step_false B (d + 3) (by omega) (by omega)]
  rfl

/-- **一位加一（不进位）**：`2d+10` 步后最右块 `d ↦ d+1`，头停在新终止空白上。
    Add one, no carry. -/
theorem incDigit_run_grow (B d : Nat) (hd : d + 1 < B) (L R : List Sym) :
    (incDigit B).run (2 * d + 10)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 2) (some true) ++ some false :: L) (none :: R))) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7))
        (Tape.mk (List.replicate (d + 3) (some true) ++ some false :: L) (none :: R.tail)) := by
  have hdec := incDigit_read_decide B d hd L R
  have hwalk := incDigit_walk B (blockCode d) (blockCode_ne_none d) L R
  have hhalt3 : (incDigit B).halted
      (Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
        (Tape.mk ((blockCode d).reverse ++ L) (none :: R))) = false :=
    incDigit_halted_false B (B + 4) (by omega) _
  have hhalt4 : (incDigit B).halted
      (Config.mk (⟨B + 5, by omega⟩ : Fin (B + 7))
        (Tape.mk (some true :: ((blockCode d).reverse ++ L)) R)) = false :=
    incDigit_halted_false B (B + 5) (by omega) _
  rw [show 2 * d + 10 = (d + 4) + (((blockCode d).length + 1) + (1 + 1)) from by
    rw [blockCode_length]; omega]
  rw [DTM.run_add]
  rw [hdec]
  rw [DTM.run_add]
  rw [hwalk]
  rw [DTM.run_succ_of_not_halted _ 1 _ hhalt3]
  rw [incDigit_step_two B (⟨B + 4, by omega⟩) rfl ((blockCode d).reverse ++ L) R]
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt4]
  rw [incDigit_step_three B (⟨B + 5, by omega⟩) rfl
    (some true :: ((blockCode d).reverse ++ L)) R]
  rw [show (blockCode d).reverse = List.replicate (d + 2) (some true) ++ [some false] from by
    simp only [blockCode, List.reverse_cons, List.reverse_replicate]]
  rw [show List.replicate (d + 3) (some true) ++ some false :: L
      = some true :: (List.replicate (d + 2) (some true) ++ [some false] ++ L) from by
    rw [show d + 3 = d + 2 + 1 from by omega, List.replicate_succ, List.cons_append]
    rw [List.append_assoc, List.cons_append, List.nil_append]]
  rfl

/-- **一位加一（进位）**：块满（`d+2` 个真格、`d+1 = B`）时 `d+4` 步弹掉该块，
    头停在新终止空白上，右侧旧块内容成为垃圾。
    Add one with carry: a full block is popped in `d + 4` steps. -/
theorem incDigit_run_carry (B d : Nat) (hB : 0 < B) (hd : d + 1 = B) (L R : List Sym) :
    (incDigit B).run (d + 4)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 2) (some true) ++ some false :: L) (none :: R))) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7))
        (Tape.mk L (none :: List.replicate (d + 2) (some true) ++ none :: R)) := by
  have hread := incDigit_read_block B d (by omega) L R
  have hhalt : (incDigit B).halted
      (Config.mk (⟨d + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk L (blockCode d ++ none :: R))) = false :=
    incDigit_halted_false B (d + 3) (by omega) _
  rw [show d + 4 = (d + 3) + 1 from by omega]
  rw [DTM.run_add]
  rw [hread]
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt]
  rw [show blockCode d ++ none :: R
      = some false :: (List.replicate (d + 2) (some true) ++ none :: R) from by
    simp only [blockCode, List.cons_append]]
  rw [incDigit_step_carry B (⟨d + 3, by omega⟩)
    (by show (d + 3 : Nat) = B + 2; omega) L
    (List.replicate (d + 2) (some true) ++ none :: R)]
  rfl

end DTM

end Pnp
