/-
  文件：Pnp/Machine/DigitChain.lean
  File: Pnp/Machine/DigitChain.lean

  主题：**进位链整机** `incChain`——给数字区加一，直到某位不进位为止（一次完整的 B 进制自增）。
  Topic: `incChain`, the carry-chain machine: one complete base-`B` increment of the digit area.

  与 `incDigit`（#278）的唯一差别：块满时不再停机，而是把块首改写成空白后**回到起始态 0**
  （头正好停在新终止空白上），于是下一轮自动作用于左侧的下一位；某位未满（走出成长相位）
  才回到终止态 `B+6`。由于 `incDigit` 的「弹出」出口态与「加一」出口态本来就不同，
  这里用状态值区分「继续进位」与「一轮结束」，不需要额外判断电路。
  The only change from `incDigit`: a full block no longer halts — the head is blanked and the
  machine returns to state 0, so the next round acts on the digit to the left. A non-full digit
  (growth phases) still ends in the terminal state `B+6`.

  `incChain_run`：若数字序列 `ds`（低位在前）里至少有一位未满，则整链在 `chainCost B ds` 步内
  停机，数字序列变成 `incSucc B ds`（进位链的算术后继）。
  `incChain_run`: if at least one digit of `ds` is not full, the chain halts within `chainCost`
  steps with the digit sequence replaced by its arithmetic successor `incSucc B ds`.
-/

import Pnp.Machine.DigitRound

namespace Pnp

namespace DTM

/-- 进位链整机：与 `incDigit` 同表，只把「块满 ⇒ 弹块」的出口态从终止态改成起始态 0。
    The carry-chain machine: `incDigit`'s table, with the pop branch looping back to state 0. -/
def incChain (B : Nat) : DTM (B + 7) where
  step := fun st a =>
    if st.val = 0 then (⟨1, by omega⟩, a, Dir.left)
    else if h1 : st.val < B + 2 then
      (match a with
       | some true => (⟨st.val + 1, by omega⟩, a, Dir.left)
       | some false => (⟨B + 3, by omega⟩, a, Dir.stay)
       | none => (⟨B + 6, by omega⟩, a, Dir.stay))
    else if h2 : st.val = B + 2 then
      (match a with
       | some false => (⟨0, by omega⟩, none, Dir.stay)
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
theorem incChain_halted_false (B s : Nat) (hs : s < B + 6) (t : Tape) :
    (incChain B).halted (Config.mk (⟨s, by omega⟩ : Fin (B + 7)) t) = false := by
  have hne : (⟨s, by omega⟩ : Fin (B + 7)) ≠ (⟨B + 6, by omega⟩ : Fin (B + 7)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  unfold DTM.halted incChain
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 起始步：状态 0 一律左移一格。 First step: state 0 moves left. -/
theorem incChain_step_start (B : Nat) (a : Sym) (X R : List Sym) :
    (incChain B).stepConfig
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: X) (none :: R))) =
      Config.mk (⟨1, by omega⟩ : Fin (B + 7)) (Tape.mk X (a :: none :: R)) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  simp

/-- 计数步：非起始状态读到真格就左移一格、状态加一。 Counting step on a true cell. -/
theorem incChain_step_true (B s : Nat) (hs0 : s ≠ 0) (hs : s < B + 2)
    (a : Sym) (X R : List Sym) :
    (incChain B).stepConfig
        (Config.mk (⟨s, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: X) (some true :: R))) =
      Config.mk (⟨s + 1, by omega⟩ : Fin (B + 7)) (Tape.mk X (a :: some true :: R)) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg hs0, dif_pos hs]

/-- 决策步（块未满）：计数状态读到块首 `some false`，转入成长相位（原地）。
    Decision step (not full): a counting state on the block head switches to growth. -/
theorem incChain_step_false (B s : Nat) (hs0 : s ≠ 0) (hs : s < B + 2)
    (L R : List Sym) :
    (incChain B).stepConfig
        (Config.mk (⟨s, by omega⟩ : Fin (B + 7)) (Tape.mk L (some false :: R))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (some false :: R)) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg hs0, dif_pos hs]

/-- 进位步：块满时块首改写成空白，**回到起始态 0**（头停在新终止空白上）。
    Carry step: the full block's head is blanked and the machine returns to state 0. -/
theorem incChain_step_carry (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 2)
    (L R : List Sym) :
    (incChain B).stepConfig (Config.mk st (Tape.mk L (some false :: R))) =
      Config.mk (⟨0, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R)) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]

/-- 成长相位 1：非空白格右移一格。 Growth phase 1: move right over a non-blank cell. -/
theorem incChain_step_walk (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 3)
    (L : List Sym) (a : Sym) (ha : a ≠ none) (R : List Sym) :
    (incChain B).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk (a :: L) R) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]

/-- 成长相位 1：见空白转入相位 2。 Growth phase 1: the blank switches to phase 2. -/
theorem incChain_step_walk_stop (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 3)
    (L R : List Sym) :
    (incChain B).stepConfig (Config.mk st (Tape.mk L (none :: R))) =
      Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R)) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]

/-- 成长相位 2：在终止空白处写 `some true` 并右移。 Phase 2: write `some true`, move right. -/
theorem incChain_step_two (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 4)
    (L R : List Sym) :
    (incChain B).stepConfig (Config.mk st (Tape.mk L (none :: R))) =
      Config.mk (⟨B + 5, by omega⟩ : Fin (B + 7)) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_left (by omega)]

/-- 成长相位 3：写新终止空白并停机。 Phase 3: write the trailing blank and halt. -/
theorem incChain_step_three (B : Nat) (st : Fin (B + 7)) (hval : st.val = B + 5)
    (L R : List Sym) :
    (incChain B).stepConfig (Config.mk st (Tape.mk L R)) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R.tail)) := by
  simp only [DTM.stepConfig, incChain, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega)]

/-- 连续读 `m` 个真格：状态 `s` 变 `s + m`。 Reading `m` true cells. -/
theorem incChain_count (B : Nat) :
    ∀ (m s : Nat), (hs0 : s ≠ 0) → (hs : s + m < B + 2) → ∀ (X R : List Sym),
      (incChain B).run m
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
      have hhalt : (incChain B).halted
          (Config.mk (⟨s, by omega⟩ : Fin (B + 7))
            (Tape.mk (some true :: (List.replicate m (some true) ++ X)) (some true :: R)))
          = false := incChain_halted_false B s (by omega) _
      rw [show List.replicate (m + 1) (some true) ++ X
          = some true :: (List.replicate m (some true) ++ X) from by
        rw [List.replicate_succ, List.cons_append]]
      rw [DTM.run_succ_of_not_halted _ m _ hhalt]
      rw [incChain_step_true B s hs0 hs2 (some true) (List.replicate m (some true) ++ X) R]
      rw [ih (s + 1) (by omega) (by omega) X (some true :: R)]
      rw [replicate_append_cons]
      rw [List.replicate_succ, List.cons_append]
      simp only [Nat.add_comm, Nat.add_left_comm]

/-- **读块段**：`d+3` 步从区尾空白走到块首。 Reading leg: `d+3` steps to the block head. -/
theorem incChain_read_block (B d : Nat) (hd : d < B) (L R : List Sym) :
    (incChain B).run (d + 3)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 2) (some true) ++ some false :: L) (none :: R))) =
      Config.mk (⟨d + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk L (blockCode d ++ none :: R)) := by
  rw [show List.replicate (d + 2) (some true) ++ some false :: L
      = some true :: (List.replicate (d + 1) (some true) ++ some false :: L) from by
    rw [show d + 2 = d + 1 + 1 from by omega, List.replicate_succ, List.cons_append]]
  have hhalt0 : (incChain B).halted
      (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
        (Tape.mk (some true :: (List.replicate (d + 1) (some true) ++ some false :: L))
          (none :: R)))
      = false := incChain_halted_false B 0 (by omega) _
  rw [DTM.run_succ_of_not_halted _ (d + 2) _ hhalt0]
  rw [incChain_step_start B (some true)
    (List.replicate (d + 1) (some true) ++ some false :: L) R]
  have haux := incChain_count B (d + 1) 1 (by omega) (by omega)
    (some false :: L) (none :: R)
  have hhalt1 : (incChain B).halted
      ((incChain B).run (d + 1)
        (Config.mk (⟨1, by omega⟩ : Fin (B + 7))
          (Tape.mk (List.replicate (d + 1) (some true) ++ some false :: L)
            (some true :: none :: R)))) = false := by
    rw [haux]
    exact incChain_halted_false B (1 + (d + 1)) (by omega) _
  rw [DTM.run_succ_last _ (d + 1) _ hhalt1]
  rw [haux]
  rw [show List.replicate (d + 1) (some true) ++ some true :: none :: R
      = some true :: (List.replicate d (some true) ++ some true :: none :: R) from by
    rw [List.replicate_succ, List.cons_append]]
  rw [incChain_step_true B (1 + (d + 1)) (by omega) (by omega) (some false) L
    (List.replicate d (some true) ++ some true :: none :: R)]
  rw [replicate_append_cons]
  simp only [blockCode, show d + 2 = d + 1 + 1 from by omega, List.replicate_succ,
    List.cons_append]
  simp only [Nat.add_comm, Nat.add_left_comm]

/-- 成长相位掠过整段非空白块：`|l|+1` 步后停在块后空白、状态 `B+4`。
    The growth phase walks over a non-blank block in `|l|+1` steps. -/
theorem incChain_walk : ∀ (B : Nat) (l : List Sym), (∀ y ∈ l, y ≠ none) →
    ∀ (L R : List Sym),
      (incChain B).run (l.length + 1)
        (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (l ++ none :: R))) =
      Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk (l.reverse ++ L) (none :: R))
  | B, [], _, L, R => by
      show (incChain B).run 1
          (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))
      rw [DTM.run_succ_of_not_halted _ 0 _
        (incChain_halted_false B (B + 3) (by omega) _)]
      show (incChain B).stepConfig
          (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7)) (Tape.mk L (none :: R))
      exact incChain_step_walk_stop B (⟨B + 3, by omega⟩) rfl L R
  | B, a :: t, hl, L, R => by
      have ha : a ≠ none := hl a List.mem_cons_self
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (List.mem_cons_of_mem _ hy)
      show (incChain B).run ((t.length + 1) + 1)
          (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7)) (Tape.mk L (a :: (t ++ none :: R)))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
          (Tape.mk ((a :: t).reverse ++ L) (none :: R))
      rw [DTM.run_succ_of_not_halted _ (t.length + 1) _
        (incChain_halted_false B (B + 3) (by omega) _)]
      show (incChain B).run (t.length + 1)
          ((incChain B).stepConfig
            (Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
              (Tape.mk L (a :: (t ++ none :: R))))) =
        Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
          (Tape.mk ((a :: t).reverse ++ L) (none :: R))
      rw [incChain_step_walk B (⟨B + 3, by omega⟩) rfl L a ha]
      rw [incChain_walk B t ht (a :: L) R]
      rw [show (a :: t).reverse ++ L = t.reverse ++ (a :: L) from by
        simp [List.reverse_cons, List.append_assoc]]

/-- **不进位的一轮**：最低位 `d`（`d+1 < B`）加一后停机。
    One round without carry: the lowest digit grows by one and the machine halts. -/
theorem incChain_round_grow (B d : Nat) (hd : d + 1 < B) (ds : List Nat)
    (L G : List Sym) :
    (incChain B).run (2 * d + 10)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (areaL (d :: ds) ++ L) (none :: G))) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL ((d + 1) :: ds) ++ L) (none :: G.tail)) := by
  -- 读块 + 决策（原地转入成长相位）
  have hread := incChain_read_block B d (by omega) (areaL ds ++ L) G
  have hdec : (incChain B).run (d + 4)
      (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL (d :: ds) ++ L) (none :: G))) =
      Config.mk (⟨B + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL ds ++ L) (blockCode d ++ none :: G)) := by
    have hhalt : (incChain B).halted
        (Config.mk (⟨d + 3, by omega⟩ : Fin (B + 7))
          (Tape.mk (areaL ds ++ L) (blockCode d ++ none :: G))) = false :=
      incChain_halted_false B (d + 3) (by omega) _
    rw [areaL_head_append]
    rw [show d + 4 = (d + 3) + 1 from by omega, DTM.run_add, hread]
    rw [show (1 : Nat) = 0 + 1 from rfl]
    rw [DTM.run_succ_of_not_halted _ 0 _ hhalt]
    rw [show blockCode d ++ none :: G
        = some false :: (List.replicate (d + 2) (some true) ++ none :: G) from by
      simp only [blockCode, List.cons_append]]
    rw [incChain_step_false B (d + 3) (by omega) (by omega)]
    rfl
  -- 成长相位 + 写新块尾 + 写新终止空白
  have hwalk := incChain_walk B (blockCode d) (blockCode_ne_none d) (areaL ds ++ L) G
  have hhalt3 : (incChain B).halted
      (Config.mk (⟨B + 4, by omega⟩ : Fin (B + 7))
        (Tape.mk ((blockCode d).reverse ++ (areaL ds ++ L)) (none :: G))) = false :=
    incChain_halted_false B (B + 4) (by omega) _
  have hhalt4 : (incChain B).halted
      (Config.mk (⟨B + 5, by omega⟩ : Fin (B + 7))
        (Tape.mk (some true :: ((blockCode d).reverse ++ (areaL ds ++ L))) G)) = false :=
    incChain_halted_false B (B + 5) (by omega) _
  rw [show 2 * d + 10 = (d + 4) + (((blockCode d).length + 1) + (1 + 1)) from by
    rw [blockCode_length]; omega]
  rw [DTM.run_add, hdec]
  rw [DTM.run_add, hwalk]
  rw [DTM.run_succ_of_not_halted _ 1 _ hhalt3]
  rw [incChain_step_two B (⟨B + 4, by omega⟩) rfl
    ((blockCode d).reverse ++ (areaL ds ++ L)) G]
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt4]
  rw [incChain_step_three B (⟨B + 5, by omega⟩) rfl
    (some true :: ((blockCode d).reverse ++ (areaL ds ++ L))) G]
  rw [areaL_head_append]
  rw [show (blockCode d).reverse = List.replicate (d + 2) (some true) ++ [some false] from by
    simp only [blockCode, List.reverse_cons, List.reverse_replicate]]
  rw [show List.replicate (d + 3) (some true) ++ some false :: (areaL ds ++ L)
      = some true :: (List.replicate (d + 2) (some true) ++ [some false] ++ (areaL ds ++ L))
      from by
    rw [show d + 3 = d + 2 + 1 from by omega, List.replicate_succ, List.cons_append]
    rw [List.append_assoc, List.cons_append, List.nil_append]]
  rfl

/-- **进位的一轮**：块满（`d+1 = B`）时弹块后**回到起始态 0**，头停在新终止空白上。
    One carry round: the full block is popped and the machine returns to state 0. -/
theorem incChain_round_pop (B d : Nat) (hB : 0 < B) (hd : d + 1 = B) (ds : List Nat)
    (L G : List Sym) :
    (incChain B).run (d + 4)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (areaL (d :: ds) ++ L) (none :: G))) =
      Config.mk (⟨0, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL ds ++ L)
          (none :: (List.replicate (d + 2) (some true) ++ none :: G))) := by
  have hread := incChain_read_block B d (by omega) (areaL ds ++ L) G
  have hhalt : (incChain B).halted
      (Config.mk (⟨d + 3, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL ds ++ L) (blockCode d ++ none :: G))) = false :=
    incChain_halted_false B (d + 3) (by omega) _
  rw [areaL_head_append]
  rw [show d + 4 = (d + 3) + 1 from by omega, DTM.run_add, hread]
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt]
  rw [show blockCode d ++ none :: G
      = some false :: (List.replicate (d + 2) (some true) ++ none :: G) from by
    simp only [blockCode, List.cons_append]]
  rw [incChain_step_carry B (⟨d + 3, by omega⟩)
    (by show (d + 3 : Nat) = B + 2; omega) (areaL ds ++ L)
    (List.replicate (d + 2) (some true) ++ none :: G)]
  rfl

/-- 进位链的算术后继：某位未满就加一并停；该位满就弹掉它、继续往左。
    The arithmetic successor along the carry chain. -/
def incSucc (B : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => if d + 1 < B then (d + 1) :: ds else incSucc B ds

/-- 进位链的总步数。 Total step count of the carry chain. -/
def chainCost (B : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => if d + 1 < B then 2 * d + 10 else (d + 4) + chainCost B ds

/-- **进位链主定理**：若数字序列至少有一位未满，则整链在 `chainCost B ds` 步内停机，
    数字序列变成 `incSucc B ds`，头回到终止空白上。
    Main theorem of the carry chain. -/
theorem incChain_run (B : Nat) (hB : 0 < B) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < B) → (∃ d, d ∈ ds ∧ d + 1 < B) →
      ∀ (L G : List Sym), ∃ G' : List Sym,
        (incChain B).run (chainCost B ds)
            (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
              (Tape.mk (areaL ds ++ L) (none :: G))) =
          Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7))
            (Tape.mk (areaL (incSucc B ds) ++ L) (none :: G'))
  | [], _, hex, L, G => by
      obtain ⟨d, hd, _⟩ := hex
      exact (List.not_mem_nil hd).elim
  | d :: ds, hlt, hex, L, G => by
      by_cases hg : d + 1 < B
      · have hcost : chainCost B (d :: ds) = 2 * d + 10 := by
          simp only [chainCost, if_pos hg]
        have hsucc : incSucc B (d :: ds) = (d + 1) :: ds := by
          simp only [incSucc, if_pos hg]
        refine ⟨G.tail, ?_⟩
        rw [hcost, hsucc]
        exact incChain_round_grow B d hg ds L G
      · have hd1 : d + 1 = B := by
          have hd' := hlt d List.mem_cons_self
          omega
        have hcost : chainCost B (d :: ds) = (d + 4) + chainCost B ds := by
          simp only [chainCost, if_neg hg]
        have hsucc : incSucc B (d :: ds) = incSucc B ds := by
          simp only [incSucc, if_neg hg]
        have hlt' : ∀ e ∈ ds, e < B := fun e he => hlt e (List.mem_cons_of_mem _ he)
        have hex' : ∃ e, e ∈ ds ∧ e + 1 < B := by
          obtain ⟨e, he, hge⟩ := hex
          rcases List.mem_cons.mp he with rfl | he'
          · omega
          · exact ⟨e, he', hge⟩
        obtain ⟨G₁, hrun₁⟩ := incChain_run B hB ds hlt' hex' L
          (List.replicate (d + 2) (some true) ++ none :: G)
        refine ⟨G₁, ?_⟩
        rw [hcost, hsucc, DTM.run_add, incChain_round_pop B d hB hd1 ds L G]
        exact hrun₁

/-- 后继序列不会变长（进位只会弹块）。 The successor sequence never grows. -/
theorem incSucc_length_le (B : Nat) : ∀ (ds : List Nat), (incSucc B ds).length ≤ ds.length
  | [] => by simp only [incSucc, List.length_nil]; exact Nat.le_refl 0
  | d :: ds => by
      by_cases hg : d + 1 < B
      · simp only [incSucc, if_pos hg, List.length_cons]
        omega
      · simp only [incSucc, if_neg hg, List.length_cons]
        exact Nat.le_trans (incSucc_length_le B ds) (by omega)

/-- 进位链的步数线性上界：每位至多 `2B+10` 步。
    Linear step bound of the carry chain: at most `2B+10` steps per digit. -/
theorem chainCost_le (B : Nat) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < B) → chainCost B ds ≤ ds.length * (2 * B + 10)
  | [], _ => by
      show 0 ≤ [].length * (2 * B + 10)
      omega
  | d :: ds, hlt => by
      have hd : d < B := hlt d List.mem_cons_self
      by_cases hg : d + 1 < B
      · have hcost : chainCost B (d :: ds) = 2 * d + 10 := by
          simp only [chainCost, if_pos hg]
        rw [hcost, List.length_cons]
        calc 2 * d + 10 ≤ 2 * B + 10 := by omega
          _ = 1 * (2 * B + 10) := (Nat.one_mul _).symm
          _ ≤ (ds.length + 1) * (2 * B + 10) := Nat.mul_le_mul_right _ (by omega)
      · have hd1 : d + 1 = B := by omega
        have hcost : chainCost B (d :: ds) = (d + 4) + chainCost B ds := by
          simp only [chainCost, if_neg hg]
        have hlt' : ∀ e ∈ ds, e < B := fun e he => hlt e (List.mem_cons_of_mem _ he)
        have ih := chainCost_le B ds hlt'
        have hmid : (d + 4) + chainCost B ds
            ≤ ds.length * (2 * B + 10) + (2 * B + 10) := by
          have hb : d + 4 ≤ 2 * B + 10 := by omega
          calc (d + 4) + chainCost B ds
              ≤ (2 * B + 10) + ds.length * (2 * B + 10) := Nat.add_le_add hb ih
            _ = ds.length * (2 * B + 10) + (2 * B + 10) := Nat.add_comm _ _
        rw [hcost, List.length_cons]
        calc (d + 4) + chainCost B ds
            ≤ ds.length * (2 * B + 10) + (2 * B + 10) := hmid
          _ = (ds.length + 1) * (2 * B + 10) :=
              (Nat.succ_mul ds.length (2 * B + 10)).symm

end DTM

end Pnp
