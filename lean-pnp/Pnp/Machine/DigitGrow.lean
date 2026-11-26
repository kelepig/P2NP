/-
  文件：Pnp/Machine/DigitGrow.lean
  File: Pnp/Machine/DigitGrow.lean

  主题：把数字区**最右块的数值加一**的小机 `growBlock`（不判断进位，直接给块尾追加一个真格）。
  Topic: a machine `growBlock` that increments the **rightmost block** by appending one true cell.

  用途（B5 外层枚举 E）：E 的 B 进制计数器在「不进位」时的动作——最右块 `d ↦ d+1`
  等价于块尾多一个 `some true`，并在新的块尾之后补一个终止空白。
  Purpose (E): the no-carry step of E's base-`B` counter — appending one true cell to the
  rightmost block and writing a fresh trailing blank.

  入口约定：读写头停在块首 `some false` 上、块在右侧（即 `readDigitBack` 的出口形态）。
  Entry convention: the head sits on the block head `some false` with the block to the right
  (exactly the exit shape of `readDigitBack`).

  相位（5 状态，起点 1）：1 右行掠过非空白块；2 写 `some true` 并右移；3 写新终止空白；
  4 停机。
  Phases (start state 1): 1 walks right over the non-blank block, 2 writes `some true` and
  moves right, 3 writes the new trailing blank, 4 halts.
-/

import Pnp.Machine.DigitBack

namespace Pnp

namespace DTM

/-- 最右块加一机（不判断进位）。Rightmost-block incrementer (no carry test). -/
def growBlock : DTM 5 where
  step := fun st a =>
    match st.val with
    | 1 => (match a with
       | none => (⟨2, by omega⟩, a, Dir.stay)
       | _ => (⟨1, by omega⟩, a, Dir.right))
    | 2 => (⟨3, by omega⟩, some true, Dir.right)
    | 3 => (⟨4, by omega⟩, none, Dir.stay)
    | _ => (st, a, Dir.stay)
  start := 1
  accept := 4
  reject := 4

/-- 相位状态 0–3 一律不停机。Phase states 0–3 never halt. -/
theorem growBlock_halted_lt (st : Nat) (hst : st < 4) (t : Tape) :
    growBlock.halted (Config.mk (⟨st, by omega⟩ : Fin 5) t) = false := by
  have h1 : (⟨st, by omega⟩ : Fin 5) ≠ (⟨4, by omega⟩ : Fin 5) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega
  show ((⟨st, by omega⟩ : Fin 5) == (⟨4, by omega⟩ : Fin 5)
      || (⟨st, by omega⟩ : Fin 5) == (⟨4, by omega⟩ : Fin 5)) = false
  rw [beq_eq_false_iff_ne.mpr h1]
  rfl

/-- 相位 1 见非空白格：右移一格（左带任意）。 Phase 1 on a non-blank cell: move right. -/
theorem growBlock_step_one_move (L : List Sym) (a : Sym) (ha : a ≠ none) (R : List Sym) :
    growBlock.stepConfig
        (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (a :: R))) =
      Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk (a :: L) R) := by
  cases a with
  | none => exact absurd rfl ha
  | some b =>
      simp only [DTM.stepConfig, growBlock, Tape.read, Tape.write, Tape.move, Tape.moveRight,
        List.headD, List.tail]

/-- 相位 1 见空白：转入相位 2（原地）。 Phase 1 on the blank: switch to phase 2. -/
theorem growBlock_step_one_stop (L R : List Sym) :
    growBlock.stepConfig
        (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (none :: R))) =
      Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk L (none :: R)) := by
  simp only [DTM.stepConfig, growBlock, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]

/-- 相位 2：在终止空白处写 `some true` 并右移。 Phase 2: write `some true` and move right. -/
theorem growBlock_step_two (L R : List Sym) :
    growBlock.stepConfig
        (Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk L (none :: R))) =
      Config.mk (⟨3, by omega⟩ : Fin 5) (Tape.mk (some true :: L) R) := by
  simp only [DTM.stepConfig, growBlock, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]

/-- 相位 3：写新的终止空白并停机。 Phase 3: write the new trailing blank and halt. -/
theorem growBlock_step_three (L R : List Sym) :
    growBlock.stepConfig
        (Config.mk (⟨3, by omega⟩ : Fin 5) (Tape.mk L R)) =
      Config.mk (⟨4, by omega⟩ : Fin 5) (Tape.mk L (none :: R.tail)) := by
  simp only [DTM.stepConfig, growBlock, Tape.read, Tape.write, Tape.move, Tape.moveRight,
    List.headD, List.tail]

/-- 相位 1 右行一整段非空白块：`|l|+1` 步后停在块后的空白上，进入相位 2。
    Phase 1 walks right over a non-blank block and stops on the blank. -/
theorem growBlock_right : ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) →
    ∀ (L R : List Sym),
      growBlock.run (l.length + 1)
        (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (l ++ none :: R))) =
      Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk (l.reverse ++ L) (none :: R))
  | [], _, L, R => by
      show growBlock.run 1
          (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (none :: R))) =
        Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk L (none :: R))
      rw [DTM.run_succ_of_not_halted _ 0 _
        (growBlock_halted_lt 1 (by omega) _)]
      show growBlock.stepConfig (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (none :: R))) =
        Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk L (none :: R))
      rw [growBlock_step_one_stop L R]
  | a :: t, hl, L, R => by
      have ha : a ≠ none := hl a List.mem_cons_self
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (List.mem_cons_of_mem _ hy)
      show growBlock.run ((t.length + 1) + 1)
          (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (a :: (t ++ none :: R)))) =
        Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk ((a :: t).reverse ++ L) (none :: R))
      rw [DTM.run_succ_of_not_halted _ (t.length + 1) _
        (growBlock_halted_lt 1 (by omega) _)]
      show growBlock.run (t.length + 1)
          (growBlock.stepConfig
            (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (a :: (t ++ none :: R))))) =
        Config.mk (⟨2, by omega⟩ : Fin 5) (Tape.mk ((a :: t).reverse ++ L) (none :: R))
      rw [growBlock_step_one_move L a ha]
      rw [growBlock_right t ht (a :: L) R]
      rw [show (a :: t).reverse ++ L = t.reverse ++ (a :: L) from by
        simp [List.reverse_cons, List.append_assoc]]

/-- **最右块加一**：`d+6` 步后最右块 `d ↦ d+1`（块尾多一个真格），
    头停在新终止空白上，右侧保留余下纸带。
    Incrementing the rightmost block: after `d + 6` steps the block `d` becomes `d + 1`,
    the head resting on the fresh trailing blank. -/
theorem growBlock_run (d : Nat) (L R : List Sym) :
    growBlock.run (d + 6)
        (Config.mk (⟨1, by omega⟩ : Fin 5) (Tape.mk L (blockCode d ++ none :: R))) =
      Config.mk (⟨4, by omega⟩ : Fin 5)
        (Tape.mk (List.replicate (d + 3) (some true) ++ some false :: L) (none :: R.tail)) := by
  -- 相位 1：右行整块 `blockCode d`（全非空白）
  have hwalk := growBlock_right (blockCode d) (blockCode_ne_none d) L R
  -- 相位 2、3 的停机性
  have hhalt2 : growBlock.halted
      (Config.mk (⟨2, by omega⟩ : Fin 5)
        (Tape.mk ((blockCode d).reverse ++ L) (none :: R))) =
      false := growBlock_halted_lt 2 (by omega) _
  have hhalt3 : growBlock.halted
      (Config.mk (⟨3, by omega⟩ : Fin 5)
        (Tape.mk (some true :: ((blockCode d).reverse ++ L)) R)) =
      false := growBlock_halted_lt 3 (by omega) _
  -- 拼装：`(|blockCode d| + 1)` 步右行 + 1 步写真格 + 1 步写空白
  rw [show d + 6 = ((blockCode d).length + 1) + (1 + 1) from by
    have hlen := blockCode_length d
    omega]
  rw [DTM.run_add]
  rw [hwalk]
  rw [DTM.run_succ_of_not_halted _ 1 _ hhalt2]
  rw [growBlock_step_two]
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt3]
  rw [growBlock_step_three]
  show growBlock.run 0
      (Config.mk (⟨4, by omega⟩ : Fin 5)
        (Tape.mk (some true :: ((blockCode d).reverse ++ L)) (none :: R.tail))) = _
  -- 形态对齐：块的反转 + 追加的真格 = 新块的反转
  rw [show (blockCode d).reverse = List.replicate (d + 2) (some true) ++ [some false] from by
    simp only [blockCode, List.reverse_cons, List.reverse_replicate]]
  rw [show List.replicate (d + 3) (some true) ++ some false :: L
      = some true :: (List.replicate (d + 2) (some true) ++ [some false] ++ L) from by
    rw [show d + 3 = d + 2 + 1 from by omega, List.replicate_succ, List.cons_append]
    rw [List.append_assoc, List.cons_append, List.nil_append]]
  rfl

end DTM

end Pnp
