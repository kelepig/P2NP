/-
  文件：Pnp/Machine/SeekMark.lean
  主题：模拟区「找头标记」机 `seekMark`。

  单带模拟器的模拟区是一段非空白符号串，每个被模拟格编码成 3 个符号：

      [符号编码 2 个符号（`symCode`）] ++ [头标记：some true / some false]

  区域两端是空白（分隔符），因此区域可以可靠定位。每模拟一步，机器需要先
  从区域起点向右逐格扫描，找到头标记格。

  本文件给出：
    - `cellCode` / `codeCells`：一格 / 一串格的编码（长度 3k、全非空白）；
    - `seekMark`（4 状态）：从格起点出发，逐格扫描，遇到标记即接受；
    - **`seekMark_run`**：扫描 `3m + 3` 步后停在标记格，左侧为扫过符号的逆序。
-/

import Pnp.Classes
import Pnp.Machine.SymCode

namespace Pnp

namespace DTM

/-- 一个被模拟格的 3 符号编码：2 个符号编码 + 1 个头标记（非空白）。 -/
def cellCode (p : Sym × Bool) : List Sym :=
  symCode p.1 ++ [if p.2 then some true else some false]

/-- 一串格的编码（行优先拼接）。 -/
def codeCells (cs : List (Sym × Bool)) : List Sym := cs.flatMap cellCode

/-- 单格编码长度 3。 -/
theorem cellCode_length (p : Sym × Bool) : (cellCode p).length = 3 := by
  unfold cellCode
  rw [List.length_append, symCode_length]
  cases p.2 <;> rfl

/-- 单格编码不含空白。 -/
theorem cellCode_ne_none (p : Sym × Bool) : ∀ x ∈ cellCode p, x ≠ none := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact symCode_ne_none p.1 x h
  · simp only [List.mem_singleton] at h
    rw [h]
    cases p.2 <;> decide

/-- 编码总长度是格数的 3 倍。 -/
theorem codeCells_length (cs : List (Sym × Bool)) :
    (codeCells cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons p ps ih =>
      have hsplit : codeCells (p :: ps) = cellCode p ++ codeCells ps := by
        simp [codeCells]
      rw [hsplit, List.length_append, cellCode_length, ih, List.length_cons]
      omega

/-- 编码不含空白。 -/
theorem codeCells_ne_none (cs : List (Sym × Bool)) :
    ∀ x ∈ codeCells cs, x ≠ none := by
  intro x hx
  simp only [codeCells, List.mem_flatMap] at hx
  obtain ⟨p, _, hp⟩ := hx
  exact cellCode_ne_none p x hp

/-- 编码对列表拼接相容。 -/
theorem codeCells_append (a b : List (Sym × Bool)) :
    codeCells (a ++ b) = codeCells a ++ codeCells b := by
  simp [codeCells]

/-- 找标记机：0 = 格起点，1 = 第二符号，2 = 头标记位，3 = 接受。 -/
def seekMark : DTM 4 where
  step := fun s a =>
    if s.val = 0 then (1, a, Dir.right)
    else if s.val = 1 then (2, a, Dir.right)
    else if s.val = 2 then
      if a = some true then (3, a, Dir.stay) else (0, a, Dir.right)
    else (s, a, Dir.stay)
  start := 0
  accept := 3
  reject := 3

/-- 一格无标记：走三步回到格起点，左侧加上这一格的逆序。 -/
theorem seekMark_steps_false (L : List Sym) (b0 b1 : Sym) (tail : List Sym) :
    seekMark.run 3
        { state := (0 : Fin 4),
          tape := { left := L, right := b0 :: b1 :: some false :: tail } } =
      { state := (0 : Fin 4),
        tape := { left := some false :: b1 :: b0 :: L, right := tail } } := by
  have h0 : seekMark.halted
      { state := (0 : Fin 4),
        tape := { left := L, right := b0 :: b1 :: some false :: tail } } = false := by
    simp [DTM.halted, seekMark]
  have s1 : seekMark.stepConfig
      { state := (0 : Fin 4),
        tape := { left := L, right := b0 :: b1 :: some false :: tail } }
      = { state := (1 : Fin 4), tape := { left := b0 :: L, right := b1 :: some false :: tail } } := by
    simp [DTM.stepConfig, seekMark, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  have h1 : seekMark.halted
      { state := (1 : Fin 4),
        tape := { left := b0 :: L, right := b1 :: some false :: tail } } = false := by
    simp [DTM.halted, seekMark]
  have s2 : seekMark.stepConfig
      { state := (1 : Fin 4),
        tape := { left := b0 :: L, right := b1 :: some false :: tail } }
      = { state := (2 : Fin 4),
          tape := { left := b1 :: b0 :: L, right := some false :: tail } } := by
    simp [DTM.stepConfig, seekMark, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  have h2 : seekMark.halted
      { state := (2 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some false :: tail } } = false := by
    simp [DTM.halted, seekMark]
  have s3 : seekMark.stepConfig
      { state := (2 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some false :: tail } }
      = { state := (0 : Fin 4),
          tape := { left := some false :: b1 :: b0 :: L, right := tail } } := by
    simp [DTM.stepConfig, seekMark, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  show seekMark.run (2 + 1)
      { state := (0 : Fin 4),
        tape := { left := L, right := b0 :: b1 :: some false :: tail } } = _
  rw [DTM.run_succ_of_not_halted seekMark 2 _ h0, s1]
  show seekMark.run (1 + 1)
      { state := (1 : Fin 4),
        tape := { left := b0 :: L, right := b1 :: some false :: tail } } = _
  rw [DTM.run_succ_of_not_halted seekMark 1 _ h1, s2]
  show seekMark.run (0 + 1)
      { state := (2 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some false :: tail } } = _
  rw [DTM.run_succ_of_not_halted seekMark 0 _ h2, s3]
  simp [DTM.run]

/-- 标记格：走三步后接受，停在标记位上。 -/
theorem seekMark_steps_true (L : List Sym) (b0 b1 : Sym) (tail : List Sym) :
    seekMark.run 3
        { state := (0 : Fin 4),
          tape := { left := L, right := b0 :: b1 :: some true :: tail } } =
      { state := (3 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some true :: tail } } := by
  have h0 : seekMark.halted
      { state := (0 : Fin 4),
        tape := { left := L, right := b0 :: b1 :: some true :: tail } } = false := by
    simp [DTM.halted, seekMark]
  have s1 : seekMark.stepConfig
      { state := (0 : Fin 4),
        tape := { left := L, right := b0 :: b1 :: some true :: tail } }
      = { state := (1 : Fin 4), tape := { left := b0 :: L, right := b1 :: some true :: tail } } := by
    simp [DTM.stepConfig, seekMark, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  have h1 : seekMark.halted
      { state := (1 : Fin 4),
        tape := { left := b0 :: L, right := b1 :: some true :: tail } } = false := by
    simp [DTM.halted, seekMark]
  have s2 : seekMark.stepConfig
      { state := (1 : Fin 4),
        tape := { left := b0 :: L, right := b1 :: some true :: tail } }
      = { state := (2 : Fin 4),
          tape := { left := b1 :: b0 :: L, right := some true :: tail } } := by
    simp [DTM.stepConfig, seekMark, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  have h2 : seekMark.halted
      { state := (2 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some true :: tail } } = false := by
    simp [DTM.halted, seekMark]
  have s3 : seekMark.stepConfig
      { state := (2 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some true :: tail } }
      = { state := (3 : Fin 4),
          tape := { left := b1 :: b0 :: L, right := some true :: tail } } := by
    simp [DTM.stepConfig, seekMark, Tape.read, Tape.write, Tape.move, Tape.moveRight]
  show seekMark.run (2 + 1)
      { state := (0 : Fin 4),
        tape := { left := L, right := b0 :: b1 :: some true :: tail } } = _
  rw [DTM.run_succ_of_not_halted seekMark 2 _ h0, s1]
  show seekMark.run (1 + 1)
      { state := (1 : Fin 4),
        tape := { left := b0 :: L, right := b1 :: some true :: tail } } = _
  rw [DTM.run_succ_of_not_halted seekMark 1 _ h1, s2]
  show seekMark.run (0 + 1)
      { state := (2 : Fin 4),
        tape := { left := b1 :: b0 :: L, right := some true :: tail } } = _
  rw [DTM.run_succ_of_not_halted seekMark 0 _ h2, s3]
  simp [DTM.run]

/-- 找标记：前 `m` 格无标记、第 `m+1` 格是标记格，`3m + 3` 步后接受。 -/
theorem seekMark_run : ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) →
    ∀ (s : Sym) (rest : List (Sym × Bool)) (L : List Sym),
      seekMark.run (3 * cs.length + 3)
        { state := (0 : Fin 4),
          tape := { left := L,
                    right := codeCells cs ++ cellCode (s, true) ++ codeCells rest } } =
      { state := (3 : Fin 4),
        tape := { left := List.reverse (codeCells cs ++ symCode s) ++ L,
                  right := some true :: codeCells rest } }
  | [], _, s, rest, L => by
      -- 标记格就在眼前
      obtain ⟨b0, b1, hs⟩ : ∃ b0 b1 : Sym, symCode s = [b0, b1] := by
        cases s with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hcell : cellCode (s, true) = b0 :: b1 :: some true :: [] := by
        simp [cellCode, hs]
      have hgoal := seekMark_steps_true L b0 b1 (codeCells rest)
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, codeCells, List.flatMap_nil,
        List.nil_append, hcell, hs, List.reverse_cons, List.cons_append]
      exact hgoal
  | p :: ps, hflags, s, rest, L => by
      have hp : p.2 = false := hflags p List.mem_cons_self
      have hps : ∀ q ∈ ps, q.2 = false :=
        fun q hq => hflags q (List.mem_cons_of_mem _ hq)
      -- 展开这一格
      obtain ⟨c0, c1, hc⟩ : ∃ c0 c1 : Sym, symCode p.1 = [c0, c1] := by
        cases p.1 with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hcell : cellCode p = [c0, c1, some false] := by
        simp [cellCode, hc, hp]
      -- 第一格走三步
      have hhead : codeCells (p :: ps) = [c0, c1, some false] ++ codeCells ps := by
        simp [codeCells, List.flatMap_cons, hcell]
      rw [hhead]
      rw [show 3 * (p :: ps).length + 3 = 3 + (3 * ps.length + 3) by
        simp only [List.length_cons]
        omega]
      rw [DTM.run_add seekMark 3 (3 * ps.length + 3)]
      rw [List.append_assoc, List.append_assoc]
      change seekMark.run (3 * ps.length + 3)
        (seekMark.run 3
          { state := (0 : Fin 4),
            tape := { left := L,
                      right := c0 :: c1 :: some false
                        :: (codeCells ps ++ (cellCode (s, true) ++ codeCells rest)) } }) = _
      rw [seekMark_steps_false L c0 c1 (codeCells ps ++ (cellCode (s, true) ++ codeCells rest))]
      rw [← List.append_assoc]
      rw [seekMark_run ps hps s rest (some false :: c1 :: c0 :: L)]
      -- 收尾：左侧逆序拼接
      have hfin : List.reverse ([c0, c1, some false] ++ (codeCells ps ++ symCode s)) ++ L
          = List.reverse (codeCells ps ++ symCode s) ++ (some false :: c1 :: c0 :: L) := by
        rw [List.reverse_append]
        simp [List.reverse_cons]
      rw [← hfin]
      rw [← List.append_assoc]

end DTM

end Pnp
