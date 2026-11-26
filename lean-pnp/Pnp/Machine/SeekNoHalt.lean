/-
  文件：Pnp/Machine/SeekNoHalt.lean
  主题：`seekMark` 在整段扫描过程中（`3|cs|+3` 步内）**不会提前停机**。

  用途：`run_embed` / `tagged_run` 要求子机在搬运区间内不停机；
  `seekMark` 只有到达标记位（最后一步）才进入状态 3。本文件证明前 `m` 步
  （`m < 3|cs|+3`）都停在相位 0/1/2，因而 `halted = false`。
-/

import Pnp.Machine.SeekMark

namespace Pnp

namespace DTM

/-- 从相位 0 出发、不超过 2 步，`seekMark` 不会停机（纸带任意）。 -/
theorem seekMark_halted_small (L R : List Sym) :
    ∀ m, m ≤ 2 →
      seekMark.halted
        (seekMark.run m { state := (0 : Fin 4), tape := { left := L, right := R } }) = false := by
  intro m hm
  have hcase : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · change seekMark.halted { state := (0 : Fin 4), tape := { left := L, right := R } } = false
    simp [DTM.halted, seekMark]
  · have h0 : seekMark.halted
        { state := (0 : Fin 4), tape := { left := L, right := R } } = false := by
      simp [DTM.halted, seekMark]
    rw [DTM.run_succ_of_not_halted seekMark 0 _ h0]
    simp [DTM.run, DTM.stepConfig, seekMark, DTM.halted, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]
  · have h0 : seekMark.halted
        { state := (0 : Fin 4), tape := { left := L, right := R } } = false := by
      simp [DTM.halted, seekMark]
    have h1 : seekMark.halted
        (seekMark.stepConfig { state := (0 : Fin 4), tape := { left := L, right := R } }) = false := by
      simp [DTM.stepConfig, seekMark, DTM.halted, Tape.read, Tape.write, Tape.move, Tape.moveRight]
    rw [DTM.run_succ_of_not_halted seekMark 1 _ h0]
    rw [DTM.run_succ_of_not_halted seekMark 0 _ h1]
    simp [DTM.run, DTM.stepConfig, seekMark, DTM.halted, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

/-- 找标记的运行前 `3|cs|+3` 步都不会停机。 -/
theorem seekMark_halted_false_before : ∀ (cs : List (Sym × Bool)),
    (∀ p ∈ cs, p.2 = false) →
    ∀ (s : Sym) (rest : List (Sym × Bool)) (L : List Sym) (m : Nat),
      m < 3 * cs.length + 3 →
      seekMark.halted
        (seekMark.run m
          { state := (0 : Fin 4),
            tape := { left := L, right := codeCells cs ++ cellCode (s, true) ++ codeCells rest } })
        = false
  | [], _, s, rest, L, m, hm => by
      have hle : m ≤ 2 := by simp only [List.length_nil] at hm; omega
      exact seekMark_halted_small L
        (cellCode (s, true) ++ codeCells rest) m hle
  | p :: ps, hmark, s, rest, L, m, hm => by
      obtain ⟨b0, b1, hs⟩ : ∃ b0 b1 : Sym, symCode p.1 = [b0, b1] := by
        cases p.1 with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hp : p.2 = false := hmark p (by simp)
      have hcell : cellCode p = [b0, b1, some false] := by
        simp [cellCode, hs, hp]
      have hright : codeCells (p :: ps) ++ cellCode (s, true) ++ codeCells rest
          = b0 :: b1 :: some false :: (codeCells ps ++ cellCode (s, true) ++ codeCells rest) := by
        simp only [codeCells, List.flatMap_cons, hcell, List.cons_append, List.nil_append]
      have hps : ∀ q ∈ ps, q.2 = false := fun q hq => hmark q (by simp [hq])
      by_cases hm3 : m < 3
      · have hle : m ≤ 2 := by omega
        rw [hright]
        exact seekMark_halted_small L
          (b0 :: b1 :: some false :: (codeCells ps ++ cellCode (s, true) ++ codeCells rest)) m hle
      · obtain ⟨m', rfl⟩ : ∃ m', m = 3 + m' := ⟨m - 3, by omega⟩
        have hm' : m' < 3 * ps.length + 3 := by
          simp only [List.length_cons] at hm
          omega
        rw [hright, DTM.run_add]
        rw [seekMark_steps_false L b0 b1
          (codeCells ps ++ cellCode (s, true) ++ codeCells rest)]
        exact seekMark_halted_false_before ps hps s rest (some false :: b1 :: b0 :: L) m' hm'

end DTM

end Pnp
