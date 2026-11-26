/-
  文件：Pnp/Machine/ExpandNoHalt.lean
  File: Pnp/Machine/ExpandNoHalt.lean

  主题：展开机 `expand` 在整段运行结束**之前**不停机。
  Topic: the expander never halts before the end of its full run.

  用途：E 机把"展开 → 写副垫 → 左移定位 → 写头标记"用 `seqComp` 拼成一台机器时，
  `SeqComp.seqComp_run` 要求每一段在自己的步数内不停机。`expand_run` 的终点是接受态，
  无法直接由终点推出不停机；本文按与 `expand_run` 相同的归纳给出逐步版本。
  Purpose: `seqComp_run` needs per-segment non-halting. The endpoint of `expand_run` is the
  accept state, so this file mirrors its induction to get the step-by-step fact.

  关键观察：`expand` 只在状态 0 读到空白时进入接受态 99；每一轮循环
  （`expand_round` / `expand_round2`）的终点都回到状态 0（非终止），
  由 `halted_false_before` 即可覆盖整轮；单符号块（6 步）单独枚举到第 5 步。
  Key point: `expand` enters 99 only from state 0 on a blank; each round ends in state 0
  (non-terminal), so `halted_false_before` covers it, and the one-symbol case is enumerated.
-/

import Pnp.Machine.ExpandRun

namespace Pnp

namespace DTM

/-- **展开机整段运行内不停机**：非空白块 `l` 后跟 `2|l|+1` 个空白时，`expandCost l` 步内
    任何一步的状态都不是接受态（`halted` 恒为 `false`）。
    The expander does not halt during its `expandCost l` steps. -/
theorem expand_halted_false (l : List Sym) (hl : ∀ v ∈ l, v ≠ none) (M R : List Sym)
    (k : Nat) (hk : k < expandCost l) :
    expand.halted (expand.run k ⟨(⟨0, by omega⟩ : Fin 128),
      Tape.mk M (l ++ List.replicate (2 * l.length + 1) none ++ R)⟩) = false := by
  revert M R hl k hk
  induction l with
  | nil =>
      intro hl M R k hk
      have hk0 : k = 0 := by simpa [expandCost] using hk
      subst hk0
      exact expand_halted_ne 0 (by omega) (by decide) _
  | cons a t ih =>
      intro hl M R k hk
      cases t with
      | nil =>
          -- 单符号块：6 步内前 5 步都在状态 0 或非终止相位
          have ha : a ≠ none := hl a (by simp)
          have h5 : expand.run 5
              ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk M (a :: none :: none :: none :: R)⟩
              = ⟨(⟨0, by omega⟩ : Fin 128),
                  Tape.mk (some false :: codeSnd a :: codeFst a :: M) (none :: R)⟩ := by
            rw [show (5 : Nat) = 1 + (1 + (1 + (1 + 1))) from rfl]
            rw [DTM.run_add expand 1 (1 + (1 + (1 + 1)))]
            cases a with
            | none => exact absurd rfl ha
            | some b =>
                cases b with
                | false =>
                    rw [expand_entry_false]
                    exact expand_last_false none M R
                | true =>
                    rw [expand_entry_true]
                    exact expand_last_true none M R
          -- 把目标里的纸带写成 `h5` 的形态
          have h5' : expand.run 5 ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk M ([a] ++ List.replicate (2 * [a].length + 1) none ++ R)⟩
              = ⟨(⟨0, by omega⟩ : Fin 128),
                  Tape.mk (some false :: codeSnd a :: codeFst a :: M) (none :: R)⟩ := by
            have ht : ([a] ++ List.replicate (2 * [a].length + 1) none ++ R)
                = a :: none :: none :: none :: R := rfl
            rw [ht]
            exact h5
          have hne1 : (expand.run 5 ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk M ([a] ++ List.replicate (2 * [a].length + 1) none ++ R)⟩).state
              ≠ expand.accept := by
            rw [h5']
            intro h
            have hv := congrArg Fin.val h
            simp [expand] at hv
            exact absurd hv (by decide)
          have hne2 : (expand.run 5 ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk M ([a] ++ List.replicate (2 * [a].length + 1) none ++ R)⟩).state
              ≠ expand.reject := by
            rw [h5']
            intro h
            have hv := congrArg Fin.val h
            simp [expand] at hv
            exact absurd hv (by decide)
          rcases Nat.lt_or_ge k 5 with hk5 | hk5
          · have hnh := halted_false_before expand 5
              ⟨(⟨0, by omega⟩ : Fin 128),
                Tape.mk M ([a] ++ List.replicate (2 * [a].length + 1) none ++ R)⟩
              hne1 hne2
            exact hnh k hk5
          · have hk6 : k = 5 := by
              have := hk
              rw [show expandCost [a] = 6 from rfl] at this
              omega
            subst hk6
            rw [h5']
            exact expand_halted_ne 0 (by omega) (by decide) _
      | cons b rest =>
          have ha : a ≠ none := hl a (by simp)
          have hb : b ≠ none := hl b (by simp)
          have hrest : ∀ v ∈ b :: rest, v ≠ none := by
            intro v hv
            exact hl v (List.mem_cons_of_mem a hv)
          -- 首相位：`2|b::rest|+9` 步后回到状态 0（与 `expand_run` 同构）
          have hphase : expand.run (2 * (b :: rest).length + 9)
              ⟨(⟨0, by omega⟩ : Fin 128),
                Tape.mk M ((a :: b :: rest) ++ List.replicate (2 * (a :: b :: rest).length + 1)
                  none ++ R)⟩
              = ⟨(⟨0, by omega⟩ : Fin 128),
                Tape.mk (symCode3 a ++ M)
                  ((b :: rest) ++ List.replicate (2 * (b :: rest).length + 1) none ++ R)⟩ := by
            cases rest with
            | nil =>
                rw [show 2 * (b :: []).length + 9 = 11 from rfl]
                rw [show (a :: b :: []) ++ List.replicate (2 * (a :: b :: []).length + 1) none ++ R
                      = a :: b :: none :: none :: none :: none :: none :: R from rfl]
                rw [expand_round2 a b ha hb M R]
                rw [show (some false :: codeSnd a :: codeFst a :: M) = (symCode3 a ++ M)
                      from rfl]
                rw [show (b :: []) ++ List.replicate (2 * (b :: []).length + 1) none ++ R
                      = b :: none :: none :: none :: R from rfl]
            | cons c rest' =>
                obtain ⟨bs, bl, hbs⟩ := exists_append_singleton (c :: rest') (by simp)
                rw [hbs]
                have hrest' : ∀ v ∈ b :: (bs ++ [bl]), v ≠ none := by
                  intro v hv
                  exact hrest v (by rw [hbs]; exact hv)
                have hbs' : ∀ v ∈ bs, v ≠ none := by
                  intro v hv
                  exact hrest' v (List.mem_cons_of_mem b
                    (List.mem_append.mpr (Or.inl hv)))
                have hbl : bl ≠ none := by
                  exact hrest' bl (List.mem_cons_of_mem b
                    (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))))
                rw [show 2 * (b :: (bs ++ [bl])).length + 9 = 2 * bs.length + 13 from by
                  simp only [List.length_cons, List.length_append, List.length_nil]
                  omega]
                have htap : (a :: b :: (bs ++ [bl]))
                      ++ List.replicate (2 * (a :: b :: (bs ++ [bl])).length + 1) none ++ R
                    = (a :: b :: (bs ++ [bl])) ++ none :: none :: none
                        :: (List.replicate (2 * bs.length + 4) none ++ R) := by
                  have hlen : (a :: b :: (bs ++ [bl])).length = (bs ++ [bl]).length + 2 := by
                    simp only [List.length_cons]
                    try omega
                  rw [hlen]
                  simp only [List.length_append, List.length_singleton, List.append_assoc]
                  rfl
                rw [htap]
                rw [expand_round a b bl bs ha hb hbs' hbl M
                  (List.replicate (2 * bs.length + 4) none ++ R)]
                have htap2 : (b :: (bs ++ [bl]))
                      ++ none :: (List.replicate (2 * bs.length + 4) none ++ R)
                    = (b :: (bs ++ [bl]))
                        ++ List.replicate (2 * (b :: (bs ++ [bl])).length + 1) none ++ R := by
                  have hlen : (b :: (bs ++ [bl])).length = (bs ++ [bl]).length + 1 := by
                    simp only [List.length_cons]
                  rw [hlen]
                  simp only [List.length_append, List.length_singleton, List.append_assoc]
                  rfl
                rw [htap2]
                rw [show (some false :: codeSnd a :: codeFst a :: M) = (symCode3 a ++ M)
                      from rfl]
          have hne1 : (expand.run (2 * (b :: rest).length + 9)
              ⟨(⟨0, by omega⟩ : Fin 128),
                Tape.mk M ((a :: b :: rest)
                  ++ List.replicate (2 * (a :: b :: rest).length + 1) none ++ R)⟩).state
              ≠ expand.accept := by
            rw [hphase]
            intro h
            have hv := congrArg Fin.val h
            simp [expand] at hv
            exact absurd hv (by decide)
          have hne2 : (expand.run (2 * (b :: rest).length + 9)
              ⟨(⟨0, by omega⟩ : Fin 128),
                Tape.mk M ((a :: b :: rest)
                  ++ List.replicate (2 * (a :: b :: rest).length + 1) none ++ R)⟩).state
              ≠ expand.reject := by
            rw [hphase]
            intro h
            have hv := congrArg Fin.val h
            simp [expand] at hv
            exact absurd hv (by decide)
          rcases Nat.lt_or_ge k (2 * (b :: rest).length + 9) with hk1 | hk1
          · have hnh := halted_false_before expand (2 * (b :: rest).length + 9)
              ⟨(⟨0, by omega⟩ : Fin 128),
                Tape.mk M ((a :: b :: rest)
                  ++ List.replicate (2 * (a :: b :: rest).length + 1) none ++ R)⟩
              hne1 hne2
            exact hnh k hk1
          · obtain ⟨j, hjk⟩ : ∃ j, k = (2 * (b :: rest).length + 9) + j :=
              ⟨k - (2 * (b :: rest).length + 9), by omega⟩
            subst hjk
            rw [DTM.run_add expand (2 * (b :: rest).length + 9) j, hphase]
            exact ih hrest (symCode3 a ++ M) R j (by
              have hcost := hk
              rw [show expandCost (a :: b :: rest)
                    = (2 * (b :: rest).length + 9) + expandCost (b :: rest) from rfl] at hcost
              omega)

end DTM

end Pnp
