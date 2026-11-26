/-
  文件：Pnp/Machine/WalkLT.lean
  File: Pnp/Machine/WalkLT.lean

  主题：**左走找标记的走位机 `walkLT`**——连续左移跳过 `some false`，读到 `some true`
        进状态 1（接受）、读到空白进状态 2（「源已耗尽」标记）。
  Topic: a left-walking machine that skips `some false` cells and halts either on
  `some true` (state 1, accept) or on a blank (state 2, exhausted).

  用途（见 docs/07 补记 #199 续）：unary 加法「两标记消费」的每一轮都要
  「向左走回下一个未读源格」，`walkL`/`walkR` 只支持「遇空白停」，本机补上这一缺件。
  Use: the per-round "walk back to the next unread source cell" of unary addition.
-/

import Pnp.Machine.ExpandRun

namespace Pnp

namespace DTM

/-- **左走找非 `some false`**：跳过 `some false`；`some true` ⇒ 状态 1（接受），
    空白 ⇒ 状态 2（耗尽标记）。其余状态原地吸收、不停机。
    Left-walker skipping `some false`; `some true` ends in state 1, a blank in state 2. -/
def walkLT : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | some true => (⟨1, by omega⟩, some true, Dir.stay)
       | some false => (⟨0, by omega⟩, some false, Dir.left)
       | none => (⟨2, by omega⟩, none, Dir.stay))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨1, by omega⟩
  reject := ⟨2, by omega⟩

/-- 非终止状态（既非 1 也非 2）一律不停机。 States other than 1/2 never halt. -/
theorem walkLT_halted_ne (st : Nat) (hst : st < 128) (h1 : st ≠ 1) (h2 : st ≠ 2)
    (t : Tape) : walkLT.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkLT.accept.val = 1 from rfl] at hv
    exact h1 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkLT.reject.val = 2 from rfl] at hv
    exact h2 hv

/-- `walkLT` 的单步运行套路。 The one-step idiom for `walkLT`. -/
theorem estepLT (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : walkLT.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 1)
    (hne2 : st ≠ 2) :
    walkLT.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (walkLT_halted_ne st hst hne hne2 _)]
  exact stepConfig_of_step walkLT ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 末尾补一个同符号：`replicate n a ++ a :: R = replicate (n+1) a ++ R`。
    Appending one `a` extends the replicate block by one. -/
theorem replicate_succ_append (n : Nat) (a : Sym) (R : List Sym) :
    List.replicate n a ++ a :: R = List.replicate (n + 1) a ++ R := by
  rw [show a :: R = ([a] : List Sym) ++ R from rfl, ← List.append_assoc,
    show ([a] : List Sym) = List.replicate 1 a from rfl, List.replicate_append_replicate]

/-- **走到 `some true`**：左带 `m` 个 `some false` 之后是 `some true`，`m + 2` 步后
    头停在该 `some true` 上并接受。
    Walk to the `some true` behind `m` `some false` cells in `m + 2` steps. -/
theorem walkLT_run_true : ∀ (m : Nat) (P R : List Sym),
    walkLT.run (m + 2)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk (List.replicate m (some false) ++ some true :: P) (some false :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 128),
          Tape.mk P (some true :: List.replicate (m + 1) (some false) ++ R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add walkLT 1 1]
      rw [estepLT 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [estepLT 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      simp
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add walkLT 1 (m + 2)]
      rw [estepLT 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkLT_run_true m P (some false :: R)]
      simp only [List.cons_append]
      rw [replicate_succ_append (m + 1) (some false) R]

/-- **走到空白（源耗尽）**：左带 `m` 个 `some false` 之后是空白，`m + 2` 步后
    头停在空白上并进入状态 2。
    Walk to the blank behind `m` `some false` cells; ends in state 2. -/
theorem walkLT_run_none : ∀ (m : Nat) (P R : List Sym),
    walkLT.run (m + 2)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk (List.replicate m (some false) ++ none :: P) (some false :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 128),
          Tape.mk P (none :: List.replicate (m + 1) (some false) ++ R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add walkLT 1 1]
      rw [estepLT 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [estepLT 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      simp
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add walkLT 1 (m + 2)]
      rw [estepLT 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkLT_run_none m P (some false :: R)]
      simp only [List.cons_append]
      rw [replicate_succ_append (m + 1) (some false) R]

end DTM

end Pnp
