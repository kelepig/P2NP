/-
  文件：Pnp/Machine/WalkRT.lean
  File: Pnp/Machine/WalkRT.lean

  主题：**右走找标记的走位机 `walkRT`**——连续右移跳过 `some true`，读到 `some false`
        进状态 1（接受）、读到空白进状态 2（「块已尽」标记）。是 `walkLT` 的镜像。
  Topic: a right-walking machine skipping `some true` cells; `some false` ends in state 1,
  a blank in state 2. Mirror image of `walkLT`.

  用途（docs/07 补记 #201）：unary 加法先把头从源块最左格移到最右格，再向左逐格消费。
  Use: unary addition first moves the head to the rightmost source cell.
-/

import Pnp.Machine.WalkLT
import Pnp.Machine.ReadDigit

namespace Pnp

namespace DTM

/-- **右走找非 `some true`**：跳过 `some true`；`some false` ⇒ 状态 1（接受），
    空白 ⇒ 状态 2（块已尽）。其余状态原地吸收。
    Right-walker skipping `some true`; `some false` ends in state 1, a blank in state 2. -/
def walkRT : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | some false => (⟨1, by omega⟩, some false, Dir.stay)
       | some true => (⟨0, by omega⟩, some true, Dir.right)
       | none => (⟨2, by omega⟩, none, Dir.stay))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨1, by omega⟩
  reject := ⟨2, by omega⟩

/-- 非终止状态（既非 1 也非 2）一律不停机。 States other than 1/2 never halt. -/
theorem walkRT_halted_ne (st : Nat) (hst : st < 128) (h1 : st ≠ 1) (h2 : st ≠ 2)
    (t : Tape) : walkRT.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkRT.accept.val = 1 from rfl] at hv
    exact h1 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkRT.reject.val = 2 from rfl] at hv
    exact h2 hv

/-- `walkRT` 的单步运行套路。 The one-step idiom for `walkRT`. -/
theorem estepRT (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : walkRT.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 1)
    (hne2 : st ≠ 2) :
    walkRT.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (walkRT_halted_ne st hst hne hne2 _)]
  exact stepConfig_of_step walkRT ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **走到 `some false`**：右带 `m` 个 `some true` 之后是 `some false`，`m + 1` 步后
    头停在该 `some false` 上并接受。
    Walk to the `some false` behind `m` `some true` cells in `m + 1` steps. -/
theorem walkRT_run_false : ∀ (m : Nat) (P R : List Sym),
    walkRT.run (m + 1)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk R (List.replicate m (some true) ++ some false :: P)⟩
      = ⟨(⟨1, by omega⟩ : Fin 128),
          Tape.mk (List.replicate m (some true) ++ R) (some false :: P)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [estepRT 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 1 : Nat) = 1 + (m + 1) from by omega,
        DTM.run_add walkRT 1 (m + 1)]
      rw [estepRT 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkRT_run_false m P (some true :: R)]
      rw [replicate_append_cons m (some true) R]

/-- **走到空白（块已尽）**：右带 `m` 个 `some true` 之后是空白，`m + 1` 步后
    头停在空白上并进入状态 2。
    Walk to the blank behind `m` `some true` cells; ends in state 2. -/
theorem walkRT_run_none : ∀ (m : Nat) (P R : List Sym),
    walkRT.run (m + 1)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk R (List.replicate m (some true) ++ none :: P)⟩
      = ⟨(⟨2, by omega⟩ : Fin 128),
          Tape.mk (List.replicate m (some true) ++ R) (none :: P)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [estepRT 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 1 : Nat) = 1 + (m + 1) from by omega,
        DTM.run_add walkRT 1 (m + 1)]
      rw [estepRT 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [walkRT_run_none m P (some true :: R)]
      rw [replicate_append_cons m (some true) R]

end DTM

end Pnp
