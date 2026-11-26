/-
  文件：Pnp/Machine/PadConflict.lean
  File: Pnp/Machine/PadConflict.lean

  主题：机器层逐分支定理的**右预留前提可满足性检查**。
  Topic: satisfiability check of the right-pad premise in the machine-level theorems.

  结论（重要）：`branchMachine_dummy_complete` / `_sound` / `_iff` 里
  `hpad : roundCostStay x Z B x.cur + branchBudget x.pre.length Z T B b + 1
        ≤ 3 * x.post.length + 1`（`x = Reg.initReg M.start w m m`）**强迫输入格数
  至少是 `T` 的二次方**：`(T+1)(1+2T) ≤ |(w.map some).drop 1|`。而实际用法是
  `T = |w|^k + k`（`|w| ≤ T`），于是该前提恒不成立 ⇒ 这三条机器层定理在目标参数区间内
  是**空真**的（不影响定理正确性，但 E 不能据此装配）。
  Finding: the premise forces the input to be quadratic in `T`; with `T = |w|^k + k`
  it is unsatisfiable, so those theorems are vacuous there.
  修法：左右垫解耦，改用 `Reg.initReg M.start w (T+1) m`（左垫固定 `T+1`，
  只让右垫 `m` 覆盖预算）。
  Fix: decouple the pads — keep the left pad at `T+1` and only grow the right pad.
-/

import Pnp.Machine.BranchMachine

namespace Pnp

namespace DTM

/-- 单轮成本的粗下界：`6·|pre| ≤ roundCostStay`（两处各 `3·|pre|` 的码长）。
    Crude lower bound on one round's cost. -/
theorem roundCostStay_ge_pre {q : Nat} (x : Reg q) (z k : Nat) (s' : Sym) :
    6 * x.pre.length ≤ roundCostStay x z k s' := by
  simp only [roundCostStay, List.length_cons, List.length_reverse, List.length_append,
    List.length_replicate, codeCells_length]
  omega

/-- 逐分支预算的粗下界：`6·(|pre|·T) ≤ branchBudget pre Z T B b`。
    Crude lower bound on the per-branch budget. -/
theorem branchBudget_ge (P Z T B b : Nat) :
    6 * (P * T) ≤ branchBudget P Z T B b := by
  have hc : 6 * P ≤ costCap P Z T (2 ^ b) := by
    unfold costCap
    omega
  have hmul : 6 * P * T ≤ costCap P Z T (2 ^ b) * T :=
    Nat.mul_le_mul_right T hc
  have hassoc : 6 * P * T = 6 * (P * T) := Nat.mul_assoc 6 P T
  rw [hassoc] at hmul
  calc 6 * (P * T) ≤ costCap P Z T (2 ^ b) * T := hmul
    _ = T * costCap P Z T (2 ^ b) := Nat.mul_comm _ _
    _ ≤ branchBudget P Z T B b := by
        unfold branchBudget
        omega

/-- 展开恒等式：`m·(1+2T) = m + 2·(m·T)`。 -/
theorem mul_one_add_two (m T : Nat) : m * (1 + 2 * T) = m + 2 * (m * T) := by
  rw [Nat.mul_add, Nat.mul_one]
  congr 1
  ac_rfl

/-- 小算术：`T < 1 + 2T`。 -/
theorem lt_one_add_two_mul (T : Nat) : T < 1 + 2 * T := by omega

/-- 输入末尾丢弃一格后长度不增。 -/
theorem drop_one_length_le (w : List Bool) :
    ((w.map some).drop 1).length ≤ w.length := by
  rw [List.length_drop, List.length_map]
  omega

/-- **右预留前提强迫输入很长**：在 `m ≥ T+1` 下，`hpad` 推出
    `(T+1)(1+2T) ≤ |(w.map some).drop 1|`。
    The right-pad premise forces the input to be quadratic in `T`. -/
theorem branchMachine_hpad_needs_long_input {q : Nat} (M : NTM q) (w : List Bool)
    (Z T B b m : Nat) (hT : 0 < T) (hm : T + 1 ≤ m)
    (hpad : roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w m m).post.length + 1) :
    (T + 1) * (1 + 2 * T) ≤ ((w.map some).drop 1).length := by
  have hpre : (Reg.initReg M.start w m m).pre.length = m :=
    Reg.initReg_pre_length M.start w m m
  have hpost : (Reg.initReg M.start w m m).post.length
      = ((w.map some).drop 1).length + m :=
    Reg.initReg_post_length M.start w m m
  rw [hpre, hpost] at hpad
  -- 下界：单轮成本 ≥ 6m、逐分支预算 ≥ 6·(m·T)
  have hrc : 6 * m ≤ roundCostStay (Reg.initReg M.start w m m) Z B
      (Reg.initReg M.start w m m).cur := by
    have h := roundCostStay_ge_pre (Reg.initReg M.start w m m) Z B
      (Reg.initReg M.start w m m).cur
    rw [hpre] at h
    exact h
  have hbb : 6 * (m * T) ≤ branchBudget m Z T B b := branchBudget_ge m Z T B b
  -- 线性合并：`3m + 6·(m·T) ≤ 3·|drop 1|`
  have hA : 3 * m + 6 * (m * T) ≤ 3 * ((w.map some).drop 1).length := by
    omega
  -- 除以 3：`m + 2·(m·T) ≤ |drop 1|`
  have hB : m + 2 * (m * T) ≤ ((w.map some).drop 1).length := by
    have h3 : 3 * (m + 2 * (m * T)) = 3 * m + 6 * (m * T) := by
      rw [Nat.mul_add]
      omega
    have h4 : 3 * (m + 2 * (m * T)) ≤ 3 * ((w.map some).drop 1).length := by
      rw [h3]; exact hA
    exact Nat.le_of_mul_le_mul_left h4 (by decide)
  -- 单调性放大到 `(T+1)(1+2T)`
  have hmono : (T + 1) + 2 * ((T + 1) * T) ≤ m + 2 * (m * T) := by
    have h2 : (T + 1) * (1 + 2 * T) ≤ m * (1 + 2 * T) :=
      Nat.mul_le_mul_right (1 + 2 * T) hm
    rw [mul_one_add_two (T + 1) T, mul_one_add_two m T] at h2
    exact h2
  have htarget : (T + 1) * (1 + 2 * T) = (T + 1) + 2 * ((T + 1) * T) :=
    mul_one_add_two (T + 1) T
  rw [htarget]
  exact Nat.le_trans hmono hB

/-- **空真性**：`|w| ≤ T`（如 `T = |w|^k + k`）时右预留前提恒不成立。
    Vacuousness: with `|w| ≤ T` the right-pad premise can never hold. -/
theorem branchMachine_hpad_false {q : Nat} (M : NTM q) (w : List Bool)
    (Z T B b m : Nat) (hT : 0 < T) (hm : T + 1 ≤ m) (hwl : w.length ≤ T) :
    ¬ (roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w m m).post.length + 1) := by
  intro hpad
  have hnl := branchMachine_hpad_needs_long_input M w Z T B b m hT hm hpad
  have hle : (T + 1) * (1 + 2 * T) ≤ T :=
    Nat.le_trans hnl (Nat.le_trans (drop_one_length_le w) hwl)
  have hlin : 1 + 2 * T ≤ (T + 1) * (1 + 2 * T) := by
    rw [Nat.succ_mul T (1 + 2 * T)]
    exact Nat.le_add_left _ _
  have hle' : 1 + 2 * T ≤ T := Nat.le_trans hlin hle
  exact absurd hle' (Nat.not_le.mpr (lt_one_add_two_mul T))

end DTM

end Pnp
