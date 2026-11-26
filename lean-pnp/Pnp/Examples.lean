/-
  文件：Pnp/Examples.lean
  主题：具体判定器实例——证明 P 类非空、定义没有退化。

  这里给出三个能一行转移就停机的机器：
    - `acceptAll`：接受所有输入（语言恒真）；
    - `rejectAll`：拒绝所有输入（语言恒假）；
    - `emptyOnly`：只接受空串。

  三个机器的时间上限都取 `n ^ 0 + 0 = 1`（常数 1 步），
  因而都落在 P 中。它们的作用是回归测试：如果哪天 `InP`、`DTM.run`
  或纸带语义被改坏，这些证明会先失败。
-/

import Pnp.Classes

namespace Pnp

/-- 接受一切输入的机器：第一步直接进入接受状态。 -/
def acceptAll : DTM 3 where
  step := fun _ a => (1, a, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-- 拒绝一切输入的机器：第一步直接进入拒绝状态。 -/
def rejectAll : DTM 3 where
  step := fun _ a => (2, a, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-- 只接受空串的机器：看初始格是否空白，是则接受，否则拒绝。 -/
def emptyOnly : DTM 3 where
  step := fun _ a =>
    match a with
    | none => (1, none, Dir.stay)
    | some b => (2, some b, Dir.stay)
  start := 0
  accept := 1
  reject := 2

/-! ## 初始格局不停机 -/

/-- 三个机器的初始状态都是 0，不等于接受/拒绝状态 1、2。
    分别先算出两个状态比较的布尔值（无自由变量，可直接 decide），再化简。 -/
theorem acceptAll_init_halted (w : List Bool) :
    acceptAll.halted (acceptAll.init w) = false := by
  have h1 : (acceptAll.start == acceptAll.accept) = false := by decide
  have h2 : (acceptAll.start == acceptAll.reject) = false := by decide
  simp [DTM.halted, DTM.init, h1, h2]

theorem rejectAll_init_halted (w : List Bool) :
    rejectAll.halted (rejectAll.init w) = false := by
  have h1 : (rejectAll.start == rejectAll.accept) = false := by decide
  have h2 : (rejectAll.start == rejectAll.reject) = false := by decide
  simp [DTM.halted, DTM.init, h1, h2]

theorem emptyOnly_init_halted (w : List Bool) :
    emptyOnly.halted (emptyOnly.init w) = false := by
  have h1 : (emptyOnly.start == emptyOnly.accept) = false := by decide
  have h2 : (emptyOnly.start == emptyOnly.reject) = false := by decide
  simp [DTM.halted, DTM.init, h1, h2]

/-! ## 一步之后的格局 -/

/-- 接受机走一步即进入接受状态。 -/
theorem acceptAll_run_one (w : List Bool) :
    (acceptAll.run 1 (acceptAll.init w)).state = acceptAll.accept := by
  have hstep : acceptAll.run 1 (acceptAll.init w)
      = acceptAll.stepConfig (acceptAll.init w) := by
    simp [DTM.run, acceptAll_init_halted]
  rw [hstep]
  simp [DTM.stepConfig, acceptAll]

/-- 拒绝机走一步即进入拒绝状态。 -/
theorem rejectAll_run_one (w : List Bool) :
    (rejectAll.run 1 (rejectAll.init w)).state = rejectAll.reject := by
  have hstep : rejectAll.run 1 (rejectAll.init w)
      = rejectAll.stepConfig (rejectAll.init w) := by
    simp [DTM.run, rejectAll_init_halted]
  rw [hstep]
  simp [DTM.stepConfig, rejectAll]

/-- 空串输入：初始格为空白，一步后接受。 -/
theorem emptyOnly_run_nil :
    (emptyOnly.run 1 (emptyOnly.init [])).state = emptyOnly.accept := by
  have hstep : emptyOnly.run 1 (emptyOnly.init [])
      = emptyOnly.stepConfig (emptyOnly.init []) := by
    simp [DTM.run, emptyOnly_init_halted]
  rw [hstep]
  simp [DTM.stepConfig, DTM.init, Tape.ofInput, Tape.read, emptyOnly]

/-- 非空输入：初始格为某个符号，一步后拒绝。 -/
theorem emptyOnly_run_cons (b : Bool) (bs : List Bool) :
    (emptyOnly.run 1 (emptyOnly.init (b :: bs))).state = emptyOnly.reject := by
  have hstep : emptyOnly.run 1 (emptyOnly.init (b :: bs))
      = emptyOnly.stepConfig (emptyOnly.init (b :: bs)) := by
    simp [DTM.run, emptyOnly_init_halted]
  rw [hstep]
  simp [DTM.stepConfig, DTM.init, Tape.ofInput, Tape.read, emptyOnly]

/-! ## 三个语言都在 P 中 -/

/-- 恒真语言属于 P。 -/
theorem acceptAll_decides :
    acceptAll.DecidesIn (fun n => n ^ 0 + 0) (fun _ => True) := by
  intro w
  have hT : w.length ^ 0 + 0 = 1 := by simp
  have hstate := acceptAll_run_one w
  have hH : acceptAll.HaltsWithin w 1 := Or.inl hstate
  have hA : acceptAll.AcceptsWithin w 1 ↔ True :=
    ⟨fun _ => trivial, fun _ => hstate⟩
  simpa [hT] using And.intro hH hA

/-- 恒假语言属于 P。 -/
theorem rejectAll_decides :
    rejectAll.DecidesIn (fun n => n ^ 0 + 0) (fun _ => False) := by
  intro w
  have hT : w.length ^ 0 + 0 = 1 := by simp
  have hstate := rejectAll_run_one w
  have hne : rejectAll.reject ≠ rejectAll.accept := by decide
  have hH : rejectAll.HaltsWithin w 1 := Or.inr hstate
  have hA : rejectAll.AcceptsWithin w 1 ↔ False := by
    constructor
    · -- 拒绝状态与接受状态不同，不可能同时是接受
      intro hacc
      exact hne (hstate.symm.trans hacc)
    · intro hf
      exact absurd hf (by trivial)
  simpa [hT] using And.intro hH hA

/-- 「只含空串」的语言属于 P。 -/
theorem emptyOnly_decides :
    emptyOnly.DecidesIn (fun n => n ^ 0 + 0) (fun w => w = []) := by
  intro w
  have hT : w.length ^ 0 + 0 = 1 := by simp
  rcases w with _ | ⟨b, bs⟩
  · -- 空串：一步接受
    have hstate := emptyOnly_run_nil
    have hH : emptyOnly.HaltsWithin [] 1 := Or.inl hstate
    have hA : emptyOnly.AcceptsWithin [] 1 ↔ ([] = []) :=
      ⟨fun _ => (rfl : ([] : List Bool) = []), fun _ => hstate⟩
    simpa [hT] using And.intro hH hA
  · -- 非空：一步拒绝
    have hstate := emptyOnly_run_cons b bs
    have hne : emptyOnly.reject ≠ emptyOnly.accept := by decide
    have hH : emptyOnly.HaltsWithin (b :: bs) 1 := Or.inr hstate
    have hA : emptyOnly.AcceptsWithin (b :: bs) 1 ↔ ((b :: bs) = []) := by
      constructor
      · intro hacc
        -- 非空串不可能等于空串
        exact False.elim (hne (hstate.symm.trans hacc))
      · intro hnil
        cases hnil
    simpa [hT] using And.intro hH hA

theorem inP_true : InP (fun _ : List Bool => True) :=
  ⟨0, 3, acceptAll, by decide, acceptAll_decides⟩

theorem inP_false : InP (fun _ : List Bool => False) :=
  ⟨0, 3, rejectAll, by decide, rejectAll_decides⟩

theorem inP_empty : InP (fun w : List Bool => w = []) :=
  ⟨0, 3, emptyOnly, by decide, emptyOnly_decides⟩

end Pnp
