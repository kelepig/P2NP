/-
  文件：Pnp/Machine/Embed.lean
  主题：把「小机器的一段运行」搬进「大机器」的通用引理。

  背景：本项目的机器组件各自是独立的小状态机。最终模拟器要把
  多个阶段合并成一臺状态数更大的机器。合并时只要：
    - 大机器在嵌入后的非终止状态上照抄小机器的转移；
    - 大机器在这些状态上也不终止，
  小机器的整段运行就能原样搬进大机器。

  本文件的核心是 `run_embed`：
  若 A 的整段运行 `n` 步内不终止，则 B 从状态嵌入 `e` 出发，
  `n` 步后的状态与纸带正好是 A 的运行结果经 `e` 映射。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 状态嵌入下的运行搬运：
    - `hstep`：B 在所有嵌入后的非终止状态上照抄 A 的转移；
    - `hhalt`：B 在这些状态上不终止；
    - 前提：A 在前 `n` 步内都不终止。
    结论：B 的运行等于 A 的运行（状态经 `e` 映射，纸带完全相同）。 -/
theorem run_embed {q q' : Nat} (A : DTM q) (B : DTM q') (e : Fin q → Fin q')
    (hstep : ∀ (s : Fin q) (a : Sym), s ≠ A.accept → s ≠ A.reject →
      B.step (e s) a = (e (A.step s a).1, (A.step s a).2))
    (hhalt : ∀ s : Fin q, s ≠ A.accept → s ≠ A.reject →
      B.accept ≠ e s ∧ B.reject ≠ e s) :
    ∀ (n : Nat) (c : Config q), (∀ m, m < n → A.halted (A.run m c) = false) →
      B.run n { state := e c.state, tape := c.tape } =
        { state := e (A.run n c).state, tape := (A.run n c).tape } := by
  intro n
  induction n with
  | zero =>
      intro c _
      rfl
  | succ n ih =>
      intro c hA
      -- 当前格局在 A 中未终止
      have hnf : A.halted c = false := hA 0 (Nat.zero_lt_succ n)
      have hstate : c.state ≠ A.accept ∧ c.state ≠ A.reject := by
        simpa [DTM.halted] using hnf
      obtain ⟨hna, hnr⟩ := hstate
      -- B 在当前格局也不终止
      have hBh : B.halted { state := e c.state, tape := c.tape } = false := by
        obtain ⟨ha, hr⟩ := hhalt c.state hna hnr
        have ha' : e c.state ≠ B.accept := fun h => ha h.symm
        have hr' : e c.state ≠ B.reject := fun h => hr h.symm
        simpa [DTM.halted] using And.intro ha' hr'
      -- 一步转移在 B 中与 A 的嵌入一致
      have hstepC : B.stepConfig { state := e c.state, tape := c.tape } =
          { state := e (A.stepConfig c).state, tape := (A.stepConfig c).tape } := by
        simp only [DTM.stepConfig, hstep c.state c.tape.read hna hnr]
      -- A 的运行剩余部分仍不终止
      have hA' : ∀ m, m < n → A.halted (A.run m (A.stepConfig c)) = false := by
        intro m hm
        rw [← DTM.run_succ_of_not_halted A m c hnf]
        exact hA (m + 1) (Nat.succ_lt_succ hm)
      rw [DTM.run_succ_of_not_halted A n c hnf]
      rw [DTM.run_succ_of_not_halted B n
        { state := e c.state, tape := c.tape } hBh]
      rw [hstepC]
      exact ih (A.stepConfig c) hA'

/-- `run_embed` 的加强版：除 A 的接受/拒绝外，另有中间状态 `bad` 也不要求照抄
    （例如「溢出标志」状态在合并机里被改接到别的相位）。
    代价是多一条前提：A 的运行在前 `n` 步内不经过 `bad`。 -/
theorem run_embed3 {q q' : Nat} (A : DTM q) (B : DTM q') (e : Fin q → Fin q')
    (bad : Fin q)
    (hstep : ∀ (s : Fin q) (a : Sym), s ≠ A.accept → s ≠ A.reject → s ≠ bad →
      B.step (e s) a = (e (A.step s a).1, (A.step s a).2))
    (hhalt : ∀ s : Fin q, s ≠ A.accept → s ≠ A.reject → s ≠ bad →
      B.accept ≠ e s ∧ B.reject ≠ e s) :
    ∀ (n : Nat) (c : Config q), (∀ m, m < n → A.halted (A.run m c) = false) →
      (∀ m, m < n → (A.run m c).state ≠ bad) →
      B.run n { state := e c.state, tape := c.tape } =
        { state := e (A.run n c).state, tape := (A.run n c).tape } := by
  intro n
  induction n with
  | zero =>
      intro c _ _
      rfl
  | succ n ih =>
      intro c hA hbad
      have hnf : A.halted c = false := hA 0 (Nat.zero_lt_succ n)
      have hstate : c.state ≠ A.accept ∧ c.state ≠ A.reject := by
        simpa [DTM.halted] using hnf
      obtain ⟨hna, hnr⟩ := hstate
      have hnb : c.state ≠ bad := hbad 0 (Nat.zero_lt_succ n)
      have hBh : B.halted { state := e c.state, tape := c.tape } = false := by
        obtain ⟨ha, hr⟩ := hhalt c.state hna hnr hnb
        have ha' : e c.state ≠ B.accept := fun h => ha h.symm
        have hr' : e c.state ≠ B.reject := fun h => hr h.symm
        simpa [DTM.halted] using And.intro ha' hr'
      have hstepC : B.stepConfig { state := e c.state, tape := c.tape } =
          { state := e (A.stepConfig c).state, tape := (A.stepConfig c).tape } := by
        simp only [DTM.stepConfig, hstep c.state c.tape.read hna hnr hnb]
      have hA' : ∀ m, m < n → A.halted (A.run m (A.stepConfig c)) = false := by
        intro m hm
        rw [← DTM.run_succ_of_not_halted A m c hnf]
        exact hA (m + 1) (Nat.succ_lt_succ hm)
      have hbad' : ∀ m, m < n → (A.run m (A.stepConfig c)).state ≠ bad := by
        intro m hm
        rw [← DTM.run_succ_of_not_halted A m c hnf]
        exact hbad (m + 1) (Nat.succ_lt_succ hm)
      rw [DTM.run_succ_of_not_halted A n c hnf]
      rw [DTM.run_succ_of_not_halted B n
        { state := e c.state, tape := c.tape } hBh]
      rw [hstepC]
      exact ih (A.stepConfig c) hA' hbad'

/-- 带「安全状态」谓词的运行搬运：只有落在 `ok` 里的状态才要求照抄。
    与 `run_embed3` 的区别是 `ok` 可以是任意谓词（例如「阶段不是 13 或 14」），
    而 `run_embed3` 只排除单个 `bad` 状态。 -/
theorem run_lift {q q' : Nat} (A : DTM q) (B : DTM q') (e : Fin q → Fin q')
    (ok : Fin q → Prop)
    (hstep : ∀ (s : Fin q) (a : Sym), ok s →
      B.step (e s) a = (e (A.step s a).1, (A.step s a).2))
    (hhalt : ∀ s : Fin q, ok s → B.accept ≠ e s ∧ B.reject ≠ e s) :
    ∀ (n : Nat) (c : Config q), (∀ m, m < n → A.halted (A.run m c) = false) →
      (∀ m, m < n → ok (A.run m c).state) →
      B.run n { state := e c.state, tape := c.tape } =
        { state := e (A.run n c).state, tape := (A.run n c).tape } := by
  intro n
  induction n with
  | zero =>
      intro c _ _
      rfl
  | succ n ih =>
      intro c hA hok
      have hnf : A.halted c = false := hA 0 (Nat.zero_lt_succ n)
      have hstate : c.state ≠ A.accept ∧ c.state ≠ A.reject := by
        simpa [DTM.halted] using hnf
      obtain ⟨hna, hnr⟩ := hstate
      have hcok : ok c.state := hok 0 (Nat.zero_lt_succ n)
      have hBh : B.halted { state := e c.state, tape := c.tape } = false := by
        obtain ⟨ha, hr⟩ := hhalt c.state hcok
        have ha' : e c.state ≠ B.accept := fun h => ha h.symm
        have hr' : e c.state ≠ B.reject := fun h => hr h.symm
        simpa [DTM.halted] using And.intro ha' hr'
      have hstepC : B.stepConfig { state := e c.state, tape := c.tape } =
          { state := e (A.stepConfig c).state, tape := (A.stepConfig c).tape } := by
        simp only [DTM.stepConfig, hstep c.state c.tape.read hcok]
      have hA' : ∀ m, m < n → A.halted (A.run m (A.stepConfig c)) = false := by
        intro m hm
        rw [← DTM.run_succ_of_not_halted A m c hnf]
        exact hA (m + 1) (Nat.succ_lt_succ hm)
      have hok' : ∀ m, m < n → ok (A.run m (A.stepConfig c)).state := by
        intro m hm
        rw [← DTM.run_succ_of_not_halted A m c hnf]
        exact hok (m + 1) (Nat.succ_lt_succ hm)
      rw [DTM.run_succ_of_not_halted A n c hnf]
      rw [DTM.run_succ_of_not_halted B n { state := e c.state, tape := c.tape } hBh]
      rw [hstepC]
      exact ih (A.stepConfig c) hA' hok'

end DTM

end Pnp
