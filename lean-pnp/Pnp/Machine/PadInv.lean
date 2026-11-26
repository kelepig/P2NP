/-
  文件：Pnp/Machine/PadInv.lean
  主题：纸带两端空白预留的语义不变性——在 `Tape` 两侧追加任意多个空白格，不改变
        读写语义与运行结果（只改变纸带表示）。

  为什么需要它（docs/07-B5-模拟器设计.md「越界语义差异与修复方案」、auto-run-log #107）：
    - 区域语义 `Reg.step` 在区域边界（`pre = []` 或 `post = []`）处返回 `none`，
      而真机纸带 `Tape.moveLeft/moveRight` 在边界处自动补空白格、继续运行；
    - 外层枚举因此要在初始区域两侧预留空白（#108 的 `hpadpost`/`hpadpre`），
      这使区域的 `toConfig` 不再与 `M.init w` 逐字相等；
    - 本文件证明「两侧空白追加」是语义透明的：以 `SameInf` 关联两张纸带，
      任何一步都保持该关系，故 `runWith` 的成败与终态状态一致。

  Blank padding on either side is invisible to DTM semantics: `SameInf` relates
  tapes up to trailing blanks, and it is preserved by read/write/move, hence by
  `runWith`.
-/

import Pnp.Classes

namespace Pnp

namespace Tape

/-- 两张纸带在「无限空白延拓」下相同：各自只多出一串尾部空白格。
    纸带 `left` 的头部最靠近读写头，故空白追加在 `left`/`right` 的**末端**。
    Two tapes agree up to trailing blanks at both ends. -/
def SameInf (t1 t2 : Tape) : Prop :=
  ∃ kl kr, t1.left = t2.left ++ List.replicate kl none ∧
    t1.right = t2.right ++ List.replicate kr none

/-- 自身与自身语义相同。 -/
theorem sameInf_refl (t : Tape) : SameInf t t :=
  ⟨0, 0, by simp, by simp⟩

/-- 语义相同的纸带，读出同一符号。 -/
theorem sameInf_read {t1 t2 : Tape} (h : SameInf t1 t2) : t1.read = t2.read := by
  obtain ⟨kl, kr, hl, hr⟩ := h
  cases t1 with
  | mk l1 r1 =>
  cases t2 with
  | mk l2 r2 =>
    simp only at hl hr
    simp only [read, hr]
    cases r2 with
    | nil =>
        cases kr with
        | zero => rfl
        | succ kr' => rfl
    | cons r rs => rfl

/-- 写入只改当前格，`SameInf` 保持。 -/
theorem sameInf_write {t1 t2 : Tape} (h : SameInf t1 t2) (s : Sym) :
    SameInf (t1.write s) (t2.write s) := by
  obtain ⟨kl, kr, hl, hr⟩ := h
  cases t1 with
  | mk l1 r1 =>
  cases t2 with
  | mk l2 r2 =>
    simp only at hl hr
    cases r2 with
    | nil =>
        cases kr with
        | zero =>
            simp only [List.nil_append, List.replicate_zero, List.append_nil] at hr
            subst hr
            exact ⟨kl, 0, hl, by simp [write]⟩
        | succ kr' =>
            simp only [List.nil_append, List.replicate_succ] at hr
            subst hr
            exact ⟨kl, kr', hl, by simp [write, List.tail_cons]⟩
    | cons r rs =>
        cases kr with
        | zero =>
            simp only [List.replicate_zero, List.append_nil] at hr
            subst hr
            exact ⟨kl, 0, hl, by simp [write, List.tail_cons]⟩
        | succ kr' =>
            simp only [List.replicate_succ, List.cons_append] at hr
            subst hr
            exact ⟨kl, kr' + 1, hl, by simp [write, List.tail_cons, List.replicate_succ]⟩

/-- 左移一格只消耗左端一格，`SameInf` 保持。 -/
theorem sameInf_moveLeft {t1 t2 : Tape} (h : SameInf t1 t2) :
    SameInf t1.moveLeft t2.moveLeft := by
  obtain ⟨kl, kr, hl, hr⟩ := h
  cases t1 with
  | mk l1 r1 =>
  cases t2 with
  | mk l2 r2 =>
    simp only at hl hr
    cases l2 with
    | nil =>
        cases kl with
        | zero =>
            simp only [List.nil_append, List.replicate_zero, List.append_nil] at hl
            subst hl
            exact ⟨0, kr, by simp [moveLeft], by simp [moveLeft, hr]⟩
        | succ kl' =>
            simp only [List.nil_append, List.replicate_succ] at hl
            subst hl
            exact ⟨kl', kr, by simp [moveLeft], by simp [moveLeft, hr]⟩
    | cons x xs =>
        subst hl
        exact ⟨kl, kr, by simp [moveLeft], by simp [moveLeft, hr]⟩

/-- 右移一格只消耗右端一格，`SameInf` 保持。 -/
theorem sameInf_moveRight {t1 t2 : Tape} (h : SameInf t1 t2) :
    SameInf t1.moveRight t2.moveRight := by
  obtain ⟨kl, kr, hl, hr⟩ := h
  cases t1 with
  | mk l1 r1 =>
  cases t2 with
  | mk l2 r2 =>
    simp only at hl hr
    cases r2 with
    | nil =>
        cases kr with
        | zero =>
            simp only [List.nil_append, List.replicate_zero, List.append_nil] at hr
            subst hr
            exact ⟨kl, 0, by simp [moveRight, hl], by simp [moveRight]⟩
        | succ kr' =>
            simp only [List.nil_append, List.replicate_succ] at hr
            subst hr
            exact ⟨kl, kr', by simp [moveRight, hl], by simp [moveRight]⟩
    | cons r rs =>
        cases kr with
        | zero =>
            simp only [List.replicate_zero, List.append_nil] at hr
            subst hr
            exact ⟨kl, 0, by simp [moveRight, hl], by simp [moveRight]⟩
        | succ kr' =>
            simp only [List.replicate_succ, List.cons_append] at hr
            subst hr
            exact ⟨kl, kr' + 1, by simp [moveRight, hl], by simp [moveRight, List.replicate_succ]⟩

/-- 按方向移动，`SameInf` 保持。 -/
theorem sameInf_move {t1 t2 : Tape} (h : SameInf t1 t2) (d : Dir) :
    SameInf (t1.move d) (t2.move d) := by
  cases d with
  | stay => exact h
  | left => exact sameInf_moveLeft h
  | right => exact sameInf_moveRight h

/-- 写入并移动后仍语义相同（组合形态，供后继使用）。 -/
theorem sameInf_write_move {t1 t2 : Tape} (h : SameInf t1 t2) (s : Sym) (d : Dir) :
    SameInf ((t1.write s).move d) ((t2.write s).move d) :=
  sameInf_move (sameInf_write h s) d

/-- **对称版 `SameInf`**：两张纸带至多差两侧空白格，不指定哪一侧更长。
    逐字版 `SameInf` 对追加方向敏感（`t ++ 空白` 与 `t` 只在「前者作主导」时成立），
    因此外层枚举的双向搬运需要这一对称版本。
    Symmetric variant: the padding may be on either side. -/
def SameInfS (t1 t2 : Tape) : Prop := SameInf t1 t2 ∨ SameInf t2 t1

/-- 对称版读符号一致。 -/
theorem sameInfS_read {t1 t2 : Tape} (h : SameInfS t1 t2) : t1.read = t2.read := by
  rcases h with h | h
  · exact sameInf_read h
  · exact (sameInf_read h).symm

/-- 对称版写入并移动后仍相同。 -/
theorem sameInfS_write_move {t1 t2 : Tape} (h : SameInfS t1 t2) (s : Sym) (d : Dir) :
    SameInfS ((t1.write s).move d) ((t2.write s).move d) := by
  rcases h with h | h
  · exact Or.inl (sameInf_write_move h s d)
  · exact Or.inr (sameInf_write_move h s d)

end Tape

/-- **格局级语义相同**：状态相同、纸带至多差两侧空白格（对称）。外层枚举器构造的
    初始区域带有两侧预留空白，因此与 `M.init w` 只能按此关系比较（逐字相等不可满足）。
    Configuration-level equivalence: equal states and tapes differing only by padding.
    Padded initial regions cannot be literally equal to `M.init w`, only equivalent. -/
def CfgEquiv {q : Nat} (c1 c2 : Config q) : Prop :=
  c1.state = c2.state ∧ Tape.SameInfS c1.tape c2.tape

/-- `CfgEquiv` 是对称关系。 -/
theorem CfgEquiv.symm {q : Nat} {c1 c2 : Config q} (h : CfgEquiv c1 c2) : CfgEquiv c2 c1 :=
  ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩

namespace NTM

/-- 单步：语义相同的格局走同一候选动作仍语义相同。 -/
theorem stepWith_sameInf (M : NTM q) (c1 c2 : Config q) (i : Nat)
    (hs : c1.state = c2.state) (ht : Tape.SameInf c1.tape c2.tape) :
    ∀ c1', M.stepWith c1 i = some c1' →
      ∃ c2', M.stepWith c2 i = some c2' ∧ c1'.state = c2'.state ∧
        Tape.SameInf c1'.tape c2'.tape := by
  intro c1' h
  have hpick : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, Tape.sameInf_read ht]
  simp only [stepWith] at h ⊢
  rw [hpick] at h
  cases hp : pick (M.step c2.state c2.tape.read) i with
  | none =>
      rw [hp] at h
      cases h
  | some v =>
      obtain ⟨m', s', d⟩ := v
      rw [hp] at h
      simp only [hp]
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, rfl, Tape.sameInf_write_move ht s' d⟩

/-- 整段运行：从语义相同的格局出发，同一选择序列成功与否一致，终态状态相同。 -/
theorem runWith_sameInf (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) (c1 c2 : Config q),
      c1.state = c2.state → Tape.SameInf c1.tape c2.tape →
      ∀ c1', M.runWith n cs c1 = some c1' →
        ∃ c2', M.runWith n cs c2 = some c2' ∧
          c1'.state = c2'.state ∧ Tape.SameInf c1'.tape c2'.tape := by
  intro n
  induction n with
  | zero =>
      intro cs c1 c2 hs ht c1' h
      simp only [runWith, Option.some.injEq] at h
      subst h
      exact ⟨c2, rfl, hs, ht⟩
  | succ n ih =>
      intro cs c1 c2 hs ht c1' h
      have hh : M.halted c1 = M.halted c2 := by simp only [halted, hs]
      rw [runWith_succ] at h ⊢
      rw [hh] at h
      cases hc : M.halted c2 with
      | true =>
          simp only [hc, Option.some.injEq] at h ⊢
          subst h
          exact ⟨c2, rfl, hs, ht⟩
      | false =>
          cases cs with
          | nil =>
              simp only [hc] at h
              cases h
          | cons i rest =>
              simp only [hc] at h ⊢
              cases hp : M.stepWith c1 i with
              | none =>
                  rw [hp] at h
                  cases h
              | some c1m =>
                  rw [hp] at h
                  have hrun : M.runWith n rest c1m = some c1' := h
                  obtain ⟨c2m, hp2, hs2, ht2⟩ :=
                    stepWith_sameInf M c1 c2 i hs ht c1m hp
                  obtain ⟨c2', hrun2, hs3, ht3⟩ := ih rest c1m c2m hs2 ht2 c1' hrun
                  refine ⟨c2', ?_, hs3, ht3⟩
                  rw [hp2]
                  exact hrun2

/-- 单步（对称版）：语义相同的格局走同一候选动作仍语义相同。 -/
theorem stepWith_sameInfS (M : NTM q) (c1 c2 : Config q) (i : Nat)
    (hs : c1.state = c2.state) (ht : Tape.SameInfS c1.tape c2.tape) :
    ∀ c1', M.stepWith c1 i = some c1' →
      ∃ c2', M.stepWith c2 i = some c2' ∧ c1'.state = c2'.state ∧
        Tape.SameInfS c1'.tape c2'.tape := by
  intro c1' h
  have hpick : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, Tape.sameInfS_read ht]
  simp only [stepWith] at h ⊢
  rw [hpick] at h
  cases hp : pick (M.step c2.state c2.tape.read) i with
  | none =>
      rw [hp] at h
      cases h
  | some v =>
      obtain ⟨m', s', d⟩ := v
      rw [hp] at h
      simp only [hp]
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, rfl, Tape.sameInfS_write_move ht s' d⟩

/-- 整段运行（对称版）：同一选择序列在语义相同的格局上要么都成功，要么都失败，
    成功后终态状态一致。
    Symmetric run transport: success and the final state agree. -/
theorem runWith_sameInfS (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) (c1 c2 : Config q),
      c1.state = c2.state → Tape.SameInfS c1.tape c2.tape →
      ∀ c1', M.runWith n cs c1 = some c1' →
        ∃ c2', M.runWith n cs c2 = some c2' ∧ c1'.state = c2'.state := by
  intro n
  induction n with
  | zero =>
      intro cs c1 c2 hs ht c1' h
      simp only [runWith, Option.some.injEq] at h
      subst h
      exact ⟨c2, rfl, hs⟩
  | succ n ih =>
      intro cs c1 c2 hs ht c1' h
      have hh : M.halted c1 = M.halted c2 := by simp only [halted, hs]
      rw [runWith_succ] at h ⊢
      rw [hh] at h
      cases hc : M.halted c2 with
      | true =>
          simp only [hc, Option.some.injEq] at h ⊢
          subst h
          exact ⟨c2, rfl, hs⟩
      | false =>
          cases cs with
          | nil =>
              simp only [hc] at h
              cases h
          | cons i rest =>
              simp only [hc] at h ⊢
              cases hp : M.stepWith c1 i with
              | none =>
                  rw [hp] at h
                  cases h
              | some c1m =>
                  rw [hp] at h
                  obtain ⟨c2m, hp2, hs2, ht2⟩ :=
                    stepWith_sameInfS M c1 c2 i hs ht c1m hp
                  rw [hp2]
                  exact ih rest c1m c2m hs2 ht2 c1' h

/-- **格局语义相同的运行搬运**：从 `c1` 出发按同一选择序列跑通，则从语义相同的
    `c2` 出发也能跑通，且终态状态一致（终态纸带至多差空白）。
    Run transport across `CfgEquiv`: success and the final state agree. -/
theorem runWith_cfgEquiv (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) {c1 c2 : Config q}, CfgEquiv c1 c2 →
      ∀ c1', M.runWith n cs c1 = some c1' →
        ∃ c2', M.runWith n cs c2 = some c2' ∧ c1'.state = c2'.state :=
  fun n cs _ _ h => runWith_sameInfS M n cs _ _ h.1 h.2

/-- **空白预留不改变接受语义（对称版）**：只允许两侧多出空白格的初始格局，与
    `M.init w` 在 `T` 步内的接受行为一致；空白可以在任一侧（`SameInfS`）。
    Padding on either side does not change acceptance within `T`. -/
theorem acceptsWithin_of_sameInfS (M : NTM q) (w : List Bool) (T : Nat)
    (c0 : Config q) (hs : c0.state = M.start)
    (ht : Tape.SameInfS c0.tape (M.init w).tape)
    (h : ∃ cs : List Nat, cs.length ≤ T ∧
      ∃ c : Config q, M.runWith T cs c0 = some c ∧ c.state = M.accept) :
    M.AcceptsWithin w T := by
  obtain ⟨cs, hlen, c, hrun, hacc⟩ := h
  obtain ⟨c2, hrun2, hst⟩ := runWith_sameInfS M T cs c0 (M.init w) hs ht c hrun
  exact ⟨cs, hlen, c2, hrun2, by rw [← hst]; exact hacc⟩

/-- **空白预留不改变接受语义**：只允许两侧多出空白格的初始格局，与 `M.init w`
    在 `T` 步内的接受行为一致（接受方向的单向桥接，B5 只需要这一向）。
    Trailing-blank padding does not change acceptance within `T`. -/
theorem acceptsWithin_of_sameInf (M : NTM q) (w : List Bool) (T : Nat)
    (c0 : Config q) (hs : c0.state = M.start)
    (ht : Tape.SameInf c0.tape (M.init w).tape)
    (h : ∃ cs : List Nat, cs.length ≤ T ∧
      ∃ c : Config q, M.runWith T cs c0 = some c ∧ c.state = M.accept) :
    M.AcceptsWithin w T := by
  obtain ⟨cs, hlen, c, hrun, hacc⟩ := h
  obtain ⟨c2, hrun2, hst, -⟩ :=
    runWith_sameInf M T cs c0 (M.init w) hs ht c hrun
  exact ⟨cs, hlen, c2, hrun2, by rw [← hst]; exact hacc⟩

end NTM

end Pnp
