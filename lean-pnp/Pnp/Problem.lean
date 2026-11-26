/-
  文件：Pnp/Problem.lean
  主题：把「P 与 NP 是否相等」这个**问题本身**写成 Lean 命题。

  重要边界（务必遵守）：
    - 本文件只做「陈述」与「等价改写」，**不证明** P = NP 或 P ≠ NP。
    - 这两个命题至今未解决；任何 Lean 文件声称证明了它，必然依赖
      `sorry`、自建公理或退化定义，会被 `#print axioms` 直接识破。
    - 这里给出的价值是：外部任何声称的证明，都可以拿来与本文件的
      `PEqualsNP` 对照——先看它证的到底是不是这个命题。

  实现说明：
    - 核心库没有 `Set`，因此「语言类」用谓词表示，不引入任何依赖；
    - P = NP 写成「对所有语言，属于 P 当且仅当属于 NP」。
-/

import Pnp.Classes

namespace Pnp

/-- P 类（谓词版）：一个语言属于 P。 -/
def PClass (L : List Bool → Prop) : Prop := InP L

/-- NP 类（谓词版）：一个语言属于 NP。 -/
def NPClass (L : List Bool → Prop) : Prop := InNP L

/-- P = NP：每个语言属于 P 当且仅当属于 NP。这就是千禧年难题的正式陈述。 -/
def PEqualsNP : Prop := ∀ L : List Bool → Prop, InP L ↔ InNP L

/-- P ≠ NP 的正式陈述。 -/
def PNeqNP : Prop := ¬ PEqualsNP

/-- P = NP 等价于「每个 NP 语言都属于 P」（另一半 P ⊆ NP 已证）。 -/
theorem pEqualsNP_iff : PEqualsNP ↔ ∀ L : List Bool → Prop, InNP L → InP L := by
  constructor
  · -- 类相等 ⇒ 逐个语言检验
    intro h L hL
    exact (h L).mpr hL
  · -- P ⊆ NP 已证；假设给出 NP ⊆ P
    intro h L
    exact ⟨fun hP => inP_subset_inNP hP, fun hN => h L hN⟩

/-- P ≠ NP 等价于「存在一个属于 NP 但不属于 P 的语言」。 -/
theorem pNeqNP_iff : PNeqNP ↔ ∃ L : List Bool → Prop, InNP L ∧ ¬ InP L := by
  constructor
  · -- 不相等 ⇒ 存在反例语言（核心库无 by_contra，改用 Classical.byContradiction）
    intro hne
    apply Classical.byContradiction
    intro h
    apply hne
    intro L
    constructor
    · intro hP
      exact inP_subset_inNP hP
    · intro hN
      apply Classical.byContradiction
      intro hP
      exact h ⟨L, hN, hP⟩
  · -- 有反例 ⇒ 类不可能相等
    rintro ⟨L, hN, hP⟩ hEq
    exact hP ((hEq L).mpr hN)

/-- 一致性检查：P = NP 与 P ≠ NP 不可能同时成立。
    这不是在解决难题，只是在确认两个陈述互为否定。 -/
theorem not_both : ¬ (PEqualsNP ∧ PNeqNP) := by
  intro ⟨h1, h2⟩
  exact h2 h1

end Pnp
