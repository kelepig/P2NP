module

/-
  文件：PnpMathlib/Complexity.lean
  主题：用 Mathlib 现有的图灵机模型（TM2）与多项式时间可计算性定义，
        搭建 P 类的语言层定义。

  重要边界（务必先读）：
    - Mathlib 没有 P、NP 的复杂性类定义；它提供的是机器模型与
      `TM2ComputableInPolyTime`（多项式时间可计算的函数）。
    - 因此本文件的 `InP` 是在 Mathlib 的机器与时间定义之上写的标准封装，
      不是「另起炉灶的公式」：机器、步数、输出语义全部来自 Mathlib。
    - P vs NP 本身仍未解决。本文件不声称、也不可能证明 P = NP。
-/

import Mathlib.Computability.TuringMachine.Computable

namespace PnpMathlib

open Turing

/-- 多项式时间可计算的函数（二元输入输出）：完全复用 Mathlib 的 TM2 模型。 -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime
    (α := List Bool) (β := List Bool) (αΓ := Bool) (βΓ := Bool) id id f)

/-- 多项式时间可判定的语言：存在多项式时间可计算的判定函数。 -/
def InP (L : List Bool → Prop) : Prop :=
  ∃ f : List Bool → Bool,
    (∀ w : List Bool, (f w = true) ↔ L w) ∧
      Nonempty (TM2ComputableInPolyTime
        (α := List Bool) (β := Bool) (αΓ := Bool) (βΓ := Bool)
        id Computability.encodeBool f)

/-- 自检：恒等函数在 Mathlib 的模型下是多项式时间可计算的。 -/
theorem id_polyTime : PolyTimeComputable (fun w : List Bool => w) :=
  ⟨Turing.idComputableInPolyTime (α := List Bool) (αΓ := Bool) id⟩

end PnpMathlib
