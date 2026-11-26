module

/-
  文件：PnpMathlib.lean
  作用：Mathlib 实验工程的入口。
  当前只做「环境自检」：确认 Mathlib 可导入，并调用现成的鸽笼原理
  作为 A2 的对照实现（正式实现仍保留在零依赖工程 lean-pnp 中）。
-/
import Mathlib.Data.Fintype.Card
import PnpMathlib.Complexity

namespace PnpMathlib

/-- 鸽笼原理（Mathlib 版）：若 f : α → β 是单射，则 β 的元素个数不少于 α。 -/
example {α β : Type} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f) :
    Fintype.card α ≤ Fintype.card β :=
  Fintype.card_le_of_injective f hf

end PnpMathlib
