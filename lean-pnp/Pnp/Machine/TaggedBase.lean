/-
  文件：Pnp/Machine/TaggedBase.lean
  主题：「数字标签」组合器的算术底座（状态布局 `d*q + p`）。

  为把机器 A 的状态空间放大 B 倍（状态 `d*q+p`），需要两条界：
    - `mul_succ_le_mul`：`d < B ⇒ (d+1)*q ≤ B*q`；
    - `add_mul_lt_mul`：`d < B`、`p < q ⇒ d*q + p < B*q`（嵌入状态仍在界内）。
  组合器本体（`tagged`）在 `run_embed` 之上构造，仍在 `.tmp/gen_round/Tagged.wip.lean`
  收敛中；本文件只保留已验证的算术部分。
-/

import Pnp.Classes

namespace Pnp

/-- `d < B ⇒ (d+1)*q ≤ B*q`。 -/
theorem mul_succ_le_mul {B q d : Nat} (hd : d < B) : (d + 1) * q ≤ B * q :=
  Nat.mul_le_mul_right q (Nat.succ_le_of_lt hd)

/-- `d < B`、`p < q ⇒ d*q + p < B*q`。 -/
theorem add_mul_lt_mul {B q d p : Nat} (hd : d < B) (hp : p < q) :
    d * q + p < B * q := by
  have h1 : d * q + q ≤ B * q := by
    calc d * q + q = (d + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ B * q := mul_succ_le_mul hd
  omega

end Pnp
