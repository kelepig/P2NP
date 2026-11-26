/-
  文件：Pnp/Machine/SimCostBound.lean
  主题：单轮代价 `roundCost{Stay,Right,Left}` 的线性上界——为外层枚举的时间界提供
        每轮成本的显式界（区域前缀格数、零计数 `z`、块值 `k` 的线性组合）。

  用途（B5 3c-ii 时间界，见 auto-run-log #117 义务 d）：通路步数 `r.steps` 是各轮代价之和，
  每轮代价可界为 `O(|pre| + z + k)`；把逐轮界相加即得 `r.steps = O(T·poly)`，最终收进
  `2^(n^K+K)`。本文件先给逐轮线性界（纯长度算术，`simp + omega` 即可）。

  Linear upper bounds on one round's step cost, a building block for the exponential
  time bound. Each round's cost is bounded linearly in `|pre|`, the zero counter `z`,
  and the block value `k`.
-/

import Pnp.Machine.SimPass

namespace Pnp

namespace DTM

/-- 原地一轮代价线性上界。Cost of one stay round is linear in `|pre|, z, k`. -/
theorem roundCostStay_le {q : Nat} (x : Reg q) (z k : Nat) (s' : Sym) :
    roundCostStay x z k s' ≤ 30 + 6 * x.pre.length + 2 * z + 2 * k := by
  simp only [roundCostStay, List.length_cons, List.length_reverse, List.length_append,
    List.length_replicate, codeCells_length]
  omega

/-- 右移一轮代价线性上界（前缀临时增一格；用原地版加一格前缀化归）。 -/
theorem roundCostRight_le {q : Nat} (x : Reg q) (z k : Nat) (p : Sym × Bool) (s' : Sym) :
    roundCostRight x z k p s' ≤ 40 + 6 * x.pre.length + 2 * z + 2 * k := by
  -- 右移代价 = 把前缀补一格后的原地代价
  have heq : roundCostRight x z k p s'
      = roundCostStay { x with pre := x.pre ++ [(s', false)] } z k s' := rfl
  rw [heq]
  have h := roundCostStay_le { x with pre := x.pre ++ [(s', false)] } z k s'
  simp only [List.length_append, List.length_singleton] at h ⊢
  omega

/-- 左移一轮代价线性上界（前缀按 `pre'` 计）。 -/
theorem roundCostLeft_le {q : Nat} (z k : Nat) (pre' : List (Sym × Bool)) (cq : Sym × Bool)
    (s' : Sym) :
    roundCostLeft (q := q) z k pre' cq s' ≤ 30 + 6 * pre'.length + 2 * z + 2 * k := by
  simp only [roundCostLeft, List.length_cons, List.length_reverse, List.length_append,
    List.length_replicate, codeCells_length]
  omega

end DTM

end Pnp
