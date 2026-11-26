/-
  文件：Pnp/IndexedSimulation.lean
  主题：用计数器下标表达的接受语义（B5 阶段 3 的语义规格）。

  把 `acceptsWithin_allSeqs` 与下标解码 `seqOfIndex` 合起来：

    M 在 T 步内接受  ⇔  存在 i < B^T，
        按 B 进制把 i 解码成长度 T 的选择序列后模拟到接受状态。

  这就是单带模拟器要实现的规格：机器只需要维护一个计数器 i，
  每步用「模 B」「除 B」取出一位选择，而不必在纸带上存 `allSeqs` 整张表。
  机器本身的实现（计数器进位、模拟区、接受即停）仍未完成，
  因此 `inNP_subset_inExp` 尚未证明。
-/

import Pnp.Simulation
import Pnp.Indexing

namespace Pnp

/-- 接受语义的计数器版本。 -/
theorem acceptsWithin_iff_exists_index {q : Nat} {M : NTM q} {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T : Nat) :
    M.AcceptsWithin w T ↔
      ∃ i : Nat, i < B ^ T ∧ ∃ c : Config q,
        M.runWith T (seqOfIndex B T i) (M.init w) = some c ∧ c.state = M.accept := by
  rw [acceptsWithin_allSeqs hB hBpos]
  constructor
  · -- 枚举中的序列都可以由某个 i < B^T 解码得到
    rintro ⟨cs, hcs, c, hrun, hstate⟩
    obtain ⟨i, hi, hseq⟩ := exists_index_of_mem_allSeqs hBpos hcs
    exact ⟨i, hi, c, by rw [hseq]; exact hrun, hstate⟩
  · -- 任何 i < B^T 的解码结果都在枚举里
    rintro ⟨i, _, c, hrun, hstate⟩
    exact ⟨seqOfIndex B T i, seqOfIndex_mem_allSeqs B T i hBpos, c, hrun, hstate⟩

end Pnp
