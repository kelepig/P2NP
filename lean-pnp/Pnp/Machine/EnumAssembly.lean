/-
  文件：Pnp/Machine/EnumAssembly.lean
  主题：B5 义务 e——「枚举器一就位，NP ⊆ EXP 即成立」的装配引理。

  `inNP_bruteForce_spec` 已把 NP 的语义化约成一条 `bruteForce` 规格：
  存在非确定机 `M` 与次数 `k`，使 `bruteForce (branchBound+1) (n^k+k)` 判定 `L`。
  本文件证明：**只要有一台确定性图灵机 `E` 在 `2^(n^k0+k0)` 步内判定该 `bruteForce`，
  就能立刻得到 `InExp L`**。于是整个 B5 只剩一个纯机器义务：
  构造 `E` 并证 `hHalt` / `hAcc` 两条前提。

  Assembly lemma: once a deterministic machine `E` decides the `bruteForce`
  Boolean within exponential time, `InExp L` follows immediately.
-/
import Pnp.Search
import Pnp.Classes

namespace Pnp

/-- **B5 装配（义务 e）**：若 `M` 在 `n^k+k` 步内判定 `L`，且确定性机 `E` 在
    `2^(n^k0+k0)` 步内判定同一 `M` 的暴力搜索，则 `L ∈ EXP`。

    If an NTM `M` decides `L` in polynomial time and a DTM `E` decides `M`'s
    brute-force Boolean within `2^(n^k0+k0)`, then `L ∈ EXP`. -/
theorem inExp_of_enumerator {L : List Bool → Prop} {k q : Nat} (M : NTM q)
    (hdec : M.DecidesIn (fun n => n ^ k + k) L)
    {q' : Nat} (E : DTM q') (hne : E.accept ≠ E.reject) (k0 : Nat)
    (hHalt : ∀ w : List Bool, E.HaltsWithin w (2 ^ (w.length ^ k0 + k0)))
    (hAcc : ∀ w : List Bool,
      E.AcceptsWithin w (2 ^ (w.length ^ k0 + k0)) ↔
        M.bruteForce (M.branchBound + 1) (w.length ^ k + k) w = true) :
    InExp L := by
  refine ⟨k0, q', E, hne, ?_⟩
  intro w
  -- `M` 的暴力搜索在多项式预算内判定 `L`（`bruteForce_decides`）。
  have hBF : M.bruteForce (M.branchBound + 1) (w.length ^ k + k) w = true ↔ L w :=
    M.bruteForce_branchBound_decides hdec w
  -- `E` 判定 `bruteForce`，故判定 `L`；停机性与接受等价同时给出。
  exact ⟨hHalt w, (hAcc w).trans hBF⟩

/-- **分支块的 `hb` 前提**：若 `B + 2 < 2^b`，则下标 `i` 解码出的每条选择 `k'`
    满足 `k' + 2 < 2^b`（`passRun` 的块界前提）。
    The block-bound premise for the branch decoded from index `i`. -/
theorem seqOfIndex_hb (B T i b : Nat) (hB : 0 < B) (hb : B + 2 < 2 ^ b) :
    ∀ k' ∈ seqOfIndex B T i, k' + 2 < 2 ^ b := by
  intro k' hk'
  have hlt : k' < B := seqOfIndex_lt_bound B T i hB k' hk'
  omega

end Pnp

