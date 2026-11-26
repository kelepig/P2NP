/-
  文件：Pnp/Search.lean
  主题：可执行的暴力搜索判定过程（B5 阶段 3 的可执行规格）。

  `bruteForce M B T w` 就是模拟器要执行的算法：
    对 i = 0, 1, ..., B^T - 1，把 i 解码成选择序列并模拟 T 步，
    一旦某条分支接受就返回 true。

  本文件证明它与 `NTM.AcceptsWithin` 等价：
    `bruteForce = true  ⇔  在 T 步内接受`。

  这仍是**函数层**的规格；把它实现成单带图灵机（阶段 3c）才完成 NP ⊆ EXP。
-/

import Pnp.IndexedSimulation

namespace Pnp

namespace NTM

variable {q : Nat}

/-- 暴力搜索：枚举计数器 i < B^T，解码后模拟，任一分支接受即为 true。 -/
def bruteForce (M : NTM q) (B T : Nat) (w : List Bool) : Bool :=
  (List.range (B ^ T)).any (fun i =>
    match M.runWith T (seqOfIndex B T i) (M.init w) with
    | some c => c.state == M.accept
    | none => false)

/-- 暴力搜索结果正确：返回 true 当且仅当 T 步内存在接受分支。 -/
theorem bruteForce_eq_true_iff (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T : Nat) :
    M.bruteForce B T w = true ↔ M.AcceptsWithin w T := by
  unfold bruteForce
  rw [List.any_eq_true]
  constructor
  · -- 找到一条接受分支
    rintro ⟨i, hi, htrue⟩
    rw [List.mem_range] at hi
    rw [acceptsWithin_iff_exists_index hB hBpos w T]
    cases hr : M.runWith T (seqOfIndex B T i) (M.init w) with
    | none => simp [hr] at htrue
    | some c =>
        simp only [hr] at htrue
        exact ⟨i, hi, c, hr, by simpa using htrue⟩
  · -- 接受分支给出一个计数器值
    intro hacc
    obtain ⟨i, hi, c, hrun, hstate⟩ :=
      (acceptsWithin_iff_exists_index hB hBpos w T).mp hacc
    refine ⟨i, ?_, ?_⟩
    · rw [List.mem_range]; exact hi
    · rw [hrun]
      simp [hstate]

/-- 把暴力搜索与判定器语义对接：若 M 在 T 步内判定 L，
    则同一预算下的暴力搜索也判定 L。 -/
theorem bruteForce_decides (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    {T : Nat → Nat} {L : List Bool → Prop}
    (hdec : M.DecidesIn T L) (w : List Bool) :
    M.bruteForce B (T w.length) w = true ↔ L w :=
  (M.bruteForce_eq_true_iff hB hBpos w (T w.length)).trans (hdec w).2

/-- 取 `branchBound + 1` 作为统一分支上界，搜索仍然正确。 -/
theorem bruteForce_branchBound_decides (M : NTM q)
    {T : Nat → Nat} {L : List Bool → Prop}
    (hdec : M.DecidesIn T L) (w : List Bool) :
    M.bruteForce (M.branchBound + 1) (T w.length) w = true ↔ L w := by
  refine M.bruteForce_decides (B := M.branchBound + 1) ?_ (Nat.succ_pos _) hdec w
  intro s a
  exact Nat.le_trans (M.length_step_le_branchBound s a) (Nat.le_succ _)

end NTM

/-- NP 的机器定义直接给出一个「暴力搜索规格」：存在非确定机 M 与次数 k，
    使 `bruteForce (branchBound+1) (n^k+k)` 判定 L。
    剩余工程是把该 Boolean 搜索实现成确定性图灵机（B5 阶段 3c-ii）。 -/
theorem inNP_bruteForce_spec {L : List Bool → Prop} (h : InNP L) :
    ∃ (k q : Nat) (M : NTM q), ∀ w : List Bool,
      M.bruteForce (M.branchBound + 1) (w.length ^ k + k) w = true ↔ L w := by
  rcases h with ⟨k, q, M, _hne, hdec⟩
  exact ⟨k, q, M, fun w => M.bruteForce_branchBound_decides hdec w⟩

end Pnp
