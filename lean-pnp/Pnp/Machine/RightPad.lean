/-
  文件：Pnp/Machine/RightPad.lean
  主题：区域右侧预留 ⇒ 右尾绝缘的**长度判据**（E 机把输入副本挂在区域右侧时使用）。

  背景：E 的实际纸带 = 理想区域编码 + 远端右尾（输入副本）。`PadRight` 绝缘要求理想运行的
  每一步右侧非空；本文件把它化为**一条纯算术条件**：区域右侧预留格数 ≥ 预算步数即可。

  关键观察（docs/07 #146/#164）：一轮的成本（`roundCostStay` 等）只依赖 `pre` 长度与
  计数器内容，**不依赖 `post` 长度**；因此把右侧预留取成 ≥ 预算不增加时间界，却免费给出
  右尾绝缘。于是无需逐段核算导航相位。

  Right-side padding gives a length criterion for right-tail insulation: the actual tape is the
  ideal region encoding followed by a far-right tail (the input copy). One round's cost does not
  depend on `post` length, so padding the right side up to the step budget buys insulation at no
  extra time cost.
-/

import Pnp.Machine.Locality
import Pnp.Machine.PadVerdict

namespace Pnp

namespace Tape

/-- 在右侧追加尾巴即得右副本绝缘。 Insulation from an explicit far-right append. -/
theorem padRight_of_append (t : Tape) (C : List Sym) :
    PadRight t ⟨t.left, t.right ++ C⟩ :=
  ⟨rfl, C, rfl⟩

end Tape

namespace DTM

variable {q : Nat}

namespace Reg

/-- 区域编码的右侧长度：头标记 1 个符号 + 每格 3 个符号。
    The right side of a region encoding is the head marker plus three symbols per cell. -/
theorem enc_right_length (x : Reg q) (L : List Sym) :
    (Reg.enc x L).right.length = 3 * x.post.length + 1 := by
  show ((some true) :: codeCells x.post).length = 3 * x.post.length + 1
  rw [List.length_cons, codeCells_length]

end Reg

/-- **区域右侧预留 ⇒ 右侧不触底**：`K ≤ |post|` 时，区域编码起步的任意运行前 `K` 步
    右侧都非空（`K+1 ≤ 3|post|+1`）。
    Right-side padding keeps the right nonempty: if `K` cells are reserved on the right, any
    run of `K` steps starting from the region encoding keeps a nonempty right side. -/
theorem right_safe_of_enc (M : DTM q) (K : Nat) (st : Fin q) (x : Reg q) (L : List Sym)
    (h : K ≤ x.post.length) :
    ∀ j, j < K → (M.run j (Config.mk st (Reg.enc x L))).tape.right ≠ [] := by
  have hlen : K + 1 ≤ (Reg.enc x L).right.length := by
    rw [Reg.enc_right_length]
    omega
  exact right_safe_of_len M K (Config.mk st (Reg.enc x L)) hlen

/-- **右尾绝缘（区域版）**：实际纸带是理想区域编码加上远端右尾（副本），右侧预留 ≥ 预算
    ⇒ 跑 `K` 步后状态相同。
    Region-level right-tail insulation: with `K` cells reserved on the right, a far-right tail
    never changes the state trajectory. -/
theorem run_state_eq_of_padRight_enc (M : DTM q) (K : Nat) (st : Fin q) (x : Reg q)
    (L : List Sym) (t : Tape) (hP : Tape.PadRight (Reg.enc x L) t)
    (h : K ≤ x.post.length) :
    (M.run K (Config.mk st (Reg.enc x L))).state = (M.run K (Config.mk st t)).state := by
  refine run_state_eq_of_padRight M K (Config.mk st (Reg.enc x L)) (Config.mk st t) rfl hP ?_
  intro j hj
  exact right_safe_of_enc M K st x L h j hj

/-- **右尾绝缘的判定版（区域版）**：右侧预留 ≥ 预算时，远端右尾不影响 `K` 步内的接受判定。
    Verdict form: a far-right tail does not change acceptance within `K` steps. -/
theorem run_accept_eq_of_padRight_enc (M : DTM q) (K : Nat) (st : Fin q) (x : Reg q)
    (L : List Sym) (t : Tape) (hP : Tape.PadRight (Reg.enc x L) t)
    (h : K ≤ x.post.length) :
    ((M.run K (Config.mk st (Reg.enc x L))).state = M.accept ↔
      (M.run K (Config.mk st t)).state = M.accept) := by
  rw [run_state_eq_of_padRight_enc M K st x L t hP h]

/-- **停机后判定不变**：两个格局在第 `n` 步后状态相同且都已停机，则在任意更大预算 `K`
    下接受判定相同（两边都冻结在原格局）。
    Once both runs halt at the same state after `n` steps, the verdict at any larger budget is
    the same. -/
theorem run_accept_eq_of_halted_at (M : DTM q) (n K : Nat) (hn : n ≤ K)
    (c1 c2 : Config q)
    (hs : (M.run n c1).state = (M.run n c2).state)
    (h1 : M.halted (M.run n c1) = true) :
    ((M.run K c1).state = M.accept ↔ (M.run K c2).state = M.accept) := by
  have h2 : M.halted (M.run n c2) = true := by
    rw [← halted_congr M hs]
    exact h1
  have hK : K = n + (K - n) := by omega
  have e1 : M.run K c1 = M.run n c1 := by
    rw [hK, run_add, run_of_halted M _ h1]
  have e2 : M.run K c2 = M.run n c2 := by
    rw [hK, run_add, run_of_halted M _ h2]
  rw [e1, e2, hs]

/-- **冻结时刻的右尾判定搬运（区域版）**：实际纸带 = 理想区域编码 + 远端右尾；右侧预留
    `≥ n`（冻结时刻）且理想运行在第 `n` 步已停机 ⇒ 任意更大预算 `K ≥ n` 下接受判定相同。
    这是 E 机逐分支读判据的接口：预留只需**多项式**（覆盖到冻结时刻即可）。
    Freeze-time verdict transfer: padding up to the freeze moment `n` suffices, and the
    verdict persists to any larger budget. -/
theorem run_accept_eq_at_budget_of_padRight_enc (M : DTM q) (n K : Nat) (hn : n ≤ K)
    (st : Fin q) (x : Reg q) (L : List Sym) (t : Tape)
    (hP : Tape.PadRight (Reg.enc x L) t) (h : n ≤ x.post.length)
    (h1 : M.halted (M.run n (Config.mk st (Reg.enc x L))) = true) :
    ((M.run K (Config.mk st (Reg.enc x L))).state = M.accept ↔
      (M.run K (Config.mk st t)).state = M.accept) := by
  refine run_accept_eq_of_halted_at M n K hn _ _ ?_ h1
  exact run_state_eq_of_padRight_enc M n st x L t hP h

/-- **远端右尾追加不改变判定（冻结时刻版）**：在纸带右端追加任意尾巴，只要右侧预留覆盖到
    冻结时刻 `n`（`n+1 ≤ 右长`）且第 `n` 步已停机，则任意预算 `K ≥ n` 下接受判定相同。
    这是 E 装配时「实际纸带 = 理想纸带 + 右侧输入副本」的直接接口。
    Appending a far-right tail does not change the verdict once the ideal run has halted by a
    time covered by the right padding. -/
theorem run_accept_eq_at_budget_of_right_append (M : DTM q) (n K : Nat) (hn : n ≤ K)
    (c : Config q) (copy : List Sym) (hlen : n + 1 ≤ c.tape.right.length)
    (h1 : M.halted (M.run n c) = true) :
    ((M.run K c).state = M.accept ↔
      (M.run K (Config.mk c.state ⟨c.tape.left, c.tape.right ++ copy⟩)).state
        = M.accept) := by
  refine run_accept_eq_of_halted_at M n K hn _ _ ?_ h1
  exact run_state_eq_of_padRight M n c _ rfl (Tape.padRight_of_append c.tape copy)
    (right_safe_of_len M n c (by omega))

end DTM

end Pnp
