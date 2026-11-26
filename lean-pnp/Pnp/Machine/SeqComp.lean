/-
  文件：Pnp/Machine/SeqComp.lean
  主题：两台确定性图灵机的顺序组合 `seqComp`。

  用途：B5 的枚举循环要把多个机器组件串起来：
    加一（`binInc`）→ 回绕检测（`binZeroCheck`）→ 下一轮模拟，
  这些组件各自只有几个状态，必须能合并成「一台」状态数相加的机器。

  组合语义（状态 = `Fin (q + q')`）：
    - `Fin.castAdd q' s`：左侧，原封不动地执行 A；
    - 走到 A 的接受状态时，下一步原地（`Dir.stay`）转入 B 的起始状态；
    - `Fin.natAdd q s`：右侧，执行 B；
    - 组合机的接受/拒绝状态只取自 B。

  本文件提供三类桥接引理：
    - `seqComp_embed_left` / `seqComp_embed_right`：左右两段各自可被 `run_embed` 搬运；
    - `seqComp_switch`：A 接受后一步转入 B 的精确纸带状态。
-/

import Pnp.Machine.Embed

namespace Pnp

namespace DTM

variable {q q' : Nat}

/-- 组合机的转移函数：左侧原样执行 A；A 接受则原地转入 B 的起始状态；
    右侧原样执行 B。 -/
def seqCompStep (A : DTM q) (B : DTM q') :
    Fin (q + q') → Sym → Fin (q + q') × Sym × Dir :=
  fun s a =>
    if h : s.val < q then
      if hs : s.val = A.accept.val then
        -- A 已接受：不写、不动，直接把控制状态切到 B 的起点
        (Fin.natAdd q B.start, a, Dir.stay)
      else
        let r := A.step ⟨s.val, h⟩ a
        (Fin.castAdd q' r.1, r.2.1, r.2.2)
    else
      let r := B.step ⟨s.val - q, by have hs := s.isLt; omega⟩ a
      (Fin.natAdd q r.1, r.2.1, r.2.2)

/-- 顺序组合：先跑 A，A 接受后接着跑 B。 -/
def seqComp (A : DTM q) (B : DTM q') : DTM (q + q') where
  step := seqCompStep A B
  start := Fin.castAdd q' A.start
  accept := Fin.natAdd q B.accept
  reject := Fin.natAdd q B.reject

/-- 左侧转移与 A 完全一致（A 非接受状态处）。 -/
theorem seqComp_step_castAdd (A : DTM q) (B : DTM q') (s : Fin q) (a : Sym)
    (ha : s ≠ A.accept) :
    (seqComp A B).step (Fin.castAdd q' s) a
      = (Fin.castAdd q' (A.step s a).1, (A.step s a).2) := by
  simp only [seqComp, seqCompStep, Fin.val_castAdd]
  rw [dite_eq_left s.isLt]
  have hs : ¬ (s.val = A.accept.val) := fun h => ha (Fin.ext h)
  rw [dite_eq_right hs]

/-- 右侧转移与 B 完全一致。 -/
theorem seqComp_step_natAdd (A : DTM q) (B : DTM q') (s : Fin q') (a : Sym) :
    (seqComp A B).step (Fin.natAdd q s) a
      = (Fin.natAdd q (B.step s a).1, (B.step s a).2) := by
  simp only [seqComp, seqCompStep, Fin.val_natAdd]
  rw [dite_eq_right (by omega : ¬ q + s.val < q)]
  -- 状态 `⟨q + s.val - q, _⟩` 就是 `s` 本身
  have hs : (⟨q + s.val - q, by have := s.isLt; omega⟩ : Fin q') = s :=
    Fin.ext (by simp)
  rw [hs]

/-- 组合机接受态编号 = 左段状态数 + 右段接受态编号（定义等价）。
    The accept index of `seqComp` in value form. -/
theorem seqComp_accept_val (A : DTM q) (B : DTM q') :
    (seqComp A B).accept.val = q + B.accept.val := rfl

/-- 组合机拒绝态编号 = 左段状态数 + 右段拒绝态编号（定义等价）。
    The reject index of `seqComp` in value form. -/
theorem seqComp_reject_val (A : DTM q) (B : DTM q') :
    (seqComp A B).reject.val = q + B.reject.val := rfl

/-- 左侧状态永远不会落入组合机的接受/拒绝状态。 -/
theorem seqComp_halt_castAdd (A : DTM q) (B : DTM q') (s : Fin q) :
    (seqComp A B).accept ≠ Fin.castAdd q' s
      ∧ (seqComp A B).reject ≠ Fin.castAdd q' s := by
  constructor
  · intro h
    have h2 : q + B.accept.val = s.val := by
      have := congrArg Fin.val h
      simpa only [seqComp, Fin.val_natAdd, Fin.val_castAdd] using this
    have hlt : q + B.accept.val < q := by rw [h2]; exact s.isLt
    exact Nat.lt_irrefl q (Nat.lt_of_le_of_lt (Nat.le_add_right q _) hlt)
  · intro h
    have h2 : q + B.reject.val = s.val := by
      have := congrArg Fin.val h
      simpa only [seqComp, Fin.val_natAdd, Fin.val_castAdd] using this
    have hlt : q + B.reject.val < q := by rw [h2]; exact s.isLt
    exact Nat.lt_irrefl q (Nat.lt_of_le_of_lt (Nat.le_add_right q _) hlt)

/-- 右侧状态只在 B 自己的接受/拒绝状态处与组合机终止状态重合。 -/
theorem seqComp_halt_natAdd (A : DTM q) (B : DTM q') (s : Fin q')
    (ha : s ≠ B.accept) (hr : s ≠ B.reject) :
    (seqComp A B).accept ≠ Fin.natAdd q s
      ∧ (seqComp A B).reject ≠ Fin.natAdd q s := by
  constructor
  · intro h
    have h2 : q + B.accept.val = q + s.val := by
      have := congrArg Fin.val h
      simpa only [seqComp, Fin.val_natAdd, Fin.val_castAdd] using this
    exact ha (Fin.ext (Nat.add_left_cancel h2).symm)
  · intro h
    have h2 : q + B.reject.val = q + s.val := by
      have := congrArg Fin.val h
      simpa only [seqComp, Fin.val_natAdd, Fin.val_castAdd] using this
    exact hr (Fin.ext (Nat.add_left_cancel h2).symm)

/-- 左段：在组合机里执行 A 的 `n` 步（A 在前缀上不终止）。 -/
theorem seqComp_embed_left (A : DTM q) (B : DTM q') (n : Nat) (c : Config q)
    (hnh : ∀ k, k < n → A.halted (A.run k c) = false) :
    (seqComp A B).run n ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.castAdd q' (A.run n c).state, (A.run n c).tape⟩ :=
  run_embed A (seqComp A B) (Fin.castAdd q')
    (fun s a ha _ => seqComp_step_castAdd A B s a ha)
    (fun s _ _ => seqComp_halt_castAdd A B s) n c hnh

/-- 右段：在组合机里执行 B 的 `n` 步（B 在前缀上不终止）。 -/
theorem seqComp_embed_right (A : DTM q) (B : DTM q') (n : Nat) (c : Config q')
    (hnh : ∀ k, k < n → B.halted (B.run k c) = false) :
    (seqComp A B).run n ⟨Fin.natAdd q c.state, c.tape⟩
      = ⟨Fin.natAdd q (B.run n c).state, (B.run n c).tape⟩ :=
  run_embed B (seqComp A B) (Fin.natAdd q)
    (fun s a _ _ => seqComp_step_natAdd A B s a)
    (fun s ha hr => seqComp_halt_natAdd A B s ha hr) n c hnh

/-- 切换步：A 接受后，组合机原地转入 B 的起始状态。
    纸带按一步的语义更新（读到的符号原样写回）。 -/
theorem seqComp_switch (A : DTM q) (B : DTM q') (c : Config q)
    (hacc : c.state = A.accept) :
    (seqComp A B).run 1 ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.natAdd q B.start,
          (c.tape.write c.tape.read).move Dir.stay⟩ := by
  -- 组合机在左侧状态处不会停机，因此 `run 1` 就是一步转移
  have hneA : (Fin.castAdd q' c.state) ≠ (seqComp A B).accept :=
    (seqComp_halt_castAdd A B c.state).1.symm
  have hneR : (Fin.castAdd q' c.state) ≠ (seqComp A B).reject :=
    (seqComp_halt_castAdd A B c.state).2.symm
  have hnh : (seqComp A B).halted ⟨Fin.castAdd q' c.state, c.tape⟩ = false := by
    simp [halted, hneA, hneR]
  rw [run_succ_of_not_halted (M := seqComp A B) 0 _ hnh]
  -- 展开一步转移：左侧、且状态等于 A.accept
  simp only [run, stepConfig, seqComp, seqCompStep, Fin.val_castAdd]
  rw [dite_eq_left c.state.isLt]
  have hs : c.state.val = A.accept.val := congrArg Fin.val hacc
  rw [dite_eq_left hs]

/-- **组合机整段运行（装配引理）**：A 恰好 `na` 步跑到接受态、纸带 `t'`（右侧非空，切换步
    不改变纸带），B 从起始态在 `t'` 上跑 `nb` 步到接受态、纸带 `t''`；两段各自前缀内不停机。
    结论：组合机 `na + 1 + nb` 步从 A 的起点直达 B 的接受态。
    End-to-end run of a sequential composition: A's full run, the one-step switch, B's run. -/
theorem seqComp_run (A : DTM q) (B : DTM q') (na nb : Nat) (c : Config q)
    (t' t'' : Tape)
    (hA : A.run na c = ⟨A.accept, t'⟩)
    (hne : t'.right ≠ [])
    (hB : B.run nb ⟨B.start, t'⟩ = ⟨B.accept, t''⟩)
    (hnhA : ∀ k, k < na → A.halted (A.run k c) = false)
    (hnhB : ∀ k, k < nb → B.halted (B.run k ⟨B.start, t'⟩) = false) :
    (seqComp A B).run (na + 1 + nb) ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.natAdd q B.accept, t''⟩ := by
  -- 先拆出 B 段，再把前段（A + 切换）整体化简
  rw [show na + 1 + nb = (na + 1) + nb from by omega,
    DTM.run_add (seqComp A B) (na + 1) nb]
  have hInner : (seqComp A B).run (na + 1) ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.natAdd q B.start, t'⟩ := by
    rw [DTM.run_add (seqComp A B) na 1, seqComp_embed_left A B na c hnhA, hA,
      seqComp_switch A B ⟨A.accept, t'⟩ rfl]
    -- 切换步的纸带：写回读到的符号、原地不动
    rw [show ((t'.write t'.read).move Dir.stay) = t' from by
      rw [Tape.write_read _ hne, Tape.move]]
  rw [hInner, seqComp_embed_right A B nb ⟨B.start, t'⟩ hnhB, hB]

/-- **右段「吸收停机」搬运**：组合机在右段起点（`natAdd` 形态）出发的 `m` 步与 B 自己的
    `m` 步逐字一致——**不要求 B 全程不停机**：B 中途停机时双方同时冻结，等式仍成立。
    The right segment follows `B` step by step even if `B` halts midway (both freeze).
    This removes the `hnhB` premise from phase chaining. -/
theorem seqComp_run_natAdd (A : DTM q) (B : DTM q') (m : Nat) (c : Config q') :
    (seqComp A B).run m ⟨Fin.natAdd q c.state, c.tape⟩
      = ⟨Fin.natAdd q (B.run m c).state, (B.run m c).tape⟩ := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
      rw [DTM.run]
      by_cases hh : B.halted c = true
      · -- B 已停机：双方原地冻结
        have hx : c.state = B.accept ∨ c.state = B.reject := by
          simpa [DTM.halted, Bool.or_eq_true] using hh
        have hC : (seqComp A B).halted ⟨Fin.natAdd q c.state, c.tape⟩ = true := by
          apply halted_of_accept_or_reject
          rcases hx with h | h
          · exact Or.inl (by show Fin.natAdd q c.state = Fin.natAdd q B.accept; rw [h])
          · exact Or.inr (by show Fin.natAdd q c.state = Fin.natAdd q B.reject; rw [h])
        rw [hC]
        simp only [ite_true]
        rw [run_of_halted B c hh (m + 1)]
      · -- B 未停机：组合机也未停机，两边各走一步
        have hx : B.halted c = false := by
          cases hv : B.halted c with
          | false => rfl
          | true => exact absurd hv hh
        have h1 : c.state ≠ B.accept := by
          intro h
          have : B.halted c = true := halted_of_accept_or_reject B c (Or.inl h)
          rw [this] at hx
          exact Bool.noConfusion hx
        have h2 : c.state ≠ B.reject := by
          intro h
          have : B.halted c = true := halted_of_accept_or_reject B c (Or.inr h)
          rw [this] at hx
          exact Bool.noConfusion hx
        have hC : (seqComp A B).halted ⟨Fin.natAdd q c.state, c.tape⟩ = false := by
          rw [DTM.halted, Bool.or_eq_false_iff]
          exact ⟨beq_eq_false_iff_ne.mpr (Ne.symm (seqComp_halt_natAdd A B c.state h1 h2).1),
            beq_eq_false_iff_ne.mpr (Ne.symm (seqComp_halt_natAdd A B c.state h1 h2).2)⟩
        rw [hC]
        simp only [Bool.false_eq_true, ite_false]
        have hstep : (seqComp A B).stepConfig ⟨Fin.natAdd q c.state, c.tape⟩
            = ⟨Fin.natAdd q (B.stepConfig c).state, (B.stepConfig c).tape⟩ := by
          simp only [DTM.stepConfig, seqComp_step_natAdd A B c.state c.tape.read]
        have hB : B.run (m + 1) c = B.run m (B.stepConfig c) := by
          rw [DTM.run, hx]
          simp
        rw [hstep, ih (B.stepConfig c), hB]

/-- **相位吸收**：A 恰好 `na` 步跑到接受态后交给 B，组合机再跑 `nb` 步。
    与 `seqComp_run` 的区别：**不需要 B 前缀不停机**（B 停机即冻结，判定照样可读）。
    Phase absorption: after A's exactly-`na`-step run, the composite follows B for `nb`
    arbitrary steps, with no non-halting premise on B. -/
theorem seqComp_run_absorb (A : DTM q) (B : DTM q') (na nb : Nat) (c : Config q) (t' : Tape)
    (hA : A.run na c = ⟨A.accept, t'⟩) (hne : t'.right ≠ [])
    (hnhA : ∀ k, k < na → A.halted (A.run k c) = false) :
    (seqComp A B).run (na + 1 + nb) ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.natAdd q (B.run nb ⟨B.start, t'⟩).state, (B.run nb ⟨B.start, t'⟩).tape⟩ := by
  have hInner : (seqComp A B).run (na + 1) ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.natAdd q B.start, t'⟩ := by
    rw [DTM.run_add (seqComp A B) na 1, seqComp_embed_left A B na c hnhA, hA,
      seqComp_switch A B ⟨A.accept, t'⟩ rfl]
    rw [show ((t'.write t'.read).move Dir.stay) = t' from by
      rw [Tape.write_read _ hne, Tape.move]]
  rw [show na + 1 + nb = (na + 1) + nb from by omega,
    DTM.run_add (seqComp A B) (na + 1) nb, hInner]
  exact seqComp_run_natAdd A B nb ⟨B.start, t'⟩

/-! ### 通用不停机工具（自 `MulRound` 上移，供各机器组合复用） -/
/-! ### Generic non-halting tools (moved up from `MulRound` for reuse). -/

/-! ### 通用不停机工具 -/

/-- 若运行途中的状态恒为 `s`（`s` 不是接受/拒绝态），则这段运行不停机。
    If every intermediate state equals a non-terminal state `s`, the run never halts. -/
theorem no_halt_of_state_eq {q : Nat} (M : DTM q) (n : Nat) (c : Config q) (s : Fin q)
    (ha : s ≠ M.accept) (hr : s ≠ M.reject)
    (h : ∀ k, k < n → (M.run k c).state = s) :
    ∀ k, k < n → M.halted (M.run k c) = false := by
  intro k hk
  rw [DTM.halted, h k hk, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr ha, beq_eq_false_iff_ne.mpr hr⟩

/-- 两段各自不停机 ⇒ 拼接后整段不停机。 Concatenation of two non-halting runs. -/
theorem no_halt_add {q : Nat} (M : DTM q) (n1 n2 : Nat) (c : Config q)
    (h1 : ∀ k, k < n1 → M.halted (M.run k c) = false)
    (h2 : ∀ k, k < n2 → M.halted (M.run k (M.run n1 c)) = false) :
    ∀ k, k < n1 + n2 → M.halted (M.run k c) = false := by
  intro k hk
  by_cases hk1 : k < n1
  · exact h1 k hk1
  · have hk2 : k - n1 < n2 := by omega
    rw [show k = n1 + (k - n1) from by omega, DTM.run_add M n1 (k - n1)]
    exact h2 (k - n1) hk2


/-- 一步且起点不停机 ⇒ 这一步内不停机。 A one-step non-halting run. -/
theorem no_halt_one {q : Nat} (M : DTM q) (c : Config q) (h : M.halted c = false) :
    ∀ k, k < 1 → M.halted (M.run k c) = false := by
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simpa [DTM.run] using h

/-- 若一段运行 `n` 步后落在非终止态，则这段运行不停机。
    A run ending in a non-terminal state never halts. -/
theorem no_halt_of_run_end {q : Nat} (M : DTM q) (n : Nat) (c : Config q) (s : Fin q) (t : Tape)
    (h : M.run n c = ⟨s, t⟩) (ha : s ≠ M.accept) (hr : s ≠ M.reject) :
    ∀ k, k < n → M.halted (M.run k c) = false := by
  intro k hk
  refine halted_false_before M n c ?_ ?_ k hk
  · rw [h]; exact ha
  · rw [h]; exact hr


/-! ### 组合机的不停机桥 -/

/-- 组合机在左侧状态上不停机。 -/
theorem seqComp_halted_left {q q' : Nat} (A : DTM q) (B : DTM q') (s : Fin q) (t : Tape) :
    (seqComp A B).halted ⟨Fin.castAdd q' s, t⟩ = false := by
  obtain ⟨h1, h2⟩ := seqComp_halt_castAdd A B s
  rw [DTM.halted, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr (fun he => h1 he.symm),
    beq_eq_false_iff_ne.mpr (fun he => h2 he.symm)⟩

/-- 组合机在 B 段的非终止状态上不停机。 -/
theorem seqComp_halted_right {q q' : Nat} (A : DTM q) (B : DTM q') (s : Fin q')
    (hacc : s ≠ B.accept) (hrej : s ≠ B.reject) (t : Tape) :
    (seqComp A B).halted ⟨Fin.natAdd q s, t⟩ = false := by
  obtain ⟨h1, h2⟩ := seqComp_halt_natAdd A B s hacc hrej
  rw [DTM.halted, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr (fun he => h1 he.symm),
    beq_eq_false_iff_ne.mpr (fun he => h2 he.symm)⟩

/-- **组合机全程不停机**：A 跑到接受态、B 跑完全程，两段各自不停机 ⇒ 组合机不停机。
    A sequential composition never halts when both phases never halt. -/
theorem seqComp_no_halt {q q' : Nat} (A : DTM q) (B : DTM q') (na nb : Nat) (c : Config q)
    (t' : Tape)
    (hA : A.run na c = ⟨A.accept, t'⟩)
    (hne : t'.right ≠ [])
    (hnhA : ∀ k, k < na → A.halted (A.run k c) = false)
    (hnhB : ∀ k, k < nb → B.halted (B.run k ⟨B.start, t'⟩) = false) :
    ∀ k, k < na + 1 + nb →
      (seqComp A B).halted ((seqComp A B).run k ⟨Fin.castAdd q' c.state, c.tape⟩) = false := by
  have hmid : (seqComp A B).run na ⟨Fin.castAdd q' c.state, c.tape⟩
      = ⟨Fin.castAdd q' A.accept, t'⟩ := by
    rw [seqComp_embed_left A B na c hnhA, hA]
  have hsw : (seqComp A B).run 1 (⟨Fin.castAdd q' A.accept, t'⟩ : Config (q + q'))
      = ⟨Fin.natAdd q B.start, t'⟩ := by
    rw [seqComp_switch A B ⟨A.accept, t'⟩ rfl,
      show ((t'.write t'.read).move Dir.stay) = t' from by
        rw [Tape.write_read _ hne, Tape.move]]
  rw [show na + 1 + nb = (na + 1) + nb from by omega]
  refine no_halt_add (seqComp A B) (na + 1) nb _
    (no_halt_add (seqComp A B) na 1 _ ?_ ?_) ?_
  · intro k hk
    rw [seqComp_embed_left A B k c (fun m hm => hnhA m (by omega))]
    exact seqComp_halted_left A B _ _
  · rw [hmid]
    exact no_halt_one (seqComp A B) _ (seqComp_halted_left A B A.accept t')
  · rw [DTM.run_add (seqComp A B) na 1, hmid, hsw]
    intro k hk
    rw [seqComp_embed_right A B k ⟨B.start, t'⟩ (fun m hm => hnhB m (by omega))]
    obtain ⟨hacc, hrej⟩ := by
      simpa [DTM.halted] using hnhB k hk
    exact seqComp_halted_right A B _ hacc hrej _

end DTM

end Pnp
