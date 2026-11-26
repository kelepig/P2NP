/-
  文件：Pnp/Machine/BranchPad.lean
  主题：把**带右侧预留的初始区域**代入分支族完备性引理，得到 E 机可直接引用的形态。

  背景：E 的区域取 `Reg.initReg M.start w (T+1) kr`——左侧 `T+1` 个空白格（覆盖 `t ≤ T`
  的左移），右侧 `kr` 个空白格（覆盖 `T` 步的右移，并在 #234 的意义下给出右尾绝缘。
  本文件把 `BranchPhase` 的 `(t,i)` 分支完备性在 `x = initReg ...` 上实例化，前提只剩
  「`kr ≥ T`」「`Z ≤ T+1`」与「起始态不是接受态」（`M.start ≠ M.accept`；该退化情形在
  `InExp` 层单列：起始即接受则语言为全集，平凡属 EXP）。

  Instantiating the branch-family completeness at the padded initial region, so that E can
  quote it directly.
-/

import Pnp.Machine.BranchPhase
import Pnp.Machine.RightPad

namespace Pnp

namespace DTM

variable {q : Nat}

namespace Reg

/-- 初始区域左侧格数 = `kl`。 The initial region has exactly `kl` cells on the left. -/
theorem initReg_pre_length (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (initReg st w kl kr).pre.length = kl := by
  simp [initReg]

/-- 初始区域右侧格数 = 输入剩余格数 + `kr`。
    The initial region has the remaining input cells plus `kr` cells on the right. -/
theorem initReg_post_length (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (initReg st w kl kr).post.length = ((w.map some).drop 1).length + kr := by
  simp [initReg, List.length_append]

/-- 右侧预留 `kr` 格时，右侧格数至少是 `kr`。 The right side has at least `kr` cells. -/
theorem initReg_post_ge (st : Fin q) (w : List Bool) (kl kr : Nat) :
    kr ≤ (initReg st w kl kr).post.length := by
  rw [initReg_post_length]
  omega

/-- 初始区域的 `toConfig` 与 `M.init w` 是语义等价格局（任意预留都成立）。
    The padded initial region is semantically equivalent to `M.init w`, for any padding. -/
theorem initReg_cfgEquiv (M : NTM q) (w : List Bool) (kl kr : Nat) :
    CfgEquiv (initReg M.start w kl kr).toConfig (M.init w) :=
  ⟨rfl, Or.inl (initReg_sameInf M.start w kl kr)⟩

end Reg

/-- **分支族完备性（带预留初始区域版）**：`M` 在 `T` 步内接受 ⇒ 存在 `t ≤ T`、`i < B^T`，
    使该分支的运行相位机在统一指数预算内停在接受态。区域取
    `Reg.initReg M.start w (T+1) kr`（左侧 `T+1` 格、右侧 `kr ≥ T` 格）。
    Family completeness at the padded initial region: the hypotheses reduce to `kr ≥ T`,
    `Z ≤ T + 1` and `M.start ≠ M.accept`. -/
theorem exists_branch_obsPhase_accept_of_acceptsWithin_initReg {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (hZ : Z ≤ T + 1) (kr : Nat) (hkr : T ≤ kr)
    (hstart : M.start ≠ M.accept) (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (2 ^ ((2 * 2 ^ b + 42) * (T + 1)))
        ⟨embOb q b (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  refine exists_branch_obsPhase_accept_two_pow_of_acceptsWithin M hB hBpos w T b hbnd hT Z
    (Reg.initReg M.start w (T + 1) kr) (Reg.initReg_markersOK M.start w (T + 1) kr)
    (Reg.initReg_cfgEquiv M w (T + 1) kr) ?_ ?_ hstart ?_ hZ hacc
  · rw [Reg.initReg_pre_length]; omega
  · have := Reg.initReg_post_ge M.start w (T + 1) kr
    omega
  · rw [Reg.initReg_pre_length]
    exact Nat.le_refl _

/-- **接受命中的停机时刻**：观察机在第 `n` 步停在接受哨兵 ⇒ 运行相位机在第 `n` 步已停机
    （接受态）。E 逐分支读判据时用它给出冻结时刻。
    A hit at step `n` means the run phase has halted (accept) by `n`. -/
theorem obsPhase_halted_of_simObs_acc (q b : Nat) (M : NTM q) (n : Nat)
    (c : Config (stateCountO q b))
    (h : ((simObs q b M).run n c).state = obsAcc q b) :
    (obsPhase q b M).halted
      ((obsPhase q b M).run n ⟨embOb q b c.state, c.tape⟩) = true := by
  have hacc : ((obsPhase q b M).run n ⟨embOb q b c.state, c.tape⟩).state
      = (obsPhase q b M).accept := (obsPhase_accept_iff q b M n c).mpr h
  exact halted_of_accept_or_reject (obsPhase q b M) _ (Or.inl hacc)

/-- **失败命中的停机时刻**：观察机在第 `n` 步停在失败哨兵 ⇒ 运行相位机在第 `n+1` 步已停机
    （逃逸态）。 The fail endpoint is likewise halting one step later. -/
theorem obsPhase_halted_of_simObs_fail (q b : Nat) (M : NTM q) (n : Nat)
    (c : Config (stateCountO q b))
    (h : ((simObs q b M).run n c).state = obsFail q b) :
    (obsPhase q b M).halted
      ((obsPhase q b M).run (n + 1) ⟨embOb q b c.state, c.tape⟩) = true := by
  have hesc := obsPhase_esc_of_simObs_fail q b M n c h
  exact halted_of_accept_or_reject (obsPhase q b M) _ (Or.inr hesc)

/-- **命中 + 右尾 ⇒ 判定搬运（通用胶水）**：观察机在第 `n` 步命中接受哨兵，且实际纸带是
    理想纸带加远端右尾（`PadRight`），右侧非空覆盖到 `n` ⇒ 任意预算 `K ≥ n` 下运行相位机的
    接受判定相同。 E 机逐分支把判据从理想纸带搬到带副本的实际纸带时直接调用。
    Once the observer hits accept at step `n`, a far-right tail (covered up to `n`) does not
    change the phase machine's verdict at any larger budget. -/
theorem obsPhase_verdict_of_hit_padRight (q b : Nat) (M : NTM q) (n K : Nat) (hn : n ≤ K)
    (c : Config (stateCountO q b)) (t : Tape)
    (hP : Tape.PadRight c.tape t) (hr : n + 1 ≤ c.tape.right.length)
    (hhit : ((simObs q b M).run n c).state = obsAcc q b) :
    ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state
        = (obsPhase q b M).accept ↔
      ((obsPhase q b M).run K ⟨embOb q b c.state, t⟩).state
        = (obsPhase q b M).accept := by
  have hhalt := obsPhase_halted_of_simObs_acc q b M n c hhit
  refine run_accept_eq_of_halted_at (obsPhase q b M) n K hn _ _ ?_ hhalt
  exact run_state_eq_of_padRight (obsPhase q b M) n _ _ rfl hP
    (right_safe_of_len (obsPhase q b M) n _ (by omega))

/-- 上面引理的「在右端追加副本」形态。 The append form of the same transfer. -/
theorem obsPhase_verdict_of_hit_append (q b : Nat) (M : NTM q) (n K : Nat) (hn : n ≤ K)
    (c : Config (stateCountO q b)) (copy : List Sym) (hr : n + 1 ≤ c.tape.right.length)
    (hhit : ((simObs q b M).run n c).state = obsAcc q b) :
    ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state
        = (obsPhase q b M).accept ↔
      ((obsPhase q b M).run K
        ⟨embOb q b c.state, ⟨c.tape.left, c.tape.right ++ copy⟩⟩).state
        = (obsPhase q b M).accept :=
  obsPhase_verdict_of_hit_padRight q b M n K hn c _ (Tape.padRight_of_append c.tape copy)
    hr hhit

/-- **逐分支实际判据（E 机直接接口）**：`M` 在 `T` 步内接受 ⇒ 存在分支 `(t,i)` 与命中时刻
    `n`（`n ≤ T'·costCap+6`），使运行相位机在统一预算 `K` 处**对理想纸带与带右端副本的
    实际纸带同时接受**。前提 `hpad` 只要求区域右侧预留覆盖预算加一（多项式）。
    Per-branch verdict at the E interface: some branch and hit time make the phase machine
    accept at the uniform budget, on both the ideal tape and the actual tape carrying a
    right-end copy, provided the right padding covers the budget. -/
theorem exists_branch_obsPhase_verdict_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (T' : Nat) (hTT : T ≤ T')
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hpad : T' * costCap x.pre.length Z T' (2 ^ b) + 7 ≤ 3 * x.post.length + 1)
    (copy : List Sym) (hacc : M.AcceptsWithin w T) :
    ∃ (t i n : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      n ≤ T' * costCap x.pre.length Z T' (2 ^ b) + 6 ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
        ⟨embOb q b (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
        ⟨embOb q b (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         ⟨(obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
            (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape.left,
          (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
            (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape.right ++ copy⟩⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  obtain ⟨t, i, n, ht1, htT, hi, hn, hhit⟩ :=
    exists_branch_hit_time_of_acceptsWithin M hB hBpos w T b hbnd hT T' hTT Z x hx hxw
      hd1 hd2 hxacc hacc
  -- 统一预算与命中时刻的关系
  have hnK : n ≤ T' * costCap x.pre.length Z T' (2 ^ b) + 6 := hn
  -- 观察机在预算 `K` 处仍为接受态（`obsPhase` 接受后保持）
  have haccIdeal :
      ((obsPhase q b ((M.stutter).haltNorm)).run (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
        ⟨embOb q b (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept :=
    obsPhase_accept_mono q b ((M.stutter).haltNorm) n
      (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
      (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
        (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i))
      hnK ((obsPhase_accept_iff q b _ n _).mpr hhit)
  -- 右长：理想纸带右侧长 `3|post|+1`，`hpad` 给出覆盖到命中时刻
  have hlen : n + 1 ≤ (obsStart q b (M.stutter) x x.state.val (seqHead B T i) Z x.state.isLt
      (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape.right.length := by
    show n + 1 ≤ (Reg.enc x (none :: List.replicate Z (some false) ++ digitArea _)).right.length
    rw [Reg.enc_right_length]
    omega
  exact ⟨t, i, n, ht1, htT, hi, hn, haccIdeal,
    (obsPhase_verdict_of_hit_append q b _ n _ hnK _ copy hlen hhit).mp haccIdeal⟩

/-- **逐分支实际判据（带预留初始区域版）**：E 机的直接接口。区域取
    `Reg.initReg M.start w (T+1) kr`，右侧预留 `kr` 只需覆盖预算（多项式），
    前提即 `kr ≥ T'·costCap+7`。
    The padded-initial-region form of the per-branch verdict, i.e. E's direct interface. -/
theorem exists_branch_obsPhase_verdict_of_acceptsWithin_initReg {q : Nat} (M : NTM q)
    {B : Nat} (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (T' : Nat) (hTT : T ≤ T') (Z : Nat) (hZ : Z ≤ T + 1)
    (kr : Nat) (hkr : T ≤ kr)
    (hkr2 : T' * costCap (T + 1) Z T' (2 ^ b) + 7 ≤ kr)
    (hstart : M.start ≠ M.accept) (copy : List Sym) (hacc : M.AcceptsWithin w T) :
    ∃ (t i n : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      n ≤ T' * costCap (T + 1) Z T' (2 ^ b) + 6 ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (T' * costCap (T + 1) Z T' (2 ^ b) + 6)
        ⟨embOb q b (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept ∧
      ((obsPhase q b ((M.stutter).haltNorm)).run
        (T' * costCap (T + 1) Z T' (2 ^ b) + 6)
        ⟨embOb q b (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
          (seqHead B T i) Z M.start.isLt
          (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).state,
         ⟨(obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
            (seqHead B T i) Z M.start.isLt
            (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape.left,
          (obsStart q b (M.stutter) (Reg.initReg M.start w (T + 1) kr) M.start.val
            (seqHead B T i) Z M.start.isLt
            (seqHead_lt_pow B t i b hBpos hbnd) (branchBlocks B t i)).tape.right ++ copy⟩⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  have h := exists_branch_obsPhase_verdict_of_acceptsWithin M hB hBpos w T b hbnd hT T' hTT Z
    (Reg.initReg M.start w (T + 1) kr) (Reg.initReg_markersOK M.start w (T + 1) kr)
    (Reg.initReg_cfgEquiv M w (T + 1) kr)
    (by rw [Reg.initReg_pre_length]; omega)
    (by have := Reg.initReg_post_ge M.start w (T + 1) kr; omega)
    hstart
    (by
      rw [Reg.initReg_pre_length, Reg.initReg_post_length]
      omega)
    copy hacc
  simpa [Reg.initReg] using h

end DTM

end Pnp
