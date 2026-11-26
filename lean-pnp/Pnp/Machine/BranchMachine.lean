/-
  文件：Pnp/Machine/BranchMachine.lean
  File: Pnp/Machine/BranchMachine.lean

  主题：E 的**逐分支循环体**是一台机器——区域装配段 + 运行相位机串成 `seqComp`。
  Topic: the per-branch loop body of E is a single machine: the region assembly followed by
  the running-phase observer.

  用法：`alignChain_to_initReg` 把输入块写成 `Reg.enc (Reg.initReg …)` 并在右端多留一个空白；
  利用相位吸收（`seqComp_run_absorb`，免右段不停机）把观察机接在后面跑满预算 `K`；
  再用右尾绝缘（`obsPhase_verdict_of_padRight_budget`）把「实际纸带」的判定搬到「理想纸带」。
  Usage: the assembly endpoint is the ideal region encoding plus a far-right tail; the
  observer then runs the whole budget; the verdict on the actual tape equals the verdict on
  the ideal tape (right-tail insulation).

  前提 `hb` 只要求理想纸带右侧长度覆盖预算加一（E 取指数副垫时成立）。
  Premise `hb` just asks the ideal right side to cover the budget (holds with exponential pad).
-/

import Pnp.Machine.AlignChain
import Pnp.Machine.BranchEntry
import Pnp.Machine.BranchPad

namespace Pnp

namespace DTM

/-- **逐分支判定机（装配 + 观察 → 判定搬运）**：整机从装配段的初始纸带出发跑
    「装配段步数 + 1 + 预算 `K`」步后停在接受态，当且仅当观察机在**理想纸带**
    `Reg.enc (Reg.initReg st w (T+1) (T+1)) L` 上跑 `K` 步后停在接受态。
    The per-branch machine accepts at the end of its run iff the observer accepts within the
    budget on the ideal region tape. -/
theorem branchMachine_accept_iff {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (T b K : Nat) (L R : List Sym) (M : NTM q)
    (hb : K + 1 ≤ (Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right.length) :
    ((seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)) + 1 + K)
      ⟨(seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr T).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept
      ↔ ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  -- 装配段的运行与不停机
  have hA := alignChain_to_initReg st w a l' hw hl T L R
  have hnh := alignChain_halted_false (padStr T) (3 * (T + 1) + 3 * l'.length + 1)
    (a :: l') hl (padStr T ++ L) R
  -- 装配段终点纸带（实际纸带）：理想区域编码 + 右尾 `none :: R`
  have hne : (Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
      ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R)).right ≠ [] := by
    simp
  -- 相位吸收：整机 = 观察机在实际纸带上跑 `K` 步（右段停机即冻结，无需不停机前提）
  have hrun := seqComp_run_absorb
    (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
    (obsPhase q b ((M.stutter).haltNorm))
    (expandCost (a :: l') + 1
      + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)))
    K
    ⟨(alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).start,
      Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
        ++ (List.replicate (padStr T).length none ++ R))⟩
    (Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
      ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R))
    hA hne hnh
  -- 右尾绝缘：实际纸带与理想纸带的判定相同（预算覆盖版）
  have hver := obsPhase_verdict_of_padRight_budget q b ((M.stutter).haltNorm) K
    ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
      Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L⟩
    (Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
      ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R))
    (enc_padRight_append (Reg.initReg st w (T + 1) (T + 1)) L R) hb
  -- 把整机的终点状态换成「观察机实际纸带的终点状态」（`natAdd` 形态）
  have hgoal : ((seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)) + 1 + K)
      ⟨(seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr T).length none ++ R))⟩).state
      = Fin.natAdd (128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
          ((obsPhase q b ((M.stutter).haltNorm)).run K
            ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
              Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
                ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R)⟩).state := by
    rw [show (⟨(seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
            ++ (List.replicate (padStr T).length none ++ R))⟩
        : Config ((128 + ((padStr T).length + 1
              + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
            + (stateCountO q b + 1)))
      = ⟨Fin.castAdd (stateCountO q b + 1)
          (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).start,
          Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
            ++ (List.replicate (padStr T).length none ++ R))⟩ from rfl]
    exact congrArg Config.state hrun
  rw [hgoal]
  -- 状态：组合机的接受态也是 `natAdd` 形态，判定归结为观察机自己的接受态
  constructor
  · intro h
    -- 组合机接受态 = `natAdd` 形态
    have h2 : Fin.natAdd (128 + ((padStr T).length + 1
          + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
        ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
              ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R)⟩).state
        = Fin.natAdd (128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
          (obsPhase q b ((M.stutter).haltNorm)).accept := h
    exact hver.mpr (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h2)))
  · intro h
    have h2 : Fin.natAdd (128 + ((padStr T).length + 1
          + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
        ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
              ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R)⟩).state
        = Fin.natAdd (128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
          (obsPhase q b ((M.stutter).haltNorm)).accept := by
      exact Fin.ext (congrArg (fun v => 128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)) + v)
        (congrArg Fin.val (hver.mp h)))
    exact h2

/-- **逐分支判定机（副垫参数化）**：与 `branchMachine_accept_iff` 同结论，副垫空白格数
    取任意 `m ≥ 1`（代换 `T := m - 1`）。E 取 `m ≈ |branchBlocks|·costCap`（多项式）时，
    右尾长度足以覆盖固定预算 `K`。
    The per-branch machine with a free pad size `m`; the right-tail condition then holds for
    polynomial budgets. -/
theorem branchMachine_accept_iff_pad {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (m : Nat) (hm : 1 ≤ m) (b K : Nat) (L R : List Sym) (M : NTM q)
    (hb : K + 1 ≤ (Reg.enc (Reg.initReg st w m m) L).right.length) :
    ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1 + K)
      ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr (m - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept
      ↔ ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Reg.enc (Reg.initReg st w m m) L⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  have hs : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [← hs] at hb
  have h := branchMachine_accept_iff st w a l' hw hl (m - 1) b K L R M hb
  rw [hs] at h
  exact h


set_option maxHeartbeats 2000000 in
/-- **逐分支判定机（完备性，副垫 `m` 参数化）**：原机在 `T` 步内接受 ⇒ 存在分支 `(t, i)`，
    使「装配 + 观察」整机在装配步数 + 1 + 该分支固定预算内停在接受态。
    预算 `roundCostStay x Z (i % B) x.cur + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b` 来自 #258。
    Machine-level per-branch completeness: acceptance of `M` yields a branch whose assembled
    machine accepts within the fixed per-branch budget of #258. -/
theorem branchMachine_dummy_complete {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hB : ∀ s x', (M.step s x').length ≤ B) (hBpos : 0 < B)
    (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T) (Z m : Nat) (hm : 1 ≤ m)
    (hZT : Z ≤ T + 1) (R : List Sym)
    (hd1 : T ≤ m)
    (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject)
    (hpad : roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w m m).post.length + 1)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w m m) Z (i % B)
                (Reg.initReg M.start w m m).cur
              + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b))
        ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr (m - 1) ++ (none :: List.replicate Z (some false)
              ++ digitArea (i % B :: branchBlocks B t i)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept := by
  -- 初始区域的性质
  have hxM : (Reg.initReg M.start w m m).MarkersOK := Reg.initReg_markersOK M.start w m m
  have hxw : CfgEquiv (Reg.initReg M.start w m m).toConfig (M.init w) :=
    Reg.initReg_cfgEquiv M w m m
  have hd1' : T ≤ (Reg.initReg M.start w m m).pre.length := by
    rw [Reg.initReg_pre_length]; exact hd1
  have hd2' : T ≤ (Reg.initReg M.start w m m).post.length := by
    rw [Reg.initReg_post_length]; omega
  -- 完备性（#258）
  obtain ⟨t, i, ht1, htT, hi, hhit⟩ :=
    exists_branch_dummy_hit_uniform M hB hBpos w T b hbnd hT Z (Reg.initReg M.start w m m)
      hxM hxw hd1' hd2' hxacc hxre rfl hZT hacc
  refine ⟨t, i, ht1, htT, hi, ?_⟩
  -- 命中 ⇒ 运行相位机在预算末态接受
  have hK : ((obsPhase q b ((M.stutter).haltNorm)).run
      (roundCostStay (Reg.initReg M.start w m m) Z (i % B) (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b)
      ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
        Reg.enc (Reg.initReg M.start w m m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).state
      = (obsPhase q b ((M.stutter).haltNorm)).accept := by
    rw [show (obsPhase q b ((M.stutter).haltNorm)).start
          = embOb q b (simObs q b ((M.stutter).haltNorm)).start from rfl]
    exact (obsPhase_accept_iff q b ((M.stutter).haltNorm)
      (roundCostStay (Reg.initReg M.start w m m) Z (i % B) (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b)
      ⟨(simObs q b ((M.stutter).haltNorm)).start,
        Reg.enc (Reg.initReg M.start w m m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).mpr hhit
  -- 机器层判据
  have hbK : roundCostStay (Reg.initReg M.start w m m) Z (i % B)
        (Reg.initReg M.start w m m).cur + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b + 1
      ≤ (Reg.enc (Reg.initReg M.start w m m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))).right.length := by
    rw [Reg.enc_right_length]
    -- `rc_i ≤ rc_B`，再与 `hpad` 串接
    have hrc : roundCostStay (Reg.initReg M.start w m m) Z (i % B)
          (Reg.initReg M.start w m m).cur
        ≤ roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur :=
      roundCostStay_mono _ _ _ _ _ _ (Nat.le_refl _) (Nat.le_of_lt (Nat.mod_lt i hBpos))
    exact Nat.le_trans
      (Nat.add_le_add_right (Nat.add_le_add_right hrc
        (branchBudget (Reg.initReg M.start w m m).pre.length Z T B b)) 1) hpad
  exact (branchMachine_accept_iff_pad M.start w a l' hw hl m hm b
    (roundCostStay (Reg.initReg M.start w m m) Z (i % B) (Reg.initReg M.start w m m).cur
      + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b)
    (none :: List.replicate Z (some false) ++ digitArea (i % B :: branchBlocks B t i))
    R M hbK).mpr hK


set_option maxHeartbeats 2000000 in
/-- **逐分支判定机（可靠性，副垫 `m` 参数化）**：装配 + 观察的整机在该分支预算内接受
    ⇒ 原机在 `T` 步内接受。证法：`branchMachine_accept_iff_pad`（机器层 → 运行相位机）→
    `obsPhase_accept_iff`（→ 观察机命中）→ `acceptsWithin_of_dummy_branch_acc_budget`
    （任意预算可靠性，`K = 总预算 - 单轮成本`）。
    Machine-level per-branch soundness: acceptance of the assembled machine implies
    `M.AcceptsWithin w T`. -/
theorem branchMachine_dummy_sound {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hBpos : 0 < B)
    (hlB : ∀ m a', ((M.stutter).step m a').length ≤ B + 1)
    (T b t i : Nat) (hT : 0 < T) (hbnd : B + 2 < 2 ^ b)
    (Z m : Nat) (hm : 1 ≤ m) (hZT : Z ≤ T + 1) (R : List Sym)
    (hd1 : T ≤ m)
    (hk1 : i % B + 1 < 2 ^ b) (hk2 : i % B + 2 < 2 ^ b)
    (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject)
    (hpadpost : (branchBlocks B T i).length + 1
      ≤ (Reg.initReg M.start w m m).post.length)
    (hpadpre : (branchBlocks B T i).length + 1
      ≤ (Reg.initReg M.start w m m).pre.length)
    (hlen : (branchBlocks B T i).length ≤ T)
    (hpad : roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w m m).post.length + 1)
    (hAcc : ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
        + (roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
            + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b))
      ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr (m - 1) ++ (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B T i)))
          ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
            ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept) :
    M.AcceptsWithin w T := by
  have hxM : (Reg.initReg M.start w m m).MarkersOK := Reg.initReg_markersOK M.start w m m
  have hxw : CfgEquiv (Reg.initReg M.start w m m).toConfig (M.init w) :=
    Reg.initReg_cfgEquiv M w m m
  -- 机器层 → 运行相位机（预算 `rc_B + branchBudget`）
  have hbK : roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
        + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b + 1
      ≤ (Reg.enc (Reg.initReg M.start w m m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B T i))).right.length := by
    rw [Reg.enc_right_length]; exact hpad
  have hob := (branchMachine_accept_iff_pad M.start w a l' hw hl m hm b
    (roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
      + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b)
    (none :: List.replicate Z (some false) ++ digitArea (i % B :: branchBlocks B T i))
    R M hbK).mp hAcc
  -- 运行相位机 → 观察机命中（同一预算）
  have hhit := (obsPhase_accept_iff q b ((M.stutter).haltNorm)
    (roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
      + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b)
    ⟨(simObs q b ((M.stutter).haltNorm)).start,
      Reg.enc (Reg.initReg M.start w m m)
        (none :: List.replicate Z (some false)
          ++ digitArea (i % B :: branchBlocks B T i))⟩).mp hob
  -- 把预算拆成 `rc_i + K`，交给任意预算可靠性
  have hrc : roundCostStay (Reg.initReg M.start w m m) Z (i % B)
      (Reg.initReg M.start w m m).cur
    ≤ roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur :=
    roundCostStay_mono _ _ _ _ _ _ (Nat.le_refl _) (Nat.le_of_lt (Nat.mod_lt i hBpos))
  refine acceptsWithin_of_dummy_branch_acc_budget q b B T i T M w hBpos hbnd hlB Z
    (Reg.initReg M.start w m m) hxM hxw hpadpost hpadpre hlen (by omega) hk1 hk2
    rfl hxacc hxre
    (roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
      + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b
      - roundCostStay (Reg.initReg M.start w m m) Z (i % B) (Reg.initReg M.start w m m).cur)
    ?_ ?_
  · -- `hK`：前缀通路步数落在 `总预算 - rc_i` 内
    intro L1 hb1 r1 hle1 hp1
    have h1 := passRun_steps_le_uniform q b ((M.stutter).haltNorm).step
      (Z + i % B + 3) (i % B + 1) hk1
      (Reg.initReg M.start w m m) L1 hb1 r1 hp1 T hle1
    have hmod : i % B < B := Nat.mod_lt i hBpos
    have h2 : costCap (Reg.initReg M.start w m m).pre.length (Z + (i % B + 3)) T (2 ^ b)
        = costCap (Reg.initReg M.start w m m).pre.length Z T (2 ^ b) + 2 * (i % B + 3) :=
      costCap_Z_shift _ _ _ _ _
    rw [show Z + i % B + 3 = Z + (i % B + 3) from by omega, h2] at h1
    have hmul : T * (costCap (Reg.initReg M.start w m m).pre.length Z T (2 ^ b)
          + 2 * (i % B + 3))
        ≤ T * costCap (Reg.initReg M.start w m m).pre.length Z T (2 ^ b)
          + 2 * (B + 3) * (T + 1) := by
      rw [Nat.mul_add]
      have hle : T * (2 * (i % B + 3)) ≤ 2 * (B + 3) * (T + 1) := by
        rw [show T * (2 * (i % B + 3)) = 2 * (i % B + 3) * T from Nat.mul_comm _ _]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
      omega
    have hBB : r1.steps + 6 ≤ branchBudget (Reg.initReg M.start w m m).pre.length Z T B b := by
      unfold branchBudget
      omega
    -- `branchBudget ≤ 总预算 - rc_i`
    have hle2 : branchBudget (Reg.initReg M.start w m m).pre.length Z T B b
        ≤ roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
          + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b
          - roundCostStay (Reg.initReg M.start w m m) Z (i % B) (Reg.initReg M.start w m m).cur := by
      omega
    exact Nat.le_trans hBB hle2
  · -- 命中时刻：`run (rc_i + K) = run 总预算`
    rw [show roundCostStay (Reg.initReg M.start w m m) Z (i % B) (Reg.initReg M.start w m m).cur
          + (roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
            + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b
            - roundCostStay (Reg.initReg M.start w m m) Z (i % B)
                (Reg.initReg M.start w m m).cur)
        = roundCostStay (Reg.initReg M.start w m m) Z B (Reg.initReg M.start w m m).cur
          + branchBudget (Reg.initReg M.start w m m).pre.length Z T B b from by omega]
    exact hhit


end DTM

end Pnp
