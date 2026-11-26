/-
  文件：Pnp/Machine/BranchMachineTwo.lean
  File: Pnp/Machine/BranchMachineTwo.lean

  主题：**左右副垫解耦**的逐分支判定机——左垫固定 `T+1`、右垫 `m` 可放大，
        区域为 `Reg.initReg st w (T+1) m`。
  Topic: per-branch machine with decoupled pads (left fixed at `T+1`, right pad `m`).

  缘由（#265 缺陷修复）：原机器层定理的右预留前提 `hpad` 在「左右垫同取 `m`」时
  强迫 `|输入| = Ω(T²)`，与 `T = |w|^k + k` 冲突 ⇒ 空真。解耦后 `hpad` 只需
  `3m ≥ 预算 + 6(T+1)(T+1) ≈ poly(T)`，取 `m ≈ 预算/3` 即可。
  Reason: the old right-pad premise was unsatisfiable in the target regime; decoupling
  reduces it to a polynomial bound on `m`.
-/

import Pnp.Machine.BranchMachine
import Pnp.Machine.PadConflict
import Pnp.Machine.BranchIndex
import Pnp.Machine.AlignChainTwo

namespace Pnp

namespace DTM

/-- **逐分支判定机（左右副垫解耦）**：左垫 `padStr (Pl-1)` 留在初始纸带上下文，右垫 `padStr T`
    由装配段写出；整机接受 ⇔ 观察机在理想纸带 `Reg.enc (Reg.initReg st w Pl (T+1)) L` 上接受。
    Per-branch machine with decoupled pads. -/
theorem branchMachine_accept_iff_two {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (Pl T b K : Nat) (hPl : 1 ≤ Pl) (L R : List Sym) (M : NTM q)
    (hb : K + 1 ≤ (Reg.enc (Reg.initReg st w Pl (T + 1)) L).right.length) :
    ((seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)) + 1 + K)
      ⟨(seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr (Pl - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr T).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept
      ↔ ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Reg.enc (Reg.initReg st w Pl (T + 1)) L⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  -- 装配段的运行与不停机
  have hA := alignChain_to_initReg_two st w a l' hw hl Pl T hPl L R
  have hnh := alignChain_halted_false (padStr T) (3 * (T + 1) + 3 * l'.length + 1)
    (a :: l') hl (padStr (Pl - 1) ++ L) R
  -- 装配段终点纸带（实际纸带）：理想区域编码 + 右尾 `none :: R`
  have hne : (Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
      ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R)).right ≠ [] := by
    simp
  -- 相位吸收：整机 = 观察机在实际纸带上跑 `K` 步（右段停机即冻结，无需不停机前提）
  have hrun := seqComp_run_absorb
    (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
    (obsPhase q b ((M.stutter).haltNorm))
    (expandCost (a :: l') + 1
      + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)))
    K
    ⟨(alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).start,
      Tape.mk (padStr (Pl - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
        ++ (List.replicate (padStr T).length none ++ R))⟩
    (Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
      ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R))
    hA hne hnh
  -- 右尾绝缘：实际纸带与理想纸带的判定相同（预算覆盖版）
  have hver := obsPhase_verdict_of_padRight_budget q b ((M.stutter).haltNorm) K
    ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
      Reg.enc (Reg.initReg st w Pl (T + 1)) L⟩
    (Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
      ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R))
    (enc_padRight_append (Reg.initReg st w Pl (T + 1)) L R) hb
  -- 把整机的终点状态换成「观察机实际纸带的终点状态」（`natAdd` 形态）
  have hgoal : ((seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)) + 1 + K)
      ⟨(seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr (Pl - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr T).length none ++ R))⟩).state
      = Fin.natAdd (128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
          ((obsPhase q b ((M.stutter).haltNorm)).run K
            ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
              Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
                ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R)⟩).state := by
    rw [show (⟨(seqComp (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr (Pl - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
            ++ (List.replicate (padStr T).length none ++ R))⟩
        : Config ((128 + ((padStr T).length + 1
              + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
            + (stateCountO q b + 1)))
      = ⟨Fin.castAdd (stateCountO q b + 1)
          (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).start,
          Tape.mk (padStr (Pl - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
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
            Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
              ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R)⟩).state
        = Fin.natAdd (128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
          (obsPhase q b ((M.stutter).haltNorm)).accept := h
    exact hver.mpr (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h2)))
  · intro h
    have h2 : Fin.natAdd (128 + ((padStr T).length + 1
          + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
        ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
              ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R)⟩).state
        = Fin.natAdd (128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)))
          (obsPhase q b ((M.stutter).haltNorm)).accept := by
      exact Fin.ext (congrArg (fun v => 128 + ((padStr T).length + 1
            + ((3 * (T + 1) + 3 * l'.length + 1) + 1 + 2)) + v)
        (congrArg Fin.val (hver.mp h)))
    exact h2


/-- **解耦版（右垫 `m` 参数化）**：左垫固定 `T+1`、右垫 `m`，区域为
    `Reg.initReg st w (T+1) m`。E 的逐分支循环体直接用这一形态。
    Decoupled form with right pad `m` and left pad fixed at `T+1`. -/
theorem branchMachine_accept_iff_two_pad {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (T m b K : Nat) (hT : 0 < T) (hm : 1 ≤ m) (L R : List Sym) (M : NTM q)
    (hb : K + 1 ≤ (Reg.enc (Reg.initReg st w (T + 1) m) L).right.length) :
    ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1 + K)
      ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept
      ↔ ((obsPhase q b ((M.stutter).haltNorm)).run K
          ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
            Reg.enc (Reg.initReg st w (T + 1) m) L⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  have h1 : (T + 1) - 1 = T := by omega
  have h2 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hb' : K + 1 ≤ (Reg.enc (Reg.initReg st w (T + 1) ((m - 1) + 1)) L).right.length := by
    rw [h2]; exact hb
  have h := branchMachine_accept_iff_two st w a l' hw hl (T + 1) (m - 1) b K
    (by omega) L R M hb'
  rw [h1, h2] at h
  exact h

/-- **逐分支判定机（完备性，副垫 `m` 参数化）**：原机在 `T` 步内接受 ⇒ 存在分支 `(t, i)`，
    使「装配 + 观察」整机在装配步数 + 1 + 该分支固定预算内停在接受态。
    预算 `roundCostStay x Z (i % B) x.cur + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b` 来自 #258。
    Machine-level per-branch completeness: acceptance of `M` yields a branch whose assembled
    machine accepts within the fixed per-branch budget of #258. -/
theorem branchMachine_dummy_complete_two {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hB : ∀ s x', (M.step s x').length ≤ B) (hBpos : 0 < B)
    (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T) (Z m : Nat) (hm : 1 ≤ m)
    (hZT : Z ≤ T + 1) (R : List Sym)
    (hd1 : T ≤ m)
    (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject)
    (hpad : roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w (T + 1) m).post.length + 1)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
                (Reg.initReg M.start w (T + 1) m).cur
              + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b))
        ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea (i % B :: branchBlocks B t i)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept := by
  -- 初始区域的性质
  have hxM : (Reg.initReg M.start w (T + 1) m).MarkersOK := Reg.initReg_markersOK M.start w (T + 1) m
  have hxw : CfgEquiv (Reg.initReg M.start w (T + 1) m).toConfig (M.init w) :=
    Reg.initReg_cfgEquiv M w (T + 1) m
  have hd1' : T ≤ (Reg.initReg M.start w (T + 1) m).pre.length := by
    rw [Reg.initReg_pre_length]; omega
  have hd2' : T ≤ (Reg.initReg M.start w (T + 1) m).post.length := by
    rw [Reg.initReg_post_length]; omega
  -- 完备性（#258）
  obtain ⟨t, i, ht1, htT, hi, hhit⟩ :=
    exists_branch_dummy_hit_uniform M hB hBpos w T b hbnd hT Z (Reg.initReg M.start w (T + 1) m)
      hxM hxw hd1' hd2' hxacc hxre rfl hZT hacc
  refine ⟨t, i, ht1, htT, hi, ?_⟩
  -- 命中 ⇒ 运行相位机在预算末态接受
  have hK : ((obsPhase q b ((M.stutter).haltNorm)).run
      (roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B) (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)
      ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
        Reg.enc (Reg.initReg M.start w (T + 1) m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).state
      = (obsPhase q b ((M.stutter).haltNorm)).accept := by
    rw [show (obsPhase q b ((M.stutter).haltNorm)).start
          = embOb q b (simObs q b ((M.stutter).haltNorm)).start from rfl]
    exact (obsPhase_accept_iff q b ((M.stutter).haltNorm)
      (roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B) (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)
      ⟨(simObs q b ((M.stutter).haltNorm)).start,
        Reg.enc (Reg.initReg M.start w (T + 1) m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).mpr hhit
  -- 机器层判据
  have hbK : roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
        (Reg.initReg M.start w (T + 1) m).cur + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b + 1
      ≤ (Reg.enc (Reg.initReg M.start w (T + 1) m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))).right.length := by
    rw [Reg.enc_right_length]
    -- `rc_i ≤ rc_B`，再与 `hpad` 串接
    have hrc : roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
          (Reg.initReg M.start w (T + 1) m).cur
        ≤ roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur :=
      roundCostStay_mono _ _ _ _ _ _ (Nat.le_refl _) (Nat.le_of_lt (Nat.mod_lt i hBpos))
    exact Nat.le_trans
      (Nat.add_le_add_right (Nat.add_le_add_right hrc
        (branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)) 1) hpad
  exact (branchMachine_accept_iff_two_pad M.start w a l' hw hl T m b
    (roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B) (Reg.initReg M.start w (T + 1) m).cur
      + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)
    hT hm
    (none :: List.replicate Z (some false) ++ digitArea (i % B :: branchBlocks B t i))
    R M hbK).mpr hK


set_option maxHeartbeats 2000000 in

/-- **可靠性（解耦副垫）**：整机在该分支预算内接受 ⇒ 原机 `T` 步内接受。
    Soundness with decoupled pads. -/
theorem branchMachine_dummy_sound_two {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hBpos : 0 < B)
    (hlB : ∀ m a', ((M.stutter).step m a').length ≤ B + 1)
    (T b t i : Nat) (hT : 0 < T) (ht1 : 1 ≤ t) (_htT : t ≤ T) (hbnd : B + 2 < 2 ^ b)
    (Z m : Nat) (hm : 1 ≤ m) (_hZT : Z ≤ T + 1) (R : List Sym)
    (_hd1 : T ≤ m)
    (hk1 : i % B + 1 < 2 ^ b) (hk2 : i % B + 2 < 2 ^ b)
    (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject)
    (hpadpost : (branchBlocks B t i).length + 1
      ≤ (Reg.initReg M.start w (T + 1) m).post.length)
    (hpadpre : (branchBlocks B t i).length + 1
      ≤ (Reg.initReg M.start w (T + 1) m).pre.length)
    (hlen : (branchBlocks B t i).length ≤ T)
    (hpad : roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w (T + 1) m).post.length + 1)
    (hAcc : ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
        (obsPhase q b ((M.stutter).haltNorm))).run
      (expandCost (a :: l') + 1
        + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
        + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
            + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b))
      ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).start,
        Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i)))
          ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
            ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept) :
    M.AcceptsWithin w T := by
  have hxM : (Reg.initReg M.start w (T + 1) m).MarkersOK := Reg.initReg_markersOK M.start w (T + 1) m
  have hxw : CfgEquiv (Reg.initReg M.start w (T + 1) m).toConfig (M.init w) :=
    Reg.initReg_cfgEquiv M w (T + 1) m
  -- 机器层 → 运行相位机（预算 `rc_B + branchBudget`）
  have hbK : roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b + 1
      ≤ (Reg.enc (Reg.initReg M.start w (T + 1) m)
          (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))).right.length := by
    rw [Reg.enc_right_length]; exact hpad
  have hob := (branchMachine_accept_iff_two_pad M.start w a l' hw hl T m b
    (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
      + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)
    hT hm
    (none :: List.replicate Z (some false) ++ digitArea (i % B :: branchBlocks B t i))
    R M hbK).mp hAcc
  -- 运行相位机 → 观察机命中（同一预算）
  have hhit := (obsPhase_accept_iff q b ((M.stutter).haltNorm)
    (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
      + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)
    ⟨(simObs q b ((M.stutter).haltNorm)).start,
      Reg.enc (Reg.initReg M.start w (T + 1) m)
        (none :: List.replicate Z (some false)
          ++ digitArea (i % B :: branchBlocks B t i))⟩).mp hob
  -- 把预算拆成 `rc_i + K`，交给任意预算可靠性
  have hrc : roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
      (Reg.initReg M.start w (T + 1) m).cur
    ≤ roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur :=
    roundCostStay_mono _ _ _ _ _ _ (Nat.le_refl _) (Nat.le_of_lt (Nat.mod_lt i hBpos))
  refine acceptsWithin_of_dummy_branch_acc_budget q b B t i T M w hBpos hbnd hlB Z
    (Reg.initReg M.start w (T + 1) m) hxM hxw hpadpost hpadpre hlen (by omega) hk1 hk2
    rfl hxacc hxre
    (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
      + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b
      - roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B) (Reg.initReg M.start w (T + 1) m).cur)
    ?_ ?_
  · -- `hK`：前缀通路步数落在 `总预算 - rc_i` 内
    intro L1 hb1 r1 hle1 hp1
    have h1 := passRun_steps_le_uniform q b ((M.stutter).haltNorm).step
      (Z + i % B + 3) (i % B + 1) hk1
      (Reg.initReg M.start w (T + 1) m) L1 hb1 r1 hp1 T hle1
    have hmod : i % B < B := Nat.mod_lt i hBpos
    have h2 : costCap (Reg.initReg M.start w (T + 1) m).pre.length (Z + (i % B + 3)) T (2 ^ b)
        = costCap (Reg.initReg M.start w (T + 1) m).pre.length Z T (2 ^ b) + 2 * (i % B + 3) :=
      costCap_Z_shift _ _ _ _ _
    rw [show Z + i % B + 3 = Z + (i % B + 3) from by omega, h2] at h1
    have hmul : T * (costCap (Reg.initReg M.start w (T + 1) m).pre.length Z T (2 ^ b)
          + 2 * (i % B + 3))
        ≤ T * costCap (Reg.initReg M.start w (T + 1) m).pre.length Z T (2 ^ b)
          + 2 * (B + 3) * (T + 1) := by
      rw [Nat.mul_add]
      have hle : T * (2 * (i % B + 3)) ≤ 2 * (B + 3) * (T + 1) := by
        rw [show T * (2 * (i % B + 3)) = 2 * (i % B + 3) * T from Nat.mul_comm _ _]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
      omega
    have hBB : r1.steps + 6 ≤ branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b := by
      unfold branchBudget
      omega
    -- `branchBudget ≤ 总预算 - rc_i`
    have hle2 : branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b
        ≤ roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
          + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b
          - roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B) (Reg.initReg M.start w (T + 1) m).cur := by
      omega
    exact Nat.le_trans hBB hle2
  · -- 命中时刻：`run (rc_i + K) = run 总预算`
    rw [show roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B) (Reg.initReg M.start w (T + 1) m).cur
          + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
            + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b
            - roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
                (Reg.initReg M.start w (T + 1) m).cur)
        = roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
          + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b from by omega]
    exact hhit

set_option maxHeartbeats 2000000 in

/-- **单条等价（解耦副垫）**：存在分支使整机在统一预算内接受 ⇔ 原机 `T` 步内接受。
    Single equivalence with decoupled pads — E's per-branch interface. -/
theorem branchMachine_dummy_iff_two {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hB : ∀ s x', (M.step s x').length ≤ B) (hBpos : 0 < B)
    (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T) (Z m : Nat) (hm : 1 ≤ m)
    (hZT : Z ≤ T + 1) (R : List Sym) (hd1 : T ≤ m)
    (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject)
    (hpost : ∀ t i, 1 ≤ t → t ≤ T → (branchBlocks B t i).length + 1
      ≤ (Reg.initReg M.start w (T + 1) m).post.length)
    (hpre : ∀ t i, 1 ≤ t → t ≤ T → (branchBlocks B t i).length + 1
      ≤ (Reg.initReg M.start w (T + 1) m).pre.length)
    (hpad : roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w (T + 1) m).post.length + 1) :
    (∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
              + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b))
        ⟨(seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea (i % B :: branchBlocks B t i)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept) ↔
      M.AcceptsWithin w T := by
  constructor
  · -- 可靠性方向：整机接受 ⇒ 原机在 `T` 步内接受
    rintro ⟨t, i, ht1, htT, _hiT, hacc⟩
    have hmod : i % B < B := Nat.mod_lt i hBpos
    refine branchMachine_dummy_sound_two M w a l' hw hl hBpos
      (stutter_step_length_le M B hB) T b t i hT ht1 htT hbnd Z m hm hZT R hd1
      (by omega) (by omega) hxacc hxre (hpost t i ht1 htT) (hpre t i ht1 htT) ?_ hpad hacc
    rw [branchBlocks_length B t i (by omega)]
    exact htT
  · -- 完备性方向：原机接受 ⇒ 某分支在统一预算内接受（接受态冻结放宽预算）
    intro hacc
    obtain ⟨t, i, ht1, htT, hiT, haccm⟩ :=
      branchMachine_dummy_complete_two M w a l' hw hl hB hBpos T b hbnd hT Z m hm hZT R hd1
        hxacc hxre hpad hacc
    refine ⟨t, i, ht1, htT, hiT, ?_⟩
    have hmod : i % B < B := Nat.mod_lt i hBpos
    have hrc : roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
          (Reg.initReg M.start w (T + 1) m).cur
        ≤ roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur :=
      roundCostStay_mono (Reg.initReg M.start w (T + 1) m) Z Z (i % B) B
        (Reg.initReg M.start w (T + 1) m).cur (Nat.le_refl _) (Nat.le_of_lt hmod)
    have hsplit : expandCost (a :: l') + 1
          + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
              + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b)
        = (expandCost (a :: l') + 1
          + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
                (Reg.initReg M.start w (T + 1) m).cur
              + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b))
          + (roundCostStay (Reg.initReg M.start w (T + 1) m) Z B (Reg.initReg M.start w (T + 1) m).cur
              - roundCostStay (Reg.initReg M.start w (T + 1) m) Z (i % B)
                  (Reg.initReg M.start w (T + 1) m).cur) := by
      omega
    rw [hsplit]
    exact DTM.run_add_state_of_accept _ _ _ _ haccm



/-- **左预留前提（解耦版）自动成立**：左垫固定 `T+1`、`t ≤ T` 时分支块表放得下。
    Left-pad premise holds automatically with the fixed left pad `T+1`. -/
theorem branchMachine_pre_ok_two {q : Nat} (M : NTM q) (w : List Bool) {B : Nat}
    (T m t i : Nat) (hT : 0 < T) (_ht1 : 1 ≤ t) (htT : t ≤ T) :
    (branchBlocks B t i).length + 1 ≤ (Reg.initReg M.start w (T + 1) m).pre.length := by
  rw [Reg.initReg_pre_length, branchBlocks_length B t i (by omega)]
  omega

/-- **右预留前提（解耦版）自动成立**：右侧格数至少 `m`，取 `m ≥ T+1` 即够。
    Right-pad premise holds automatically once the right pad is at least `T+1`. -/
theorem branchMachine_post_ok_two {q : Nat} (M : NTM q) (w : List Bool) {B : Nat}
    (T m t i : Nat) (_hT : 0 < T) (ht1 : 1 ≤ t) (htT : t ≤ T) (hm : T + 1 ≤ m) :
    (branchBlocks B t i).length + 1 ≤ (Reg.initReg M.start w (T + 1) m).post.length := by
  rw [Reg.initReg_post_length, branchBlocks_length B t i (by omega)]
  have h0 : 0 ≤ ((w.map some).drop 1).length := Nat.zero_le _
  omega

/-- **右长覆盖前提（解耦版）的满足条件**：只要 `m` 不小于「单轮成本 + 逐分支预算 + 1」，
    `hpad` 就成立。#265 的空真性由此消除——`m` 只受预算（关于 `T` 的多项式）约束。
    The decoupled right-pad premise holds as soon as `m` covers the budget — its size is
    polynomial in `T`, so the defect of #265 is gone. -/
theorem branchMachine_hpad_two {q : Nat} (M : NTM q) (w : List Bool) (Z T B b m : Nat)
    (hm : roundCostStay (Reg.initReg M.start w (T + 1) 0) Z B
            (Reg.initReg M.start w (T + 1) 0).cur
          + branchBudget (T + 1) Z T B b + 1 ≤ m) :
    roundCostStay (Reg.initReg M.start w (T + 1) m) Z B
          (Reg.initReg M.start w (T + 1) m).cur
        + branchBudget (Reg.initReg M.start w (T + 1) m).pre.length Z T B b + 1
      ≤ 3 * (Reg.initReg M.start w (T + 1) m).post.length + 1 := by
  -- `pre.length` 与 `cur` 都与右垫无关，故单轮成本与预算项逐字相同
  have hpre : (Reg.initReg M.start w (T + 1) m).pre.length = T + 1 :=
    Reg.initReg_pre_length M.start w (T + 1) m
  -- 单轮成本只读 `pre` 与 `cur`，两者都与右垫无关
  have hEq : roundCostStay (Reg.initReg M.start w (T + 1) m) Z B
        (Reg.initReg M.start w (T + 1) m).cur
      = roundCostStay (Reg.initReg M.start w (T + 1) 0) Z B
        (Reg.initReg M.start w (T + 1) 0).cur := rfl
  rw [hEq, hpre]
  have hpost : (Reg.initReg M.start w (T + 1) m).post.length
      = ((w.map some).drop 1).length + m :=
    Reg.initReg_post_length M.start w (T + 1) m
  rw [hpost]
  omega

/-- **逐分支右垫的推荐取值**：单轮成本 + 逐分支预算 + 1（关于 `T` 的多项式）。
    Recommended right-pad size: one round's cost plus the per-branch budget. -/
def branchPad {q : Nat} (st : Fin q) (w : List Bool) (Z T B b : Nat) : Nat :=
  roundCostStay (Reg.initReg st w (T + 1) 0) Z B (Reg.initReg st w (T + 1) 0).cur
    + branchBudget (T + 1) Z T B b + 1

/-- `branchPad` 至少为 `T`：单轮成本已含 `6(T+1)` 的码长。
    `branchPad` dominates `T` because one round costs at least `6(T+1)`. -/
theorem branchPad_ge_T {q : Nat} (st : Fin q) (w : List Bool) (Z T B b : Nat) (hT : 0 < T) :
    T ≤ branchPad st w Z T B b := by
  unfold branchPad
  have h := roundCostStay_ge_pre (Reg.initReg st w (T + 1) 0) Z B
    (Reg.initReg st w (T + 1) 0).cur
  rw [Reg.initReg_pre_length] at h
  omega

/-- `branchPad` 至少为 `T+1`（右侧预留判据的要求）。 -/
theorem branchPad_ge_succ {q : Nat} (st : Fin q) (w : List Bool) (Z T B b : Nat) :
    T + 1 ≤ branchPad st w Z T B b := by
  unfold branchPad
  have h := roundCostStay_ge_pre (Reg.initReg st w (T + 1) 0) Z B
    (Reg.initReg st w (T + 1) 0).cur
  rw [Reg.initReg_pre_length] at h
  omega

/-- `branchPad` 非零。 -/
theorem branchPad_pos {q : Nat} (st : Fin q) (w : List Bool) (Z T B b : Nat) :
    1 ≤ branchPad st w Z T B b := by
  unfold branchPad
  omega

set_option maxHeartbeats 2000000 in
/-- **逐分支判定机：单条等价（前提全自动）**：右垫取 `branchPad`（多项式）后，
    三件前提（左右预留、右长覆盖）全部自动成立；E 的逐分支循环体可直接引用本条。
    Per-branch equivalence with all pad premises discharged automatically. -/
theorem branchMachine_dummy_iff_two_auto {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hB : ∀ s x', (M.step s x').length ≤ B) (hBpos : 0 < B)
    (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T) (Z : Nat) (hZT : Z ≤ T + 1)
    (R : List Sym) (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject) :
    (∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea (i % B :: branchBlocks B t i)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept) ↔
      M.AcceptsWithin w T := by
  have hm : 1 ≤ branchPad M.start w Z T B b := branchPad_pos M.start w Z T B b
  have hd1 : T ≤ branchPad M.start w Z T B b := branchPad_ge_T M.start w Z T B b hT
  exact branchMachine_dummy_iff_two M w a l' hw hl hB hBpos T b hbnd hT Z
    (branchPad M.start w Z T B b) hm hZT R hd1 hxacc hxre
    (fun t i ht1 htT => branchMachine_post_ok_two M w T _ t i hT ht1 htT
      (branchPad_ge_succ M.start w Z T B b))
    (fun t i ht1 htT => branchMachine_pre_ok_two M w T _ t i hT ht1 htT)
    (branchMachine_hpad_two M w Z T B b _ (Nat.le_refl _))


set_option maxHeartbeats 2000000 in
/-- **计数器形式的单条等价**：E 只维护一个全局计数器 `j < T·B^T`，分支取
    `(t, i) = branchOfIndex B T j`；把 `branchMachine_dummy_iff_two_auto` 的「族上存在」
    换成「计数器上存在」，是外层循环的直接接口。
    Counter form of the per-branch equivalence — E's outer-loop interface. -/
theorem branchMachine_dummy_iff_two_index {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hB : ∀ s x', (M.step s x').length ≤ B) (hBpos : 0 < B)
    (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T) (Z : Nat) (hZT : Z ≤ T + 1)
    (R : List Sym) (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject) :
    (∃ j, j < T * B ^ T ∧
      ((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea ((branchOfIndex B T j).2 % B :: branchBlocks B (branchOfIndex B T j).1 (branchOfIndex B T j).2)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept) ↔
      M.AcceptsWithin w T := by
  constructor
  · rintro ⟨j, hj, hacc⟩
    obtain ⟨t, i, ht1, htT, hi, hPi⟩ :=
      (exists_branch_iff_exists_index B T hBpos hT (fun t i =>
        ((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea (i % B :: branchBlocks B t i)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept)).mpr ⟨j, hj, hacc⟩
    exact (branchMachine_dummy_iff_two_auto M w a l' hw hl hB hBpos T b hbnd hT Z hZT R
      hxacc hxre).mp ⟨t, i, ht1, htT, hi, hPi⟩
  · intro hacc
    obtain ⟨t, i, ht1, htT, hi, hPi⟩ :=
      (branchMachine_dummy_iff_two_auto M w a l' hw hl hB hBpos T b hbnd hT Z hZT R
        hxacc hxre).mpr hacc
    exact (exists_branch_iff_exists_index B T hBpos hT (fun t i =>
      ((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea (i % B :: branchBlocks B t i)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept)).mp ⟨t, i, ht1, htT, hi, hPi⟩

set_option maxHeartbeats 1000000 in
/-- **推荐右垫的指数上界**：`Z ≤ T+1`、`B ≤ 2^b` ⇒
    `branchPad ≤ 2^((2·2^b+42)·(T+1) + (b+9))`。
    这是 E 的 `hHalt` 中「右垫大小不破坏指数时间界」的算术外壳。
    Exponential bound on the recommended right pad — the `hHalt` arithmetic shell. -/
theorem branchPad_le_two_pow {q : Nat} (st : Fin q) (w : List Bool) (Z T B b : Nat)
    (hZ : Z ≤ T + 1) (hB : B ≤ 2 ^ b) :
    branchPad st w Z T B b ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 9)) := by
  have hpos : 1 ≤ 2 * 2 ^ b + 42 := by omega
  have h2B : 2 * B ≤ 2 * 2 ^ b := Nat.mul_le_mul_left 2 hB
  -- 单轮成本 ≤ `costCap (T+1) Z T (2^b)`
  have hrc : roundCostStay (Reg.initReg st w (T + 1) 0) Z B
        (Reg.initReg st w (T + 1) 0).cur ≤ costCap (T + 1) Z T (2 ^ b) := by
    have h := roundCostStay_le (Reg.initReg st w (T + 1) 0) Z B
      (Reg.initReg st w (T + 1) 0).cur
    rw [Reg.initReg_pre_length] at h
    unfold costCap
    omega
  have hcost : costCap (T + 1) Z T (2 ^ b) ≤ polyCost (2 ^ b) (T + 1) :=
    Nat.le_trans (costCap_le_of_le (T + 1) Z T (T + 1) (2 ^ b) (Nat.le_succ T))
      (costCap_le_poly (T + 1) Z (T + 1) (2 ^ b) (Nat.le_refl _) hZ)
  -- 主指数 `E`
  have hmul : T * costCap (T + 1) Z T (2 ^ b) ≤ (T + 1) * polyCost (2 ^ b) (T + 1) :=
    Nat.le_trans (Nat.mul_le_mul_left T hcost)
      (Nat.mul_le_mul_right (polyCost (2 ^ b) (T + 1)) (Nat.le_succ T))
  have h1 : T * costCap (T + 1) Z T (2 ^ b) ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) :=
    Nat.le_trans hmul (polyCost_mul_le (2 ^ b) (T + 1))
  -- `costCap ≤ 2^E`（`polyCost ≤ (T+1)·polyCost`）
  have hpoly_le : polyCost (2 ^ b) (T + 1) ≤ (T + 1) * polyCost (2 ^ b) (T + 1) :=
    Nat.le_mul_of_pos_left _ (by omega : 0 < T + 1)
  have hcap : costCap (T + 1) Z T (2 ^ b) ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) :=
    Nat.le_trans hcost (Nat.le_trans hpoly_le (polyCost_mul_le (2 ^ b) (T + 1)))
  -- 第二项 `2·(B+3)·(T+1) + 6 ≤ 2^(b+5+(T+1))`
  have hcoef : 2 * (B + 3) ≤ 2 ^ (b + 3) := by
    have h1' : 2 * (B + 3) ≤ 2 * (2 ^ b + 3) :=
      Nat.mul_le_mul_left 2 (Nat.add_le_add_right hB 3)
    have h2' : 2 * (2 ^ b + 3) ≤ 2 ^ (b + 3) := by
      have hp : 2 ^ (b + 3) = 8 * 2 ^ b := by
        rw [Nat.pow_add]
        rw [show 2 ^ 3 = 8 from by decide]
        exact Nat.mul_comm (2 ^ b) 8
      have h6 : 6 ≤ 6 * 2 ^ b := by
        have hp1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        omega
      rw [hp]
      omega
    exact Nat.le_trans h1' h2'
  have h2 : 2 * (B + 3) * (T + 1) + 6 ≤ 2 ^ (b + 5 + (T + 1)) := by
    have hmul' : 2 * (B + 3) * (T + 1) ≤ 2 ^ (b + 4 + (T + 1)) := by
      refine Nat.le_trans (Nat.mul_le_mul hcoef (self_le_two_pow (T + 1))) ?_
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
    have h6 : 6 ≤ 2 ^ (b + 4 + (T + 1)) :=
      Nat.le_trans (by decide : 6 ≤ 2 ^ 3)
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
    calc 2 * (B + 3) * (T + 1) + 6 ≤ 2 ^ (b + 4 + (T + 1)) + 2 ^ (b + 4 + (T + 1)) :=
          Nat.add_le_add hmul' h6
      _ = 2 * 2 ^ (b + 4 + (T + 1)) := (Nat.two_mul _).symm
      _ = 2 ^ ((b + 4 + (T + 1)) + 1) := by
          rw [Nat.pow_succ]; exact Nat.mul_comm 2 _
      _ = 2 ^ (b + 5 + (T + 1)) := by
          rw [show (b + 4 + (T + 1)) + 1 = b + 5 + (T + 1) from by omega]
  -- 第二项指数不超过主指数
  have hsE : b + 5 + (T + 1) ≤ (2 * 2 ^ b + 42) * (T + 1) := by
    have hb : b + 6 ≤ 2 * 2 ^ b + 42 := by
      have hble : b ≤ 2 ^ b := self_le_two_pow b
      omega
    have hT : T ≤ (2 * 2 ^ b + 42) * T := Nat.le_mul_of_pos_left T hpos
    have hsum : (b + 6) + T ≤ (2 * 2 ^ b + 42) + (2 * 2 ^ b + 42) * T :=
      Nat.add_le_add hb hT
    rw [show (2 * 2 ^ b + 42) * (T + 1) = (2 * 2 ^ b + 42) + (2 * 2 ^ b + 42) * T from by
      rw [Nat.mul_succ]; omega]
    omega
  have h2' : 2 * (B + 3) * (T + 1) + 6 ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) :=
    Nat.le_trans h2 (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hsE)
  -- 逐项拼装
  have hbb : branchBudget (T + 1) Z T B b
      ≤ T * costCap (T + 1) Z T (2 ^ b) + (2 * (B + 3) * (T + 1) + 6) := by
    unfold branchBudget
    omega
  have hBB : branchBudget (T + 1) Z T B b
      ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) + 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) :=
    Nat.le_trans hbb (Nat.add_le_add h1 h2')
  have hrc' : roundCostStay (Reg.initReg st w (T + 1) 0) Z B
        (Reg.initReg st w (T + 1) 0).cur ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) :=
    Nat.le_trans hrc hcap
  -- 收尾：四段之和 ≤ `2^(E+2) ≤ 2^(E+(b+9))`
  have hE : 1 ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) := Nat.one_le_two_pow
  have hsum4 : 2 ^ ((2 * 2 ^ b + 42) * (T + 1))
        + (2 ^ ((2 * 2 ^ b + 42) * (T + 1)) + 2 ^ ((2 * 2 ^ b + 42) * (T + 1))) + 1
      ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + 2) := by
    rw [show (2 * 2 ^ b + 42) * (T + 1) + 2
        = ((2 * 2 ^ b + 42) * (T + 1) + 1) + 1 from by omega,
      Nat.pow_succ, Nat.pow_succ]
    omega
  refine Nat.le_trans ?_ (Nat.le_trans hsum4 (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)))
  unfold branchPad
  exact Nat.add_le_add (Nat.add_le_add hrc' hBB) (Nat.le_refl 1)

/-- 右垫写串的长度：`|padStr (m-1)| = 3m`（`m ≥ 1`）。
    Length of the written right pad, in terms of the pad size `m`. -/
theorem padStr_len_of_pos (m : Nat) (hm : 1 ≤ m) : (padStr (m - 1)).length = 3 * m := by
  rw [padStr_length]
  have := Nat.sub_add_cancel hm
  omega

/-- **二次项 + 线性项被小指数吸收**：`(n+1)² + 10(n+1) + 10 ≤ 2^(2(n+1)+6)`。
    用途：装配段成本（`expandCost_le` 的二次界）可整体塞进 `2^poly`。
    Quadratic plus linear terms are absorbed by a small exponential. -/
theorem quad_le_two_pow (T : Nat) :
    (T + 1) * (T + 1) + 10 * (T + 1) + 10 ≤ 2 ^ (2 * (T + 1) + 6) := by
  -- 记 `n = T+1`（`n ≥ 1`）
  have hn : 1 ≤ T + 1 := by omega
  -- `n² ≤ 2^(2n)`
  have hsq : (T + 1) * (T + 1) ≤ 2 ^ (2 * (T + 1)) := by
    have h1 : (T + 1) * (T + 1) ≤ 2 ^ (T + 1) * 2 ^ (T + 1) :=
      Nat.mul_le_mul (self_le_two_pow (T + 1)) (self_le_two_pow (T + 1))
    rw [← Nat.pow_add] at h1
    rwa [show (T + 1) + (T + 1) = 2 * (T + 1) from by omega] at h1
  -- `10n + 10 ≤ 2^(n+5)`
  have hlin : 10 * (T + 1) + 10 ≤ 2 ^ (T + 1 + 5) := by
    have hp : 2 ^ (T + 1 + 5) = 2 ^ 5 * 2 ^ (T + 1) := by
      rw [show T + 1 + 5 = 5 + (T + 1) from by omega, Nat.pow_add]
    have h32 : 32 * (T + 1) ≤ 32 * 2 ^ (T + 1) :=
      Nat.mul_le_mul_left 32 (self_le_two_pow (T + 1))
    have h5 : 2 ^ 5 = 32 := by decide
    rw [hp, h5]
    omega
  -- 两段合并
  have hsum : (T + 1) * (T + 1) + (10 * (T + 1) + 10)
      ≤ 2 ^ (2 * (T + 1)) + 2 ^ (T + 1 + 5) :=
    Nat.add_le_add hsq hlin
  have hmid : (T + 1) + 5 ≤ 2 * (T + 1) + 5 := by omega
  have hmax : max (2 * (T + 1)) (T + 1 + 5) ≤ 2 * (T + 1) + 5 := by
    rcases Nat.le_total (2 * (T + 1)) (T + 1 + 5) with h | h
    · rw [Nat.max_eq_right h]; omega
    · rw [Nat.max_eq_left h]; omega
  have hfin : 2 ^ (2 * (T + 1)) + 2 ^ (T + 1 + 5) ≤ 2 ^ (2 * (T + 1) + 6) := by
    refine Nat.le_trans (add_pow_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)) ?_
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  have hassoc : (T + 1) * (T + 1) + 10 * (T + 1) + 10
      = (T + 1) * (T + 1) + (10 * (T + 1) + 10) := by omega
  rw [hassoc]
  exact Nat.le_trans hsum hfin
set_option maxHeartbeats 2000000 in
/-- **逐分支整段步数的指数上界**：装配段 + 1 + 观察预算（含 `branchPad` 副垫）
    不超过 `2^((2·2^b+42)(T+1) + (b+20))`。E 的 `hHalt` 逐分支步骤外壳。
    Per-branch total step count (assembly + observer budget) is exponentially bounded. -/
theorem branchRunStep_le_two_pow {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (Z T B b : Nat) (hZ : Z ≤ T + 1) (hB : B ≤ 2 ^ b)
    (hl' : l'.length ≤ T) :
    expandCost (a :: l') + 1
      + ((padStr (branchPad st w Z T B b - 1)).length + 1
        + (3 * branchPad st w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
      + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
            (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
          + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b)
    ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 20)) := by
  -- 记号：`m` 为右垫，`rc`/`BB` 为单轮成本与逐分支预算
  have hm_pos : 1 ≤ branchPad st w Z T B b := branchPad_pos st w Z T B b
  have hm_le : branchPad st w Z T B b ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 9)) :=
    branchPad_le_two_pow st w Z T B b hZ hB
  have hlen : (padStr (branchPad st w Z T B b - 1)).length = 3 * branchPad st w Z T B b :=
    padStr_len_of_pos _ hm_pos
  have hpre : (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length = T + 1 :=
    Reg.initReg_pre_length st w (T + 1) _
  have hrcEq : roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
        (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
      = roundCostStay (Reg.initReg st w (T + 1) 0) Z B (Reg.initReg st w (T + 1) 0).cur := rfl
  have hmdef : branchPad st w Z T B b
      = roundCostStay (Reg.initReg st w (T + 1) 0) Z B (Reg.initReg st w (T + 1) 0).cur
        + branchBudget (T + 1) Z T B b + 1 := rfl
  -- 观察预算 ≤ 右垫
  have hrcBB : roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
          (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
        + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b
      ≤ branchPad st w Z T B b := by
    rw [hpre, hrcEq, hmdef]
    omega
  -- 装配段：`expandCost ≤ 2^(2(T+1)+6)`
  have hexp : expandCost (a :: l') ≤ 2 ^ (2 * (T + 1) + 6) := by
    have h1 := expandCost_le (a :: l')
    have hlen' : (a :: l').length = l'.length + 1 := rfl
    rw [hlen'] at h1
    have hn : l'.length + 1 ≤ T + 1 := by omega
    have h2 : (l'.length + 1) * (l'.length + 1) ≤ (T + 1) * (T + 1) :=
      Nat.mul_le_mul hn hn
    have h3 : 10 * (l'.length + 1) ≤ 10 * (T + 1) := Nat.mul_le_mul_left 10 hn
    have h4 : (l'.length + 1) * (l'.length + 1) + 10 * (l'.length + 1) + 10
        ≤ (T + 1) * (T + 1) + 10 * (T + 1) + 10 :=
      Nat.add_le_add (Nat.add_le_add h2 h3) (Nat.le_refl 10)
    exact Nat.le_trans (Nat.le_trans h1 h4) (quad_le_two_pow T)
  -- 各分量都被 `2^M` 控制（`M := (2·2^b+42)(T+1)+(b+12)`）
  have hA : expandCost (a :: l') ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 12)) := by
    refine Nat.le_trans hexp ?_
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    have h1 : 2 * (T + 1) ≤ (2 * 2 ^ b + 42) * (T + 1) :=
      Nat.mul_le_mul_right (T + 1) (by omega)
    omega
  have hB' : 6 * branchPad st w Z T B b ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 12)) := by
    have h8 : 6 * branchPad st w Z T B b ≤ 8 * branchPad st w Z T B b := by omega
    have h9 : 8 * branchPad st w Z T B b
        ≤ 8 * 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 9)) :=
      Nat.mul_le_mul_left 8 hm_le
    have h8eq : 8 * 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 9))
        = 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 12)) := by
      rw [show (8 : Nat) = 2 ^ 3 from by decide, ← Nat.pow_add]
      congr 1
      omega
    exact Nat.le_trans (Nat.le_trans h8 h9) (Nat.le_of_eq h8eq)
  have hC : 3 * l'.length ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 12)) := by
    have hT : T ≤ 2 ^ T := self_le_two_pow T
    have h1 : 3 * l'.length ≤ 4 * T := by omega
    have h2 : 4 * T ≤ 4 * 2 ^ T := Nat.mul_le_mul_left 4 hT
    have h3 : 4 * 2 ^ T = 2 ^ (T + 2) := by
      rw [show (4 : Nat) = 2 ^ 2 from by decide, Nat.mul_comm, ← Nat.pow_add]
    refine Nat.le_trans (Nat.le_trans h1 h2) ?_
    rw [h3]
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    have h1' : T + 1 ≤ (2 * 2 ^ b + 42) * (T + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hD : roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
          (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
        + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b
      ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 12)) := by
    refine Nat.le_trans hrcBB ?_
    refine Nat.le_trans hm_le ?_
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    omega
  have hE6 : 6 ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1) + (b + 12)) :=
    Nat.le_trans (by decide : 6 ≤ 2 ^ 3)
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
  -- 先把整段长度化成五项和，再逐对合并
  have hsplit : expandCost (a :: l') + 1
        + ((padStr (branchPad st w Z T B b - 1)).length + 1
          + (3 * branchPad st w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
        + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
              (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
            + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b)
      = expandCost (a :: l') + 6 * branchPad st w Z T B b + 3 * l'.length
        + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
              (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
            + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b)
        + 6 := by
    rw [hlen]
    omega
  -- 主指数 `M`（局部定义：零依赖工程没有 Mathlib 的 `set` 战术）
  let M := (2 * 2 ^ b + 42) * (T + 1) + (b + 12)
  have hM : M = (2 * 2 ^ b + 42) * (T + 1) + (b + 12) := rfl
  have h1 : expandCost (a :: l') + 6 * branchPad st w Z T B b ≤ 2 ^ (M + 1) :=
    Nat.le_trans (Nat.add_le_add hA hB') (add_pow_le (Nat.le_refl M) (Nat.le_refl M))
  have h2 : 3 * l'.length
        + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
              (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
            + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b)
        ≤ 2 ^ (M + 1) :=
    Nat.le_trans (Nat.add_le_add hC hD) (add_pow_le (Nat.le_refl M) (Nat.le_refl M))
  have h12 : (expandCost (a :: l') + 6 * branchPad st w Z T B b)
        + (3 * l'.length
          + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
                (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
              + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b))
        ≤ 2 ^ (M + 2) :=
    Nat.le_trans (Nat.add_le_add h1 h2)
      (add_pow_le (by omega : M + 1 ≤ M + 1) (by omega : M + 1 ≤ M + 1))
  have h3 : 2 ^ (M + 2) + 6 ≤ 2 ^ (M + 3) :=
    Nat.le_trans (Nat.add_le_add (Nat.le_refl _) hE6)
      (add_pow_le (by omega : M + 2 ≤ M + 2) (by omega : M ≤ M + 2))
  -- 收尾
  rw [hsplit]
  have h4 : expandCost (a :: l') + 6 * branchPad st w Z T B b + 3 * l'.length
        + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
              (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
            + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b)
        + 6
      = ((expandCost (a :: l') + 6 * branchPad st w Z T B b)
          + (3 * l'.length
            + (roundCostStay (Reg.initReg st w (T + 1) (branchPad st w Z T B b)) Z B
                  (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).cur
                + branchBudget (Reg.initReg st w (T + 1) (branchPad st w Z T B b)).pre.length Z T B b)))
        + 6 := by omega
  rw [h4]
  refine Nat.le_trans (Nat.add_le_add h12 (Nat.le_refl 6)) ?_
  refine Nat.le_trans h3 ?_
  apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
  rw [hM]
  omega

end DTM

end Pnp
