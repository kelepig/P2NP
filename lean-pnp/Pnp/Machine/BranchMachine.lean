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

end DTM

end Pnp
