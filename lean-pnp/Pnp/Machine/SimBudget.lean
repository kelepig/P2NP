/-
  文件：Pnp/Machine/SimBudget.lean
  主题：枚举器的「按固定预算跑观察机」接口（义务 b 的接受方向）。

  外层枚举对每条分支只做一件事：从分支起点把观察机跑满一个**统一预算**
  `BUDGET = 2^((2·2^b+42)·T)` 步，然后看末态是否等于 `obsAcc`。
  本文件把「分支接受 ⇒ 观察机在预算后停在 `obsAcc`」整条接好：
    - `simObs_run_accept_at_budget`：一旦某步命中 `obsAcc`，之后跑多久都仍在 `obsAcc`；
    - `obsAcc_at_budget_of_passRun_accept`：成功通路 + 终态接受 + 单分支预算界
      ⇒ 观察机跑满 `BUDGET` 步后停在 `obsAcc`。

  The enumerator runs the observer machine for a fixed budget per branch and inspects
  the final state; this file assembles the accept-direction budget verdict.
-/
import Pnp.Machine.SimDecide
import Pnp.Machine.SimAcceptObs
import Pnp.Machine.SimExpBound
import Pnp.Machine.SimPassPrefix

namespace Pnp

namespace DTM

/-- `obsAcc` 一旦命中便保持：第 `n` 步在 `obsAcc` 且 `n ≤ budget` ⇒ 第 `budget` 步仍在 `obsAcc`。
    Persistence wrapper: an accept hit at step `n` survives to any later budget. -/
theorem simObs_run_accept_at_budget (q b : Nat) (M : NTM q)
    (n budget : Nat) (c : Config (stateCountO q b)) (hn : n ≤ budget)
    (h : ((simObs q b M).run n c).state = obsAcc q b) :
    ((simObs q b M).run budget c).state = obsAcc q b := by
  rw [← Nat.add_sub_of_le hn]
  exact simObs_run_accept_persists q b M n (budget - n) c h

/-- **相位 14 ⇒ 失败并保持**：若观察机第 `i` 步处于模拟层相位 14 的死态（且当前模拟状态
    非接受），则第 `i+1` 步进入 `obsFail`，此后（再跑 `m` 步）一直是 `obsFail`。
    这是驱动层「数字区耗尽 ⇒ 转入终止」终止引理在观察层的落点。
    Entering phase 14 makes the observer fall into `obsFail` and stay there. -/
theorem simObs_phase14_fail_persists (q b : Nat) (M : NTM q)
    (i m : Nat) (X : Config (stateCountO q b)) (s : Fin (stateCountO q b))
    (hst : ((simObs q b M).run i X).state = s)
    (hlt : s.val < stateCountD q b) (hin : s.val < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 s.val ≠ M.accept.val)
    (h14 : unpackPh (2 ^ b) 9 15 s.val = 14) :
    ((simObs q b M).run (i + 1 + m) X).state = obsFail q b := by
  have hhalt : (simObs q b M).halted ((simObs q b M).run i X) = false := by
    have h2 : (simObs q b M).run i X
        = Config.mk s ((simObs q b M).run i X).tape := by
      rw [← hst]
    rw [h2]
    exact simObs_halted_inner q b M s hlt ((simObs q b M).run i X).tape
  have hstep : ((simObs q b M).run (i + 1) X).state = obsFail q b := by
    rw [run_succ_last (simObs q b M) i X hhalt,
      stepConfig_state (simObs q b M) ((simObs q b M).run i X), hst,
      simObs_step_fail q b M s hlt hin hacc h14]
  rw [show i + 1 + m = (i + 1) + m from by omega]
  exact simObs_run_fail_persists q b M (i + 1) m X hstep

/-! ## 查表失败 ⇒ 分支失败（拒绝方向的终止机制）

  关键设计事实（#135）：模拟区走到**拒绝态**后，规范形 `haltNorm` 的规则表为空，
  下一轮读符号 + 查表必然失败，驱动层因此在 5 步内进入模拟层相位 14，观察层随即
  落到 `obsFail` 并保持。**不需要**另加「数字区耗尽」检测：机器在 `T` 步内必然停机，
  停机后的查表失败本身就是终止机制（见 `HaltsWithin` 的语义）。
  Design fact (#135): once the simulated region halts in the reject state, `haltNorm`
  has no rule for it, so the next read+lookup fails and the driver enters phase 14 in
  five steps; the observer then sits in `obsFail` for good. -/

/-- `embS` 下的 `codeState` 可观察：模拟状态非接受、相位 ≠ 14。
    Observability of an embedded `codeState`. -/
theorem observe_embS_codeState (q b : Nat) (M : NTM q) (m c z ph : Nat)
    (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (hph : ph < 15)
    (hacc : m ≠ M.accept.val) (h14 : ph ≠ 14) :
    observeState q b M (embS (codeState q b m c z ph hm hc hz hph)) := by
  refine ⟨?_, ?_⟩
  · simp only [embS, Fin.val_mk]
    have h := (codeState q b m c z ph hm hc hz hph).isLt
    unfold stateCountD at h
    omega
  · intro _
    simp only [embS, Fin.val_mk]
    exact ⟨by rw [codeState_unpackM q b m c z ph hm hc hz hph]; exact hacc,
      by rw [codeState_unpackPh q b m c z ph hm hc hz hph]; exact h14⟩

/-- **查表失败 ⇒ 模拟层相位 14（驱动层）**：驱动层从模拟层相位 0 出发，若当前选择 `c`
    查表无候选动作，则 5 步后停在模拟层相位 14，纸带不变。
    Lookup failure drives `simDrive` into simulation-layer phase 14 in five steps. -/
theorem simDrive_lookup_fail_ph14 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (x : Reg q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpk : pick (tab x.state x.cur) c = none) (L : List Sym) :
    (simDrive q b tab s0).run 5
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L)) =
    Config.mk (embS (codeState q b m c (symIdx x.cur) 14 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide))) (x.enc L) := by
  -- 前 5 步全在模拟层相位 0..4，故驱动层与 `simStep` 一致
  have hrun := simDrive_run_embS q b tab s0 5
    (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide)) (x.enc L))
    (by
      intro k hk
      exact simStep_run_ph_ne13 q b tab s0
        (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide)) (x.enc L))
        (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)) k (by omega))
  rw [hrun]
  have hpk' : pick (tab (⟨m, hm⟩ : Fin q) x.cur) c = none := by simpa only [hx] using hpk
  have hmain := simStep_readLookup_run_none q b tab s0 m c hm hc x.cur x.pre x.post L hpk'
  simp only [Reg.enc]
  rw [← tape_marker_left x.cur x.pre L, hmain]

/-- **查表失败 ⇒ `obsFail`（观察层，6 步）**：观察机从分支起点（模拟层相位 0）出发，
    若当前选择查表失败且当前模拟状态非接受，则 6 步后停在 `obsFail`。
    Lookup failure sends the observer to `obsFail` in six steps. -/
theorem simObs_run6_fail_of_lookup_none (q b : Nat) (M : NTM q)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (x : Reg q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hacc : x.state ≠ M.accept)
    (hpk : pick (M.step x.state x.cur) c = none) (L : List Sym) :
    ((simObs q b M).run 6
        (Config.mk (embO q b (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))))
          (x.enc L))).state = obsFail q b := by
  have hpk' : pick (M.step (⟨m, hm⟩ : Fin q) x.cur) c = none := by simpa only [hx] using hpk
  have haccm : m ≠ M.accept.val := fun h => hacc (by rw [hx]; exact Fin.ext h)
  have e0 : (simObs q b M).stepConfig
      (Config.mk (embO q b (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))))
        (x.enc L)) =
      Config.mk (embO q b (embS (codeState q b m c 0 1 hm hc (by decide) (by decide))))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post)) := by
    simp only [Reg.enc]
    rw [simObs_stepConfig_delegate q b M
      (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (some true :: codeCells x.post))
      (observe_embS_codeState q b M m c 0 0 hm hc (by decide) (by decide) haccm (by decide)),
      simDrive_stepConfig_embS q b M.step M.start
        (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
          (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
            (some true :: codeCells x.post)))
        (by rw [codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)]; decide),
      simStep_readStep0 q b M.step M.start m c hm hc x.cur x.pre x.post L]
  have e1 : (simObs q b M).stepConfig
      (Config.mk (embO q b (embS (codeState q b m c 0 1 hm hc (by decide) (by decide))))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post))) =
      Config.mk (embO q b (embS (codeState q b m c (symIdx (codeSnd x.cur)) 2 hm hc
          (by have := symIdx_lt (codeSnd x.cur); omega) (by decide))))
        (Tape.mk (List.reverse (codeCells x.pre) ++ L)
          (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post)) := by
    rw [simObs_stepConfig_delegate q b M
      (embS (codeState q b m c 0 1 hm hc (by decide) (by decide)))
      (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (codeSnd x.cur :: some true :: codeCells x.post))
      (observe_embS_codeState q b M m c 0 1 hm hc (by decide) (by decide) haccm (by decide)),
      simDrive_stepConfig_embS q b M.step M.start
        (Config.mk (codeState q b m c 0 1 hm hc (by decide) (by decide))
          (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
            (codeSnd x.cur :: some true :: codeCells x.post)))
        (by rw [codeState_unpackPh q b m c 0 1 hm hc (by decide) (by decide)]; decide),
      simStep_readStep1 q b M.step M.start m c hm hc x.cur x.pre x.post L]
  have e2 : (simObs q b M).stepConfig
      (Config.mk (embO q b (embS (codeState q b m c (symIdx (codeSnd x.cur)) 2 hm hc
          (by have := symIdx_lt (codeSnd x.cur); omega) (by decide))))
        (Tape.mk (List.reverse (codeCells x.pre) ++ L)
          (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post))) =
      Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 3 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post)) := by
    rw [simObs_stepConfig_delegate q b M
      (embS (codeState q b m c (symIdx (codeSnd x.cur)) 2 hm hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)))
      (Tape.mk (List.reverse (codeCells x.pre) ++ L)
        (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post))
      (observe_embS_codeState q b M m c (symIdx (codeSnd x.cur)) 2 hm hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide) haccm (by decide)),
      simDrive_stepConfig_embS q b M.step M.start
        (Config.mk (codeState q b m c (symIdx (codeSnd x.cur)) 2 hm hc
            (by have := symIdx_lt (codeSnd x.cur); omega) (by decide))
          (Tape.mk (List.reverse (codeCells x.pre) ++ L)
            (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post)))
        (by rw [codeState_unpackPh q b m c (symIdx (codeSnd x.cur)) 2 hm hc
          (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)]; decide),
      simStep_readStep2 q b M.step M.start m c hm hc x.cur x.pre x.post L]
  have e3 : (simObs q b M).stepConfig
      (Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 3 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post))) =
      Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 4 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post)) := by
    rw [simObs_stepConfig_delegate q b M
      (embS (codeState q b m c (symIdx x.cur) 3 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide)))
      (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (codeSnd x.cur :: some true :: codeCells x.post))
      (observe_embS_codeState q b M m c (symIdx x.cur) 3 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide) haccm (by decide)),
      simDrive_stepConfig_embS q b M.step M.start
        (Config.mk (codeState q b m c (symIdx x.cur) 3 hm hc
            (by have := symIdx_lt x.cur; omega) (by decide))
          (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
            (codeSnd x.cur :: some true :: codeCells x.post)))
        (by rw [codeState_unpackPh q b m c (symIdx x.cur) 3 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide)]; decide),
      simStep_readStep3 q b M.step M.start m c hm hc x.cur x.pre x.post L]
  have e4 : (simObs q b M).stepConfig
      (Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 4 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post))) =
      Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 14 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post)) := by
    rw [simObs_stepConfig_delegate q b M
      (embS (codeState q b m c (symIdx x.cur) 4 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide)))
      (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (some true :: codeCells x.post))
      (observe_embS_codeState q b M m c (symIdx x.cur) 4 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide) haccm (by decide)),
      simDrive_stepConfig_embS q b M.step M.start
        (Config.mk (codeState q b m c (symIdx x.cur) 4 hm hc
            (by have := symIdx_lt x.cur; omega) (by decide))
          (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
            (some true :: codeCells x.post)))
        (by rw [codeState_unpackPh q b m c (symIdx x.cur) 4 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide)]; decide),
      simStep_lookupStep_none q b M.step M.start m c hm hc x.cur (some true)
        (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (codeCells x.post) hpk']
  -- 前五个格局都在驱动空间内部（观察机不停机）
  have halt0 : (simObs q b M).halted
      (Config.mk (embO q b (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))))
        (x.enc L)) = false :=
    simObs_halted_inner q b M _ (stateCount_lt_stateCountD q b _
      (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt) _
  have halt1 : (simObs q b M).halted
      (Config.mk (embO q b (embS (codeState q b m c 0 1 hm hc (by decide) (by decide))))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post))) = false :=
    simObs_halted_inner q b M _ (stateCount_lt_stateCountD q b _
      (codeState q b m c 0 1 hm hc (by decide) (by decide)).isLt) _
  have halt2 : (simObs q b M).halted
      (Config.mk (embO q b (embS (codeState q b m c (symIdx (codeSnd x.cur)) 2 hm hc
          (by have := symIdx_lt (codeSnd x.cur); omega) (by decide))))
        (Tape.mk (List.reverse (codeCells x.pre) ++ L)
          (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post))) = false :=
    simObs_halted_inner q b M _ (stateCount_lt_stateCountD q b _
      (codeState q b m c (symIdx (codeSnd x.cur)) 2 hm hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)).isLt) _
  have halt3 : (simObs q b M).halted
      (Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 3 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post))) = false :=
    simObs_halted_inner q b M _ (stateCount_lt_stateCountD q b _
      (codeState q b m c (symIdx x.cur) 3 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide)).isLt) _
  have halt4 : (simObs q b M).halted
      (Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 4 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post))) = false :=
    simObs_halted_inner q b M _ (stateCount_lt_stateCountD q b _
      (codeState q b m c (symIdx x.cur) 4 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide)).isLt) _
  have hlt5 : (embO q b (embS (codeState q b m c (symIdx x.cur) 14 hm hc
      (by have := symIdx_lt x.cur; omega) (by decide)))).val < stateCountD q b :=
    stateCount_lt_stateCountD q b _
      (codeState q b m c (symIdx x.cur) 14 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide)).isLt
  have halt5 : (simObs q b M).halted
      (Config.mk (embO q b (embS (codeState q b m c (symIdx x.cur) 14 hm hc
          (by have := symIdx_lt x.cur; omega) (by decide))))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post))) = false :=
    simObs_halted_inner q b M _ hlt5 _
  -- 第 6 步：相位 14 落到失败哨兵
  have e5 : (simObs q b M).step
      (embO q b (embS (codeState q b m c (symIdx x.cur) 14 hm hc
        (by have := symIdx_lt x.cur; omega) (by decide))))
      (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (some true :: codeCells x.post)).read =
      (obsFail q b,
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post)).read, Dir.stay) :=
    simObs_step_fail q b M _
      hlt5
      (by simp only [embO, embS, Fin.val_mk]
          exact (codeState q b m c (symIdx x.cur) 14 hm hc
            (by have := symIdx_lt x.cur; omega) (by decide)).isLt)
      (by simp only [embO, embS, Fin.val_mk]
          rw [codeState_unpackM q b m c (symIdx x.cur) 14 hm hc
            (by have := symIdx_lt x.cur; omega) (by decide)]
          exact haccm)
      (by simp only [embO, embS, Fin.val_mk]
          rw [codeState_unpackPh q b m c (symIdx x.cur) 14 hm hc
            (by have := symIdx_lt x.cur; omega) (by decide)])
      _
  have r5 := run_five_of_steps (simObs q b M) halt0 halt1 halt2 halt3 halt4 e0 e1 e2 e3 e4
  -- 第 6 步
  rw [show (6 : Nat) = 5 + 1 from rfl, DTM.run_add, r5,
    DTM.run_succ_of_not_halted (simObs q b M) 0 _ halt5]
  simp only [DTM.run, DTM.stepConfig, e5]

/-- **末态非接受 ⇒ 预算内从不接受**：若观察机跑满 `budget` 步后不在 `obsAcc`，
    则此前任何一步也都不在 `obsAcc`（由接受命中的保持性取逆否）。
    A non-accepting final state rules out an accept hit anywhere within the budget;
    this is how the enumerator's per-branch reject check is read. -/
theorem simObs_no_accept_of_final_not (q b : Nat) (M : NTM q)
    (budget : Nat) (c : Config (stateCountO q b))
    (hfinal : ((simObs q b M).run budget c).state ≠ obsAcc q b) :
    ∀ n : Nat, n ≤ budget → ((simObs q b M).run n c).state ≠ obsAcc q b := by
  intro n hn hhit
  exact hfinal (simObs_run_accept_at_budget q b M n budget c hn hhit)

/-- **通路终点查表失败 ⇒ 预算末态是 `obsFail`**：通路停在 `passEnd` 后，若终态模拟状态
    非接受且当前选择查表失败（停机拒绝态的规范形正是如此），则观察机在预算 `≥ 6` 的
    任何时刻末态都是 `obsFail`。这是拒绝方向「预算末态判据」的落点。
    A successful pass followed by a failed lookup at `passEnd` lands the observer on
    `obsFail` at the end of the budget. -/
theorem simObs_budget_fail_of_passEnd_halt (q b : Nat) (M : NTM q) (r : PassRes q b)
    (hacc : r.reg.state ≠ (M.haltNorm).accept)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = none)
    (budget : Nat) (hbud : 6 ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state = obsFail q b := by
  have h6 := simObs_run6_fail_of_lookup_none q b (M.haltNorm) r.reg.state.val r.c
    r.reg.state.isLt r.hc r.reg rfl hacc hpk
    (none :: List.replicate r.z (some false) ++ digitArea [])
  rw [show budget = 6 + (budget - 6) from by omega]
  exact simObs_run_fail_persists q b (M.haltNorm) 6 (budget - 6) _ h6

/-- **通路终点查表失败 ⇒ 预算内从不接受**：同上条件下，观察机在预算内的任何时刻都不在
    `obsAcc`（对末态 `obsFail` 用 `simObs_no_accept_of_final_not`）。
    Same hypothesis: the observer never reaches `obsAcc` within the budget. -/
theorem simObs_no_accept_budget_of_passEnd_halt (q b : Nat) (M : NTM q) (r : PassRes q b)
    (hacc : r.reg.state ≠ (M.haltNorm).accept)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = none)
    (budget : Nat) (hbud : 6 ≤ budget) :
    ∀ n : Nat, n ≤ budget →
      ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state ≠ obsAcc q b := by
  have hfin := simObs_budget_fail_of_passEnd_halt q b M r hacc hpk budget hbud
  have hne : obsFail q b ≠ obsAcc q b := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [obsFail, obsAcc, Fin.val_mk] at hv
    omega
  refine simObs_no_accept_of_final_not q b (M.haltNorm) budget _ ?_
  rw [hfin]
  exact hne

/-- **分支通路后的不误接受（预算层）**：通路成功、沿途内部状态都非接受、终态查表失败
    （停机拒绝态），则观察机从分支起点跑满预算后仍不在 `obsAcc`。
    证明分两段：通路内用 `simObs_no_acc_upto`；通路后先经观察投影把格局换成 `passEnd`，
    再用 `simObs_no_accept_budget_of_passEnd_halt`。
    After a successful pass ending in a stuck (halting-reject) region, the observer never
    reaches `obsAcc` within the budget. -/
theorem simObs_no_acc_budget_of_passRun_halt (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z L)).state.val ≠ (M.haltNorm).accept.val)
    (hxacc : r.reg.state ≠ (M.haltNorm).accept)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = none)
    (budget : Nat) (hbud : r.steps + 6 ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  -- 通路内的可观察性 ⇒ 观察投影：`r.steps` 步后正是 `passEnd`
  have hobs := simObs_pass_obs q b (M.haltNorm) L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
  have hdele := simObs_run_delegate q b (M.haltNorm) r.steps
    (passStart x m c hm hc Z L) (fun i hi => hobs i hi)
  have hpe := simDrive_pass q b (M.haltNorm).step (M.haltNorm).start L Z c hc x m hm hx
    hpre hpost hb r hpass
  have hmid : (simObs q b (M.haltNorm)).run r.steps
      (Config.mk (embO q b (passStart x m c hm hc Z L).state)
        (passStart x m c hm hc Z L).tape) =
      Config.mk (embO q b (passEnd r).state) (passEnd r).tape := by
    rw [hdele, hpe]
  -- 预算拆成「通路步数 + 余下步数」，后半段从 `passEnd` 出发必然不落 `obsAcc`
  rw [show budget = r.steps + (budget - r.steps) from by omega, DTM.run_add, hmid]
  exact simObs_no_accept_budget_of_passEnd_halt q b M r hxacc hpk (budget - r.steps)
    (by omega) (budget - r.steps) (Nat.le_refl _)

/-- **通路失败的位置分解**：`passRun` 返回 `none` 时，存在一个成功前缀 `L1`（终态 `r1`），
    其后的下一块处查表失败或移动越界（越界在两侧预留空白时不会发生）。
    Decomposition of a failing pass: a successful prefix followed by a failing round. -/
theorem passRun_none_decomp (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b),
      passRun q b tab Z c hc x L hb = none →
      ∃ (L1 : List Nat) (r1 : PassRes q b) (k : Nat) (ks : List Nat),
        L = L1 ++ (k :: ks) ∧
        (∃ hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b, passRun q b tab Z c hc x L1 hb1 = some r1) ∧
        (pick (tab r1.reg.state r1.reg.cur) r1.c = none ∨
          (∃ (m' : Fin q) (s' : Sym), pick (tab r1.reg.state r1.reg.cur) r1.c
              = some (m', s', Dir.right) ∧ r1.reg.post = []) ∨
          (∃ (m' : Fin q) (s' : Sym), pick (tab r1.reg.state r1.reg.cur) r1.c
              = some (m', s', Dir.left) ∧ r1.reg.pre = [])) := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x hb hpass
      simp only [passRun] at hpass
      cases hpass
  | cons k ks ih =>
      intro Z c hc x hb hpass
      have hkb : k + 2 < 2 ^ b := hb k (List.mem_cons_self ..)
      have hcK : k + 1 < 2 ^ b := by omega
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (List.mem_cons_of_mem _ hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          refine ⟨[], ⟨0, Z, c, hc, x⟩, k, ks, by simp only [List.nil_append], ?_, Or.inl hpk⟩
          exact ⟨fun k' hk' => by simp at hk', rfl⟩
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                  { state := m', pre := x.pre, cur := s', post := x.post } ks hb' with
              | some r0 => rw [hrec] at hpass; cases hpass
              | none =>
                  obtain ⟨L1, r1, k', ks', hL, ⟨hb1, hp1⟩, hfail⟩ :=
                    ih (Z + k + 3) (k + 1) hcK
                      { state := m', pre := x.pre, cur := s', post := x.post } hb' hrec
                  -- 前缀补上一块 `k`：映射只改步数，`reg`/`c` 不变，失败条件照搬
                  have hbpre : ∀ k'' ∈ k :: L1, k'' + 2 < 2 ^ b := by
                    intro k'' hk''
                    rcases List.mem_cons.mp hk'' with rfl | hk''
                    · exact hkb
                    · exact hb k'' (by
                        rw [show k :: ks = k :: (L1 ++ (k' :: ks')) from by rw [← hL]]
                        exact List.mem_cons_of_mem _ (List.mem_append_left _ hk''))
                  refine ⟨k :: L1,
                    ⟨roundCostStay (q := q) x Z k s' + r1.steps, r1.z, r1.c, r1.hc, r1.reg⟩,
                    k', ks', ?_, ?_, ?_⟩
                  · rw [hL]; simp only [List.cons_append]
                  · refine ⟨hbpre, ?_⟩
                    rw [passRun_stay_unfold q b tab Z c hc x k L1 hbpre m' s' hpk]
                    have hp2 : passRun q b tab (Z + k + 3) (k + 1) hcK
                        { state := m', pre := x.pre, cur := s', post := x.post } L1
                        (fun k'' hk'' => hbpre k'' (List.mem_cons_of_mem _ hk'')) = some r1 := by
                      exact hp1
                    rw [hp2, Option.map_some]
                  · simpa only using hfail
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  refine ⟨[], ⟨0, Z, c, hc, x⟩, k, ks, by simp only [List.nil_append], ?_,
                    Or.inr (Or.inl ⟨m', s', hpk, hpost0⟩)⟩
                  exact ⟨fun k' hk' => by simp at hk', rfl⟩
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      ks hb' with
                  | some r0 => rw [hrec] at hpass; cases hpass
                  | none =>
                      obtain ⟨L1, r1, k', ks', hL, ⟨hb1, hp1⟩, hfail⟩ :=
                        ih (Z + k + 3) (k + 1) hcK
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                          hb' hrec
                      have hbpre : ∀ k'' ∈ k :: L1, k'' + 2 < 2 ^ b := by
                        intro k'' hk''
                        rcases List.mem_cons.mp hk'' with rfl | hk''
                        · exact hkb
                        · exact hb k'' (by
                            rw [show k :: ks = k :: (L1 ++ (k' :: ks')) from by rw [← hL]]
                            exact List.mem_cons_of_mem _ (List.mem_append_left _ hk''))
                      refine ⟨k :: L1,
                        ⟨roundCostRight (q := q) x Z k p s' + r1.steps, r1.z, r1.c, r1.hc,
                          r1.reg⟩, k', ks', ?_, ?_, ?_⟩
                      · rw [hL]; simp only [List.cons_append]
                      · refine ⟨hbpre, ?_⟩
                        rw [passRun_right_unfold q b tab Z c hc x k L1 hbpre m' s' p post' hpost0
                          hpk]
                        have hp2 : passRun q b tab (Z + k + 3) (k + 1) hcK
                            { state := m', pre := x.pre ++ [(s', false)], cur := p.1,
                              post := post' } L1
                            (fun k'' hk'' => hbpre k'' (List.mem_cons_of_mem _ hk''))
                            = some r1 := by
                          exact hp1
                        rw [hp2, Option.map_some]
                      · simpa only using hfail
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  have hpre0 : x.pre = [] := by
                    rw [← List.reverse_reverse x.pre, hrev]; rfl
                  refine ⟨[], ⟨0, Z, c, hc, x⟩, k, ks, by simp only [List.nil_append], ?_,
                    Or.inr (Or.inr ⟨m', s', hpk, hpre0⟩)⟩
                  exact ⟨fun k' hk' => by simp at hk', rfl⟩
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                      (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) ks hb' with
                  | some r0 => rw [hrec] at hpass; cases hpass
                  | none =>
                      obtain ⟨L1, r1, k', ks', hL, ⟨hb1, hp1⟩, hfail⟩ :=
                        ih (Z + k + 3) (k + 1) hcK
                          (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) hb' hrec
                      have hbpre : ∀ k'' ∈ k :: L1, k'' + 2 < 2 ^ b := by
                        intro k'' hk''
                        rcases List.mem_cons.mp hk'' with rfl | hk''
                        · exact hkb
                        · exact hb k'' (by
                            rw [show k :: ks = k :: (L1 ++ (k' :: ks')) from by rw [← hL]]
                            exact List.mem_cons_of_mem _ (List.mem_append_left _ hk''))
                      refine ⟨k :: L1,
                        ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r1.steps,
                          r1.z, r1.c, r1.hc, r1.reg⟩, k', ks', ?_, ?_, ?_⟩
                      · rw [hL]; simp only [List.cons_append]
                      · refine ⟨hbpre, ?_⟩
                        rw [passRun_left_unfold q b tab Z c hc x k L1 hbpre m' s' cq preRev hrev
                          hpk]
                        have hp2 : passRun q b tab (Z + k + 3) (k + 1) hcK
                            (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) L1
                            (fun k'' hk'' => hbpre k'' (List.mem_cons_of_mem _ hk''))
                            = some r1 := by
                          exact hp1
                        rw [hp2, Option.map_some]
                      · simpa only using hfail

/-- 失败哨兵与接受哨兵不同。 -/
theorem obsFail_ne_obsAcc (q b : Nat) : obsFail q b ≠ obsAcc q b := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [obsFail, obsAcc, Fin.val_mk] at hv
  omega

/-- **前缀成功 + 下一轮查表失败 ⇒ 预算内不误接受**：前 `|L1|` 块的通路成功、沿途内部
    状态非接受，随后当前选择查表失败（停机拒绝态），则观察机跑满预算后仍不在 `obsAcc`。
    这是拒绝方向「分支中途死亡」情形的判据（停机拒绝态正是 passRun 在下一轮返回 none 的原因）。
    A successful prefix followed by a failed lookup never accepts within the budget. -/
theorem simObs_no_acc_budget_of_prefix_fail (q b : Nat) (M : NTM q)
    (L1 L2 : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L1, k' + 2 < 2 ^ b)
    (r1 : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L1 hb = some r1)
    (hnoacc : ∀ i : Nat, i < r1.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z (L1 ++ L2))).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z (L1 ++ L2))).state.val ≠ (M.haltNorm).accept.val)
    (hxacc : r1.reg.state ≠ (M.haltNorm).accept)
    (hpk : pick ((M.haltNorm).step r1.reg.state r1.reg.cur) r1.c = none)
    (budget : Nat) (hbud : r1.steps + 6 ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
        (Config.mk (embO q b (passStart x m c hm hc Z (L1 ++ L2)).state)
          (passStart x m c hm hc Z (L1 ++ L2)).tape)).state ≠ obsAcc q b := by
  -- 前缀结束后驱动层正好停在下一轮的起点
  have hprefix := simDrive_pass_prefix q b (M.haltNorm).step (M.haltNorm).start L1 L2 Z c
    hc x m hm hx hpre hpost hb r1 hpass
  -- 前缀内每一步都可观察（范围 + 非接受 + 非相位 14，后者与终点相位 0 矛盾）
  have hobs : ∀ i, i < r1.steps → observeState q b (M.haltNorm)
      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
        (passStart x m c hm hc Z (L1 ++ L2))).state := by
    intro i hi
    constructor
    · have h0 : (passStart x m c hm hc Z (L1 ++ L2)).state.val < 2 * stateCount q b := by
        have := passStart_state_lt q b x m c hm hc Z (L1 ++ L2)
        omega
      exact simDrive_run_range q b (M.haltNorm).step (M.haltNorm).start i _ h0
    · intro hlt
      refine ⟨hnoacc i hi hlt, ?_⟩
      intro h14
      have hstuck := simDrive_run_phase14_state q b (M.haltNorm).step (M.haltNorm).start
        (passStart x m c hm hc Z (L1 ++ L2)) ⟨_, hlt⟩ i rfl h14 (r1.steps - i)
      rw [show i + (r1.steps - i) = r1.steps from by omega, hprefix] at hstuck
      have hp0 : unpackPh (2 ^ b) 9 15
          (passStart r1.reg r1.reg.state.val r1.c r1.reg.state.isLt r1.hc r1.z L2).state.val
          = 0 := by
        simp only [passStart, Config.state, embS, Fin.val_mk]
        rw [codeState_unpackPh q b r1.reg.state.val r1.c 0 0 r1.reg.state.isLt r1.hc
          (by decide) (by decide)]
      rw [hstuck] at hp0
      simp only [embS, Fin.val_mk] at hp0
      rw [h14] at hp0
      omega
  -- 观察投影：`r1.steps` 步后正是下一轮起点
  have hmid : (simObs q b (M.haltNorm)).run r1.steps
      (Config.mk (embO q b (passStart x m c hm hc Z (L1 ++ L2)).state)
        (passStart x m c hm hc Z (L1 ++ L2)).tape) =
      Config.mk (embO q b (passStart r1.reg r1.reg.state.val r1.c r1.reg.state.isLt
          r1.hc r1.z L2).state)
        (passStart r1.reg r1.reg.state.val r1.c r1.reg.state.isLt r1.hc r1.z L2).tape := by
    rw [simObs_run_delegate q b (M.haltNorm) r1.steps
      (passStart x m c hm hc Z (L1 ++ L2)) hobs, hprefix]
  -- 再 6 步：查表失败 ⇒ `obsFail`
  have hfail : ((simObs q b (M.haltNorm)).run (r1.steps + 6)
      (Config.mk (embO q b (passStart x m c hm hc Z (L1 ++ L2)).state)
        (passStart x m c hm hc Z (L1 ++ L2)).tape)).state = obsFail q b := by
    rw [DTM.run_add, hmid]
    exact simObs_run6_fail_of_lookup_none q b (M.haltNorm) r1.reg.state.val r1.c
      r1.reg.state.isLt r1.hc r1.reg rfl hxacc hpk
      (none :: List.replicate r1.z (some false) ++ digitArea L2)
  -- 失败哨兵保持到预算末端
  intro hhit
  rw [show budget = (r1.steps + 6) + (budget - r1.steps - 6) from by omega] at hhit
  rw [simObs_run_fail_persists q b (M.haltNorm) (r1.steps + 6)
    (budget - r1.steps - 6)
    (Config.mk (embO q b (passStart x m c hm hc Z (L1 ++ L2)).state)
      (passStart x m c hm hc Z (L1 ++ L2)).tape) hfail] at hhit
  exact obsFail_ne_obsAcc q b hhit

/-- **单分支接受判定的预算版**：成功通路、终态接受、`|L| ≤ T`、`|pre| ≤ T`、`Z ≤ T`
    ⇒ 观察机从分支起点跑满 `BUDGET = 2^((2·2^b+42)·T)` 步后停在 `obsAcc`。
    Budgeted accept verdict for one branch, the form the enumerator's per-branch step uses. -/
theorem obsAcc_at_budget_of_passRun_accept (q b T : Nat) (M : NTM q)
    (L : List Nat) (hLne : L ≠ []) (hL : L.length ≤ T)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre' : ∀ p0 ∈ x.pre, p0.2 = false) (hpost' : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpre : x.pre.length ≤ T) (hZ : Z ≤ T)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hracc : r.reg.state = (M.haltNorm).accept) :
    ((simObs q b (M.haltNorm)).run (2 ^ ((2 * 2 ^ b + 42) * T))
      (obsStart q b M x m c Z hm hc L)).state = obsAcc q b := by
  -- 观察机在 `r.steps` 内命中接受哨兵
  obtain ⟨n, hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b M L hLne Z c hc x m hm hx hpre' hpost' hb r hpass hracc
  -- 单分支步数 ≤ 统一预算
  have hstep : r.steps ≤ 2 ^ ((2 * 2 ^ b + 42) * T) :=
    passRun_steps_le_two_pow_T q b T (M.haltNorm).step Z c hc x L hb hpre hZ hL r hpass
  exact simObs_run_accept_at_budget q b (M.haltNorm) n (2 ^ ((2 * 2 ^ b + 42) * T))
    (obsStart q b M x m c Z hm hc L) (Nat.le_trans hn hstep) hhit

/-- **枚举器接受完备性（预算版）**：若 `M` 在 `T` 步内接受 `w`，模拟区起点 `x` 与
    `M.init w` 逐字一致、两侧空白恰为 `T`、起点非接受态，则存在一条选择列表 `L`，
    使观察机从分支起点跑满 `BUDGET = 2^((2·2^b+42)·T)` 步后停在 `obsAcc`。
    Enumerator accept-completeness at the budget: `M` accepting `w` implies the observer,
    started at the branch's region and run for the full budget, lands on `obsAcc`. -/
theorem obsAcc_budget_enumerates_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T : Nat) (b : Nat) (hbnd : B + 2 < 2 ^ b)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hpre : x.pre.length ≤ T) (hZ : Z ≤ T)
    (hacc : M.AcceptsWithin w T) :
    ∃ (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (c : Nat) (hc : c < 2 ^ b),
      ((simObs q b (M.stutter.haltNorm)).run (2 ^ ((2 * 2 ^ b + 42) * T))
        (obsStart q b (M.stutter) x x.state.val c Z x.state.isLt hc L)).state
        = obsAcc q b := by
  -- 带长度界的接受通路：`|L| ≤ T`
  obtain ⟨L, hb, c, hc, r, hpass, hracc, hLlen⟩ :=
    exists_passRun_accept_of_acceptsWithin_len M hB hBpos w T b hbnd Z x hx hxw hd1 hd2 hacc
  -- 通路数字列表非空（否则起点即接受态）
  have hLne : L ≠ [] := by
    intro hL
    subst hL
    rw [show passRun q b (M.stutter.haltNorm).step Z c hc x [] hb
          = some ⟨0, Z, c, hc, x⟩ from rfl] at hpass
    have hr : (⟨0, Z, c, hc, x⟩ : PassRes q b) = r := Option.some.inj hpass
    have hregx : r.reg = x := by rw [← hr]
    exact hxacc (by rw [← hregx]; exact hracc)
  exact ⟨L, hb, c, hc,
    obsAcc_at_budget_of_passRun_accept q b T (M.stutter) L hLne hLlen Z c hc x
      x.state.val x.state.isLt rfl hx.1 hx.2 hb hpre hZ r hpass hracc⟩

end DTM

end Pnp
