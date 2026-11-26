/-
  文件：Pnp/Machine/BranchEntry.lean
  File: Pnp/Machine/BranchEntry.lean

  主题：E 机**逐分支入口的「哑元首轮」**——观察机从自己的起始态（计数器 `c = 0`）出发，
  第一个选择 `0` 在占位机 `M.stutter` 里正是「空转」转移，于是首轮不改变区域，
  只把计数器设成数字区首块的值 + 1（= `seqHead`），此后各轮与「直接从 `passStart`
  （`c = seqHead`）出发」完全相同。
  Topic: the dummy first round at the per-branch entry. The observer starts in its own start
  state (counter `c = 0`); choice `0` is the stutter machine's no-op, so the first round only
  sets the counter from the first digit block (`seqHead`), and the rest of the pass coincides
  with a `passStart` pass.

  为什么需要：`passStart` 的起点状态带 `c = seqHead`（分支首轮的选号来自状态），
  而一台固定控制表的机器无法「按输入设置状态」；`M.stutter` 的索引 0 空转正好补上这一轮，
  使机器可以从 `simDrive` 的起始态（`c = 0`）直接起跑。
  Why: `passStart` carries `c = seqHead` inside the control state, which a fixed transition
  table cannot synthesize from the input; stutter's index-0 no-op supplies the missing round.

  本文件给出三块：
    - `pick_haltNorm_stutter_zero`：占位机索引 0 的取值；
    - `Reg.step_zero_dummy` / `stepCs_dummy_cons`：语义层「哑元不改变后续选择」；
    - `simDrive_dummy_round`：驱动层一整轮（`passStart` 形，`c` 从 0 变 `k + 1`）。
  Three pieces: the index-0 value, the semantic no-op, and the driving-layer dummy round.
-/

import Pnp.Machine.SimPass
import Pnp.Machine.Stutter
import Pnp.Machine.PadBranch
import Pnp.Machine.SimHitComplete
import Pnp.Machine.ObsBudget
import Pnp.Machine.BranchPhase
import Pnp.Machine.PassZShift
import Pnp.Machine.BranchAccept
import Pnp.Machine.BranchReject
import Pnp.Machine.SimExpBound

namespace Pnp

namespace NTM

/-- **占位机索引 0 = 空转**：状态既不接受也不拒绝时，`(M.stutter).haltNorm` 在该状态的第一条
    候选就是 `(s, a, Dir.stay)`，故 `pick … 0` 取到空转。
    Index 0 of the stutter machine is the no-op transition. -/
theorem pick_haltNorm_stutter_zero {q : Nat} (M : NTM q) (s : Fin q) (a : Sym)
    (h : ¬(s = M.accept ∨ s = M.reject)) :
    pick ((((M.stutter).haltNorm).step) s a) 0 = some (s, a, Dir.stay) := by
  have hstep : ((M.stutter).haltNorm).step s a = (s, a, Dir.stay) :: M.step s a := by
    simp only [haltNorm, h, ite_false, stutter]
  rw [hstep]
  rfl

end NTM

namespace DTM

/-- **空转一步不改变区域**：`pick` 取到 `(x.state, x.cur, stay)` 时，`Reg.step` 原地不动。
    A no-op transition leaves the register unchanged. -/
theorem Reg.step_zero_dummy {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (x : Reg q) (h0 : pick (tab x.state x.cur) 0 = some (x.state, x.cur, Dir.stay)) :
    Reg.step tab 0 x = some x := by
  simp only [Reg.step, h0]

/-- **语义层：哑元首项不改变后续迭代**（选择序列开头的 `0` 是空转，可直接删去）。
    Semantics: a leading dummy choice can be dropped from the iterated region steps. -/
theorem stepCs_dummy_cons {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (x : Reg q) (ks : List Nat)
    (h0 : pick (tab x.state x.cur) 0 = some (x.state, x.cur, Dir.stay)) :
    stepCs tab (0 :: ks) x = stepCs tab ks x := by
  simp only [stepCs, Reg.step_zero_dummy tab x h0]
  rfl

/-- **驱动层：哑元首轮**。从 `passStart`（计数器 `c = 0`）出发跑一轮后，区域原样不变，
    零计数增加 `k + 3`，计数器变成 `k + 1`（= 数字区首块的选号 `seqHead`）。
    Driving layer: the dummy round keeps the region, grows the zero count, and sets the
    counter to `k + 1` (= `seqHead` of the first digit block). -/
theorem simDrive_dummy_round (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (x : Reg q) (z k : Nat) (hc0 : 0 < 2 ^ b)
    (hK : k + 2 < 2 ^ b) (hpre : ∀ p ∈ x.pre, p.2 = false)
    (hx0 : pick (tab x.state x.cur) 0 = some (x.state, x.cur, Dir.stay))
    (ks : List Nat) :
    (simDrive q b tab s0).run (roundCostStay x z k x.cur)
      (passStart x x.state.val 0 x.state.isLt hc0 z (k :: ks)) =
    passStart x x.state.val (k + 1) x.state.isLt (by omega) (z + k + 3) ks := by
  have hx : x.state = (⟨x.state.val, x.state.isLt⟩ : Fin q) := rfl
  have hk := hx0
  obtain ⟨xc, X', htail⟩ := digitArea_split ks
  have hround := simDrive_roundCanon_stay q b tab s0 x.state.val 0 x.state.isLt hc0
    x z k (k + 2) hK rfl xc X' (digitArea_head_ne_true ks xc X' htail) hpre
    x.state x.cur hx hk ks htail
  -- 区域 `{x with state := x.state, cur := x.cur}` 就是 `x` 本身
  simpa using hround

/-- **观察机起点就是「计数器 0」的通路起点**：`simObs` 从自己的起始态起跑，等价于从
    `passStart x M.start.val 0 …` 起跑（前提 `x.state = M.start`）。
    The observer's start state is the counter-0 pass start.
    （`x` 只用于给出 `passStart` 的区域参数，起点状态与区域的其它字段无关。）
    `x` only supplies `passStart`'s region parameter; the state does not depend on it. -/
theorem simObs_start_eq_passStart {q b : Nat} (M : NTM q) (hc0 : 0 < 2 ^ b)
    (x : Reg q) (Z : Nat) (ks : List Nat) :
    (simObs q b M).start =
      embO q b (passStart x M.start.val 0 M.start.isLt hc0 Z ks).state := by
  apply Fin.ext
  simp only [simObs, simStep, simDrive, embO, embS, passStart, codeState_val, Fin.val_mk]

/-- **哑元首轮 + 通路（驱动层整段）**：从「计数器 0」的通路起点出发，先跑哑元首轮
    （把计数器设成 `k + 1`），再按剩余数字区 `ks` 跑完通路。
    Dummy first round followed by the pass over the remaining digit area. -/
theorem simDrive_pass_dummy (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (ks : List Nat) (Z k : Nat) (hc0 : 0 < 2 ^ b)
    (x : Reg q) (hpre : ∀ p ∈ x.pre, p.2 = false)
    (hpost : ∀ p ∈ x.post, p.2 = false)
    (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b) (hk : k + 2 < 2 ^ b)
    (hx0 : pick (tab x.state x.cur) 0 = some (x.state, x.cur, Dir.stay))
    (r : PassRes q b) (hpass : passRun q b tab (Z + k + 3) (k + 1) (by omega) x ks hb = some r) :
    (simDrive q b tab s0).run (roundCostStay x Z k x.cur + r.steps)
      (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks)) = passEnd r := by
  rw [DTM.run_add]
  rw [simDrive_dummy_round q b tab s0 x Z k hc0 hk hpre hx0 ks]
  exact simDrive_pass q b tab s0 ks (Z + k + 3) (k + 1) (by omega) x x.state.val
    x.state.isLt rfl hpre hpost hb r hpass

/-- **分支命中（机器自身起点版）**：通路以 `c = 0` 起跑并停在接受态 ⇒ 观察机从**自己的
    起始态**出发（而非从 `passStart` 的格局出发），在 `r.steps` 步内命中接受哨兵。
    Hit lemma from the machine's own start state (counter 0). -/
theorem exists_obs_acc_of_passRun_accept_start {q b : Nat} (M : NTM q) (L : List Nat)
    (hL : L ≠ []) (Z : Nat) (x : Reg q) (hx : x.state = M.start)
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (hc0 : 0 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z 0 hc0 x L hb = some r)
    (hacc : r.reg.state = (M.haltNorm).accept) :
    ∃ n, n ≤ r.steps ∧
      ((simObs q b (M.haltNorm)).run n
        ⟨(simObs q b (M.haltNorm)).start,
          x.enc (none :: List.replicate Z (some false) ++ digitArea L)⟩).state
        = obsAcc q b := by
  obtain ⟨n, hn, h⟩ := exists_obs_acc_of_passRun_accept q b M L hL Z 0 hc0 x M.start.val
    M.start.isLt (by rw [← hx]) hpre hpost hb r hpass hacc
  have hcfg : obsStart q b M x M.start.val 0 Z M.start.isLt hc0 L
      = Config.mk (simObs q b (M.haltNorm)).start
          (x.enc (none :: List.replicate Z (some false) ++ digitArea L)) :=
    (Config.mk.injEq _ _ _ _).mpr
      ⟨(simObs_start_eq_passStart (M.haltNorm) hc0 x Z L).symm, rfl⟩
  rw [hcfg] at h
  exact ⟨n, hn, h⟩

/-- **运行相位机的起点 = `obsStart`（`c = 0`）状态**：两者只差一层 `embOb`，故从机器自身起点
    出发的运行与从 `obsStart` 格局出发的运行逐字一致（同一纸带时）。
    The phase machine's start state is the counter-0 `obsStart` state. -/
theorem obsPhase_start_eq_embOb_obsStart (q b : Nat) (M : NTM q) (hc0 : 0 < 2 ^ b)
    (x : Reg q) (Z : Nat) (L : List Nat) :
    (obsPhase q b (M.haltNorm)).start
      = embOb q b (obsStart q b M x M.start.val 0 Z M.start.isLt hc0 L).state := by
  show embOb q b (simObs q b (M.haltNorm)).start
    = embOb q b (obsStart q b M x M.start.val 0 Z M.start.isLt hc0 L).state
  rw [simObs_start_eq_passStart (M.haltNorm) hc0 x Z L]
  rfl

/-- **分支接受（机器自身起点 + 统一预算）**：通路以 `c = 0` 起跑并停在接受态 ⇒ 运行相位机
    从**自己的起始态**出发，在统一预算 `2^((2·2^b+42)·T)` 内停在接受态。
    Accepting branch from the machine's own start at the uniform budget. -/
theorem obsPhase_accepts_at_budget_of_passRun_accept_start (q b T : Nat) (M : NTM q)
    (L : List Nat) (hLne : L ≠ []) (hL : L.length ≤ T)
    (Z : Nat) (x : Reg q) (hx : x.state = M.start)
    (hpre' : ∀ p0 ∈ x.pre, p0.2 = false) (hpost' : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (hc0 : 0 < 2 ^ b)
    (hpre : x.pre.length ≤ T) (hZ : Z ≤ T)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z 0 hc0 x L hb = some r)
    (hracc : r.reg.state = (M.haltNorm).accept) :
    ((obsPhase q b (M.haltNorm)).run (2 ^ ((2 * 2 ^ b + 42) * T))
        ⟨(obsPhase q b (M.haltNorm)).start,
          x.enc (none :: List.replicate Z (some false) ++ digitArea L)⟩).state
      = (obsPhase q b (M.haltNorm)).accept := by
  have h := obsPhase_accepts_at_budget_of_passRun_accept q b T M L hLne hL Z 0 hc0 x
    M.start.val M.start.isLt (by rw [← hx]) hpre' hpost' hb hpre hZ r hpass hracc
  have hcfg : Config.mk (embOb q b (obsStart q b M x M.start.val 0 Z M.start.isLt hc0 L).state)
        (obsStart q b M x M.start.val 0 Z M.start.isLt hc0 L).tape
      = Config.mk (obsPhase q b (M.haltNorm)).start
          (x.enc (none :: List.replicate Z (some false) ++ digitArea L)) :=
    (Config.mk.injEq _ _ _ _).mpr
      ⟨(obsPhase_start_eq_embOb_obsStart q b M hc0 x Z L).symm, rfl⟩
  rw [hcfg] at h
  exact h

/-- **观察机的哑元前缀**：从观察机**自身起始态**（计数器 0）出发跑一个哑元首轮，落到
    「计数器 `k + 1`、零计数 `+k+3`」的通路起点格局（与 `simDrive_dummy_round` 一致）。
    可观察性照 `SimBudget` 的三件套路：范围界 / 沿途非接受（哑元轮内 `m` 恒为 `x.state`）/
    相位 14 与终点相位 0 矛盾。
    The observer's dummy prefix: from its own start state, one dummy round lands exactly on the
    counter-`k+1` pass start. Observability: range, non-acceptance, and phase 14 contradiction. -/
theorem simObs_dummy_prefix (q b : Nat) (M : NTM q) (x : Reg q) (Z k : Nat)
    (hc0 : 0 < 2 ^ b) (hK : k + 2 < 2 ^ b)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (hxs : x.state = M.start) (hxne : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (ks : List Nat) :
    (simObs q b ((M.stutter).haltNorm)).run (roundCostStay x Z k x.cur)
      ⟨(simObs q b ((M.stutter).haltNorm)).start,
        x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))⟩
      = Config.mk (embO q b (passStart x x.state.val (k + 1) x.state.isLt (show k + 1 < 2 ^ b from by omega)
            (Z + k + 3) ks).state)
          (passStart x x.state.val (k + 1) x.state.isLt (show k + 1 < 2 ^ b from by omega) (Z + k + 3) ks).tape := by
  -- 哑元轮的起点格局（驱动层）
  have hval : x.state.val = ((M.stutter).haltNorm).start.val := by
    rw [hxs]
    rfl
  have hstart : (simObs q b ((M.stutter).haltNorm)).start
      = embO q b (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks)).state := by
    rw [simObs_start_eq_passStart ((M.stutter).haltNorm) hc0 x Z (k :: ks)]
    apply Fin.ext
    simp only [embO, embS, Fin.val_mk, passStart, codeState_val, hval]
  -- 哑元轮的转移：`pick … 0` 是空转
  have hx0 : pick (((M.stutter).haltNorm).step x.state x.cur) 0
      = some (x.state, x.cur, Dir.stay) :=
    NTM.pick_haltNorm_stutter_zero M x.state x.cur (by
      intro h
      rcases h with h | h
      · exact hxne h
      · exact hxre h)
  obtain ⟨xc, X', htail⟩ := digitArea_split ks
  have hxc : xc ≠ some true := digitArea_head_ne_true ks xc X' htail
  -- 可观察性
  have hobs : ∀ i, i < roundCostStay x Z k x.cur →
      observeState q b ((M.stutter).haltNorm)
        ((simDrive q b ((M.stutter).haltNorm).step ((M.stutter).haltNorm).start).run i
          (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks))).state := by
    intro i hi
    constructor
    · have h0 : (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks)).state.val
          < 2 * stateCount q b := by
        have := passStart_state_lt q b x x.state.val 0 x.state.isLt hc0 Z (k :: ks)
        omega
      exact simDrive_run_range q b _ _ i _ h0
    · intro hlt
      constructor
      · -- 沿途非接受：哑元轮内 `m` 恒为 `x.state.val`
        intro hacc
        have hm := simDrive_passStart_roundM_stay q b ((M.stutter).haltNorm).step
          ((M.stutter).haltNorm).start x x.state.val 0 x.state.isLt hc0 Z k ks xc X' htail
          hK hxc hpre x.state x.cur rfl hx0 i (Nat.le_of_lt hi) hlt
        rcases hm with hm | hm
        · exact hxne (Fin.ext (by rw [← hm]; exact hacc))
        · exact hxne (Fin.ext (by rw [← hm]; exact hacc))
      · -- 相位 14 与终点相位 0 矛盾
        intro h14
        have hstuck := simDrive_run_phase14_state q b ((M.stutter).haltNorm).step
          ((M.stutter).haltNorm).start (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks))
          ⟨_, hlt⟩ i rfl h14 (roundCostStay x Z k x.cur - i)
        rw [show i + (roundCostStay x Z k x.cur - i) = roundCostStay x Z k x.cur from
            Nat.add_sub_cancel' (Nat.le_of_lt hi),
          simDrive_dummy_round q b ((M.stutter).haltNorm).step ((M.stutter).haltNorm).start
            x Z k hc0 hK hpre hx0 ks] at hstuck
        have hp0 : unpackPh (2 ^ b) 9 15
            (passStart x x.state.val (k + 1) x.state.isLt (show k + 1 < 2 ^ b from by omega) (Z + k + 3) ks).state.val
            = 0 := by
          simp only [passStart, embS, Fin.val_mk]
          rw [codeState_unpackPh q b x.state.val (k + 1) 0 0 x.state.isLt (by omega)
            (by decide) (by decide)]
        rw [hstuck] at hp0
        simp only [embS, Fin.val_mk] at hp0
        rw [h14] at hp0
        omega
  -- 观察投影：`d` 步后正是通路起点格局
  have hdele := simObs_run_delegate q b ((M.stutter).haltNorm)
    (roundCostStay x Z k x.cur)
    (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks)) hobs
  -- `rw` 不会把 `(passStart …).tape` 归约成 `x.enc …`，先手动换形
  have htp : (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks)).tape
      = x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks)) := rfl
  rw [htp] at hdele
  rw [hstart, hdele]
  -- 把哑元轮的结论抬到 `Config.mk (embO …)` 包装上
  have hl : Config.mk
        (embO q b ((simDrive q b ((M.stutter).haltNorm).step
          ((M.stutter).haltNorm).start).run (roundCostStay x Z k x.cur)
          (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks))).state)
        ((simDrive q b ((M.stutter).haltNorm).step
          ((M.stutter).haltNorm).start).run (roundCostStay x Z k x.cur)
          (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks))).tape
      = Config.mk (embO q b (passStart x x.state.val (k + 1) x.state.isLt
          (show k + 1 < 2 ^ b from by omega) (Z + k + 3) ks).state)
        (passStart x x.state.val (k + 1) x.state.isLt
          (show k + 1 < 2 ^ b from by omega) (Z + k + 3) ks).tape := by
    rw [simDrive_dummy_round q b ((M.stutter).haltNorm).step
      ((M.stutter).haltNorm).start x Z k hc0 hK hpre hx0 ks]
  exact hl

/-- **哑元前缀的命中平移**：若某分支在「计数器 `k + 1`、数字区 `ks`」的起点上于 `n` 步内
    命中接受哨兵，则观察机从自身起始态（计数器 0、数字区 `k :: ks`）出发，在
    `roundCostStay x Z k x.cur + n` 步内同样命中。
    Hit shift across the dummy prefix. -/
theorem exists_obs_acc_of_dummy_prefix (q b : Nat) (M : NTM q) (x : Reg q) (Z k : Nat)
    (hc0 : 0 < 2 ^ b) (hK : k + 2 < 2 ^ b) (hpre : ∀ p ∈ x.pre, p.2 = false)
    (hxs : x.state = M.start) (hxne : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (ks : List Nat) (hc : k + 1 < 2 ^ b) (n : Nat)
    (h : ((simObs q b ((M.stutter).haltNorm)).run n
        (obsStart q b (M.stutter) x x.state.val (k + 1) (Z + k + 3) x.state.isLt hc
          ks)).state = obsAcc q b) :
    ∃ n', n' ≤ roundCostStay x Z k x.cur + n ∧
      ((simObs q b ((M.stutter).haltNorm)).run n'
        ⟨(simObs q b ((M.stutter).haltNorm)).start,
          x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))⟩).state
        = obsAcc q b := by
  refine ⟨roundCostStay x Z k x.cur + n, Nat.le_refl _, ?_⟩
  rw [DTM.run_add]
  rw [simObs_dummy_prefix q b M x Z k hc0 hK hpre hxs hxne hxre ks]
  exact h

/-- **哑元前缀的预算平移（运行相位机）**：分支族成员在「计数器 `k + 1`」起点的接受，
    可直接搬到观察机自身起点（计数器 0、数字区 `k :: ks`），预算多加一个哑元轮成本。
    Budget shift across the dummy prefix for the run-phase machine. -/
theorem obsPhase_accepts_at_budget_of_obsStart_branch (q b : Nat) (M : NTM q) (x : Reg q)
    (Z k n budget : Nat) (hc0 : 0 < 2 ^ b) (hK : k + 2 < 2 ^ b)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (hxs : x.state = M.start) (hxne : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (ks : List Nat) (hc : k + 1 < 2 ^ b)
    (hn : roundCostStay x Z k x.cur + n ≤ budget)
    (h : ((obsPhase q b ((M.stutter).haltNorm)).run n
        ⟨embOb q b (obsStart q b (M.stutter) x x.state.val (k + 1) (Z + k + 3)
            x.state.isLt hc ks).state,
          (obsStart q b (M.stutter) x x.state.val (k + 1) (Z + k + 3)
            x.state.isLt hc ks).tape⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept) :
    ((obsPhase q b ((M.stutter).haltNorm)).run budget
        ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
          x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))⟩).state
        = (obsPhase q b ((M.stutter).haltNorm)).accept := by
  -- 分支族的接受 ⇔ 观察机命中
  have hS : ((simObs q b ((M.stutter).haltNorm)).run n
      (obsStart q b (M.stutter) x x.state.val (k + 1) (Z + k + 3) x.state.isLt hc ks)).state
      = obsAcc q b :=
    (obsPhase_accept_iff q b ((M.stutter).haltNorm) n _).mp h
  -- 把命中平移到机器自身起点
  obtain ⟨n', hn', hhit⟩ :=
    exists_obs_acc_of_dummy_prefix q b M x Z k hc0 hK hpre hxs hxne hxre ks hc n hS
  -- 命中 ⇒ 运行相位机在 `n'` 步接受，再延长到预算 `budget`
  have hph := obsPhase_budget_accept q b ((M.stutter).haltNorm) n'
    ⟨(simObs q b ((M.stutter).haltNorm)).start,
      x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))⟩ hhit
  exact obsPhase_accept_mono q b ((M.stutter).haltNorm) n' budget
    ⟨(simObs q b ((M.stutter).haltNorm)).start,
      x.enc (none :: List.replicate Z (some false) ++ digitArea (k :: ks))⟩
    (Nat.le_trans hn' hn) (by simpa [obsPhase] using congrArg Config.state hph)

/-- **分支族完备性的「哑元入口」版**：原机在 `T` 步内接受 ⇒ 存在分支 `(t, i)`，使观察机从
    **自身起始态**（计数器 0）出发、在数字区 `seqHead :: branchBlocks` 上运行
    「一个哑元轮 + 指数预算」步后命中接受哨兵。
    做法：通路在 `Z` 上成功（完备性）→ 平移到哑元轮的零计数 `Z + seqHead + 3`
    （`passRun_z_shift`）→ 观察机在 `r'.steps` 内命中（`exists_obs_acc_of_passRun_accept`）
    → 哑元前缀把命中搬到机器自身起点（`exists_obs_acc_of_dummy_prefix`）。
    Completeness in the dummy-entry form: `M` accepting implies some branch hits the accept
    sentinel from the observer's own start (counter 0) on `seqHead :: branchBlocks`. -/
theorem exists_branch_dummy_hit_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (hxm : x.state = M.start)
    (hpre : x.pre.length ≤ T + 1) (hZ : Z ≤ T + 1)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((simObs q b ((M.stutter).haltNorm)).run
        (roundCostStay x Z (i % B) x.cur
          + (2 ^ ((2 * 2 ^ b + 42) * (T + 1)) + 2 * (B + 3) * (T + 1)))
        ⟨(simObs q b ((M.stutter).haltNorm)).start,
          x.enc (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).state
        = obsAcc q b := by
  -- 1. 接受 ⇒ 某分支通路成功且终态接受（零计数 `Z`）
  obtain ⟨t, i, r, ht1, htT, hi, hpass, hracc⟩ :=
    exists_pass_branchBlocks_of_acceptsWithin M hB hBpos w T b hbnd hT Z x hx hxw
      hd1 hd2 hxacc hacc
  have htpos : 0 < t := by omega
  have hbks : ∀ k' ∈ branchBlocks B t i, k' + 2 < 2 ^ b :=
    branchBlocks_hb B t i b hBpos hbnd
  have hbklen : (branchBlocks B t i).length = t :=
    branchBlocks_length B t i htpos
  have hklt : seqHead B T i ≤ B := seqHead_lt B T i hBpos
  have hc0 : 0 < 2 ^ b := by omega
  have hcK : seqHead B T i < 2 ^ b := seqHead_lt_pow B t i b hBpos hbnd
  -- 首块值 `i % B`（哑元轮消费它，并把计数器推到 `i % B + 1 = seqHead`）
  have hmod : i % B ≤ B := Nat.le_of_lt (Nat.mod_lt i hBpos)
  have hkS1 : i % B + 1 < 2 ^ b := by omega
  have hK2 : i % B + 2 < 2 ^ b := by omega
  -- 2. 零计数平移到哑元轮的输出 `Z + (i % B) + 3`
  obtain ⟨r', hr', hreg, hc', hz', hst'⟩ :=
    passRun_z_shift q b ((M.stutter).haltNorm).step (branchBlocks B t i) Z
      (i % B + 3) (seqHead B T i) hcK x hbks r hpass
  have hracc' : r'.reg.state = (M.stutter).haltNorm.accept := by
    rw [hreg]; exact hracc
  -- 3. 观察机在平移后的通路上于 `r'.steps` 内命中
  have hne : branchBlocks B t i ≠ [] := by
    intro h
    rw [h, List.length_nil] at hbklen
    omega
  obtain ⟨n, hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b (M.stutter) (branchBlocks B t i) hne
      (Z + (i % B + 3)) (seqHead B T i) hcK x x.state.val x.state.isLt rfl
      hx.1 hx.2 hbks r' hr' hracc'
  -- 4. 命中搬到观察机自身起点（哑元前缀，首块值 `i % B`）
  have hhit' : ((simObs q b ((M.stutter).haltNorm)).run n
      (obsStart q b (M.stutter) x x.state.val (i % B + 1)
        (Z + i % B + 3) x.state.isLt hkS1 (branchBlocks B t i))).state
      = obsAcc q b := by
    rw [show Z + (i % B + 3) = Z + i % B + 3 from by rw [Nat.add_assoc]] at hhit
    exact hhit
  obtain ⟨n', hn', hhit2⟩ :=
    exists_obs_acc_of_dummy_prefix q b M x Z (i % B) hc0 hK2 hx.1 hxm hxacc hxre
      (branchBlocks B t i) hkS1 n hhit'
  -- 5. 步数上界：`r` 的指数预算 + 哑元轮成本
  have hblen : (branchBlocks B t i).length ≤ T + 1 := by
    rw [hbklen]; omega
  have hsteps : r.steps ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) :=
    passRun_steps_le_two_pow_T q b (T + 1) ((M.stutter).haltNorm).step Z (seqHead B T i)
      hcK x (branchBlocks B t i) hbks hpre hZ hblen r hpass
  have hmul : 2 * (i % B + 3) * t ≤ 2 * (B + 3) * (T + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
  have hnfin : n ≤ 2 ^ ((2 * 2 ^ b + 42) * (T + 1)) + 2 * (B + 3) * (T + 1) := by
    have := hn
    rw [hst'] at this
    rw [hbklen] at this
    omega
  -- 6. 延长到最终预算
  exact ⟨t, i, ht1, htT, hi,
    simObs_run_accept_at_budget q b ((M.stutter).haltNorm) n'
      (roundCostStay x Z (i % B) x.cur
        + (2 ^ ((2 * 2 ^ b + 42) * (T + 1)) + 2 * (B + 3) * (T + 1)))
      _ (by omega) hhit2⟩

/-- **分支族可靠性的「哑元入口」版**：若运行相位机从**自身起始态**（计数器 0、数字区
    `i % B :: branchBlocks`）在预算 `K` 内接受（`K` 至少覆盖「哑元轮 + 分支预算」），
    则原机在 `T'` 步内接受。
    Reliability in the dummy-entry form: acceptance from the observer's own start implies
    `M.AcceptsWithin` once the budget covers the dummy round plus the branch budget. -/
theorem acceptsWithin_of_dummy_branch_acc (q b B T i T' : Nat) (M : NTM q) (w : List Bool)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z : Nat) (x : Reg q)
    (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hc0 : 0 < 2 ^ b) (hk1 : i % B + 1 < 2 ^ b) (hk2 : i % B + 2 < 2 ^ b)
    (hxm : x.state = M.start) (hxacc : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (hAcc : ((obsPhase q b ((M.stutter).haltNorm)).run
      (roundCostStay x Z (i % B) x.cur
        + (T' * costCap x.pre.length (Z + i % B + 3) T' (2 ^ b) + 6))
      ⟨(obsPhase q b ((M.stutter).haltNorm)).start,
        x.enc (none :: List.replicate Z (some false)
          ++ digitArea (i % B :: branchBlocks B T i))⟩).state
      = (obsPhase q b ((M.stutter).haltNorm)).accept) :
    M.AcceptsWithin w T' := by
  -- 1. 运行相位机接受 ⇒ 观察机在整段预算内命中
  have hHit : ((simObs q b ((M.stutter).haltNorm)).run
      (roundCostStay x Z (i % B) x.cur
        + (T' * costCap x.pre.length (Z + i % B + 3) T' (2 ^ b) + 6))
      ⟨(simObs q b ((M.stutter).haltNorm)).start,
        x.enc (none :: List.replicate Z (some false)
          ++ digitArea (i % B :: branchBlocks B T i))⟩).state = obsAcc q b :=
    (obsPhase_accept_iff q b ((M.stutter).haltNorm) _ _).mp hAcc
  -- 2. 拆成「哑元轮 + 分支预算」
  rw [show roundCostStay x Z (i % B) x.cur
        + (T' * costCap x.pre.length (Z + i % B + 3) T' (2 ^ b) + 6)
      = roundCostStay x Z (i % B) x.cur
        + (T' * costCap x.pre.length (Z + i % B + 3) T' (2 ^ b) + 6) from rfl,
    DTM.run_add,
    simObs_dummy_prefix q b M x Z (i % B) hc0 hk2 hpre hxm hxacc hxre (branchBlocks B T i)] at hHit
  -- 3. 分支级可靠性
  exact acceptsWithin_of_branch_obsPhase_acc q b B T i M w T' hB hb hl
    (Z + i % B + 3) (i % B + 1) hk1 x x.state.val x.state.isLt rfl hxM hxw hpre hpost
    hpadpost hpadpre hlen
    ((obsPhase_accept_iff q b ((M.stutter).haltNorm) _ _).mpr hHit)

/-- **成本上限对轮数单调**（`Z`、`P`、`Bk` 固定）：`costCap` 随可用轮数 `T` 不减。
    The cost cap is monotone in the number of rounds. -/
theorem costCap_T_mono (P Z T T' Bk : Nat) (h : T' ≤ T) :
    costCap P Z T' Bk ≤ costCap P Z T Bk := by
  unfold costCap
  have h6 : 6 * (P + T') ≤ 6 * (P + T) := Nat.mul_le_mul_left 6 (by omega)
  have h2 : 2 * (Z + T' * (Bk + 3)) ≤ 2 * (Z + T * (Bk + 3)) :=
    Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.mul_le_mul_right (Bk + 3) h) _)
  omega

/-- **哑元入口完备性的多项式预算版**：与 `exists_branch_dummy_hit_of_acceptsWithin` 同结论，
    但预算换成多项式 `roundCostStay + T·costCap + 2(B+3)(T+1)`（对分支一致可枚举）。
    Polynomial-budget version of the dummy-entry completeness: the uniform per-branch budget
    is `roundCostStay + T·costCap + 2(B+3)(T+1)`, independent of the branch. -/
theorem exists_branch_dummy_hit_of_acceptsWithin_poly {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (hxm : x.state = M.start)
    (hZ : Z ≤ T + 1)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((simObs q b ((M.stutter).haltNorm)).run
        (roundCostStay x Z (i % B) x.cur
          + (T * costCap x.pre.length Z T (2 ^ b) + 2 * (B + 3) * (T + 1)))
        ⟨(simObs q b ((M.stutter).haltNorm)).start,
          x.enc (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).state
        = obsAcc q b := by
  -- 1. 接受 ⇒ 某分支通路成功且终态接受（零计数 `Z`）
  obtain ⟨t, i, r, ht1, htT, hi, hpass, hracc⟩ :=
    exists_pass_branchBlocks_of_acceptsWithin M hB hBpos w T b hbnd hT Z x hx hxw
      hd1 hd2 hxacc hacc
  have htpos : 0 < t := by omega
  have hbks : ∀ k' ∈ branchBlocks B t i, k' + 2 < 2 ^ b :=
    branchBlocks_hb B t i b hBpos hbnd
  have hbklen : (branchBlocks B t i).length = t :=
    branchBlocks_length B t i htpos
  have hklt : seqHead B T i ≤ B := seqHead_lt B T i hBpos
  have hc0 : 0 < 2 ^ b := by omega
  have hcK : seqHead B T i < 2 ^ b := seqHead_lt_pow B t i b hBpos hbnd
  have hmod : i % B ≤ B := Nat.le_of_lt (Nat.mod_lt i hBpos)
  have hkS1 : i % B + 1 < 2 ^ b := by omega
  have hK2 : i % B + 2 < 2 ^ b := by omega
  -- 2. 零计数平移到哑元轮的输出 `Z + (i % B) + 3`
  obtain ⟨r', hr', hreg, hc', hz', hst'⟩ :=
    passRun_z_shift q b ((M.stutter).haltNorm).step (branchBlocks B t i) Z
      (i % B + 3) (seqHead B T i) hcK x hbks r hpass
  have hracc' : r'.reg.state = (M.stutter).haltNorm.accept := by
    rw [hreg]; exact hracc
  -- 3. 观察机在平移后的通路上于 `r'.steps` 内命中
  have hne : branchBlocks B t i ≠ [] := by
    intro h
    rw [h, List.length_nil] at hbklen
    omega
  obtain ⟨n, hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b (M.stutter) (branchBlocks B t i) hne
      (Z + (i % B + 3)) (seqHead B T i) hcK x x.state.val x.state.isLt rfl
      hx.1 hx.2 hbks r' hr' hracc'
  -- 4. 命中搬到观察机自身起点（哑元前缀，首块值 `i % B`）
  have hhit' : ((simObs q b ((M.stutter).haltNorm)).run n
      (obsStart q b (M.stutter) x x.state.val (i % B + 1)
        (Z + i % B + 3) x.state.isLt hkS1 (branchBlocks B t i))).state
      = obsAcc q b := by
    rw [show Z + (i % B + 3) = Z + i % B + 3 from by rw [Nat.add_assoc]] at hhit
    exact hhit
  obtain ⟨n', hn', hhit2⟩ :=
    exists_obs_acc_of_dummy_prefix q b M x Z (i % B) hc0 hK2 hx.1 hxm hxacc hxre
      (branchBlocks B t i) hkS1 n hhit'
  -- 5. 步数上界：`r.steps ≤ t·costCap`（多项式），哑元轮与平移增量用常数吸收
  have hsteps : r.steps ≤ (branchBlocks B t i).length
      * costCap x.pre.length Z (branchBlocks B t i).length (2 ^ b) :=
    passRun_steps_le q b ((M.stutter).haltNorm).step Z (seqHead B T i) hcK x
      (branchBlocks B t i) hbks r hpass
  have hcapT : costCap x.pre.length Z (branchBlocks B t i).length (2 ^ b)
      ≤ costCap x.pre.length Z T (2 ^ b) :=
    costCap_T_mono _ _ _ _ _ (by omega)
  have hpoly : r.steps ≤ T * costCap x.pre.length Z T (2 ^ b) := by
    rw [hbklen] at hsteps
    have hc' : costCap x.pre.length Z t (2 ^ b) ≤ costCap x.pre.length Z T (2 ^ b) := by
      rw [← hbklen]; exact hcapT
    exact Nat.le_trans hsteps (Nat.mul_le_mul htT hc')
  have hmul : 2 * (i % B + 3) * t ≤ 2 * (B + 3) * (T + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
  have hnfin : n ≤ T * costCap x.pre.length Z T (2 ^ b) + 2 * (B + 3) * (T + 1) := by
    have := hn
    rw [hst'] at this
    rw [hbklen] at this
    omega
  -- 6. 延长到最终预算
  exact ⟨t, i, ht1, htT, hi,
    simObs_run_accept_at_budget q b ((M.stutter).haltNorm) n'
      (roundCostStay x Z (i % B) x.cur
        + (T * costCap x.pre.length Z T (2 ^ b) + 2 * (B + 3) * (T + 1)))
      _ (by omega) hhit2⟩

/-- **`costCap` 对零计数的平移**：零计数增加 `d`，成本上限增加 `2d`。
    Shifting the zero count by `d` adds `2d` to the cost cap. -/
theorem costCap_Z_shift (P Z d T Bk : Nat) :
    costCap P (Z + d) T Bk = costCap P Z T Bk + 2 * d := by
  unfold costCap
  omega

/-- **逐分支统一预算**：`T·costCap + 2(B+3)(T+1) + 6`，对分支 `(t,i)` 一致。
    The uniform per-branch observer budget, independent of the branch. -/
def branchBudget (P Z T B b : Nat) : Nat :=
  T * costCap P Z T (2 ^ b) + 2 * (B + 3) * (T + 1) + 6

/-- **单轮成本对 `z`、`k` 单调**：更大的零计数与更大的头块值只会更贵。
    A stay round costs no less when `z` and `k` grow. -/
theorem roundCostStay_mono {q : Nat} (x : Reg q) (z z' k k' : Nat) (s' : Sym)
    (hz : z ≤ z') (hk : k ≤ k') :
    roundCostStay x z k s' ≤ roundCostStay x z' k' s' := by
  unfold roundCostStay
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **分支族完备性（统一预算）**：原机在 `T` 步内接受 ⇒ 存在分支 `(t, i)`，观察机从自身
    起始态在该分支的统一预算 `roundCostStay + branchBudget` 内命中 `obsAcc`。
    Dummy-entry completeness at the uniform per-branch budget. -/
theorem exists_branch_dummy_hit_uniform {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (hxm : x.state = M.start)
    (hZ : Z ≤ T + 1)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat), 1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      ((simObs q b ((M.stutter).haltNorm)).run
        (roundCostStay x Z (i % B) x.cur + branchBudget x.pre.length Z T B b)
        ⟨(simObs q b ((M.stutter).haltNorm)).start,
          x.enc (none :: List.replicate Z (some false)
            ++ digitArea (i % B :: branchBlocks B t i))⟩).state
        = obsAcc q b := by
  obtain ⟨t, i, ht1, htT, hi, hhit⟩ :=
    exists_branch_dummy_hit_of_acceptsWithin_poly M hB hBpos w T b hbnd hT Z x hx hxw
      hd1 hd2 hxacc hxre hxm hZ hacc
  refine ⟨t, i, ht1, htT, hi, ?_⟩
  refine simObs_run_accept_at_budget q b ((M.stutter).haltNorm) _ _ _ ?_ hhit
  unfold branchBudget
  omega

/-- **分支族可靠性（统一预算）**：观察机从自身起始态在该分支的统一预算内命中 ⇒ 原机
    在 `T'` 步内接受（拒绝判据的逆否；预算由 `passRun_steps_le_uniform` 覆盖所有前缀）。
    Dummy-entry reliability at the uniform per-branch budget: a hit implies acceptance. -/
theorem acceptsWithin_of_dummy_branch_acc_uniform (q b B T i T' : Nat) (M : NTM q) (w : List Bool)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z : Nat) (x : Reg q) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hc0 : 0 < 2 ^ b) (hk1 : i % B + 1 < 2 ^ b) (hk2 : i % B + 2 < 2 ^ b)
    (hxm : x.state = M.start) (hxacc : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (hHit : ((simObs q b ((M.stutter).haltNorm)).run
      (roundCostStay x Z (i % B) x.cur + branchBudget x.pre.length Z T' B b)
      ⟨(simObs q b ((M.stutter).haltNorm)).start,
        x.enc (none :: List.replicate Z (some false)
          ++ digitArea (i % B :: branchBlocks B T i))⟩).state
      = obsAcc q b) :
    M.AcceptsWithin w T' := by
  refine Classical.byContradiction ?_
  intro hna
  -- 哑元前缀：把 `run (rc + K)` 拆成 `run K (run rc ·)`
  have hd := simObs_dummy_prefix q b M x Z (i % B) hc0 hk2 hxM.1 hxm hxacc hxre
    (branchBlocks B T i)
  rw [DTM.run_add, hd] at hHit
  -- 拒绝判据（统一预算）的逆否
  refine branch_no_acc_budget_blocks q b B T i M w T' hB hb hl
    (Z + i % B + 3) (i % B + 1) hk1
    x x.state.val x.state.isLt rfl hxM hxw hxM.1 hxM.2 hpadpost hpadpre hlen hna
    (branchBudget x.pre.length Z T' B b) ?_ hHit
  intro L1 hb1 r1 hle1 hp1
  -- 前缀通路步数：统一预算版
  have h1 := passRun_steps_le_uniform q b ((M.stutter).haltNorm).step (Z + i % B + 3)
    (i % B + 1) hk1 x L1 hb1 r1 hp1 T' hle1
  -- 零计数平移：`costCap` 增加 `2*(i%B+3)`，由 `2(B+3)(T'+1)` 吸收
  have h2 : costCap x.pre.length (Z + (i % B + 3)) T' (2 ^ b)
      = costCap x.pre.length Z T' (2 ^ b) + 2 * (i % B + 3) := costCap_Z_shift _ _ _ _ _
  rw [show Z + i % B + 3 = Z + (i % B + 3) from by omega, h2] at h1
  have hmod : i % B < B := Nat.mod_lt i hB
  have hmul : T' * (costCap x.pre.length Z T' (2 ^ b) + 2 * (i % B + 3))
      ≤ T' * costCap x.pre.length Z T' (2 ^ b) + 2 * (B + 3) * (T' + 1) := by
    rw [Nat.mul_add]
    have hle : T' * (2 * (i % B + 3)) ≤ 2 * (B + 3) * (T' + 1) := by
      rw [show T' * (2 * (i % B + 3)) = 2 * (i % B + 3) * T' from Nat.mul_comm _ _]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
    omega
  unfold branchBudget
  omega

/-- **分支族可靠性（任意预算）**：只要预算 `K` 覆盖一切前缀通路（`hK`），观察机在该预算内
    命中即 `M.AcceptsWithin`。统一预算版 `acceptsWithin_of_dummy_branch_acc_uniform` 是
    `hK` 由 `passRun_steps_le_uniform` 提供的特例。
    Reliability at an arbitrary budget `K` that covers every prefix pass. -/
theorem acceptsWithin_of_dummy_branch_acc_budget (q b B T i T' : Nat) (M : NTM q) (w : List Bool)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z : Nat) (x : Reg q) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hc0 : 0 < 2 ^ b) (hk1 : i % B + 1 < 2 ^ b) (hk2 : i % B + 2 < 2 ^ b)
    (hxm : x.state = M.start) (hxacc : x.state ≠ M.accept) (hxre : x.state ≠ M.reject)
    (K : Nat)
    (hK : ∀ (L1 : List Nat) (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
      L1.length ≤ T' →
      passRun q b ((M.stutter).haltNorm).step (Z + i % B + 3) (i % B + 1) hk1 x L1 hb1
        = some r1 → r1.steps + 6 ≤ K)
    (hHit : ((simObs q b ((M.stutter).haltNorm)).run
      (roundCostStay x Z (i % B) x.cur + K)
      ⟨(simObs q b ((M.stutter).haltNorm)).start,
        x.enc (none :: List.replicate Z (some false)
          ++ digitArea (i % B :: branchBlocks B T i))⟩).state
      = obsAcc q b) :
    M.AcceptsWithin w T' := by
  refine Classical.byContradiction ?_
  intro hna
  have hd := simObs_dummy_prefix q b M x Z (i % B) hc0 hk2 hxM.1 hxm hxacc hxre
    (branchBlocks B T i)
  rw [DTM.run_add, hd] at hHit
  exact branch_no_acc_budget_blocks q b B T i M w T' hB hb hl
    (Z + i % B + 3) (i % B + 1) hk1
    x x.state.val x.state.isLt rfl hxM hxw hxM.1 hxM.2 hpadpost hpadpre hlen hna K hK hHit


end DTM

end Pnp
