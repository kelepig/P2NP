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

end DTM

end Pnp
