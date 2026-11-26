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
    (h0 : ∀ (s : Fin q) (a : Sym), pick (tab s a) 0 = some (s, a, Dir.stay))
    (ks : List Nat) :
    (simDrive q b tab s0).run (roundCostStay x z k x.cur)
      (passStart x x.state.val 0 x.state.isLt hc0 z (k :: ks)) =
    passStart x x.state.val (k + 1) x.state.isLt (by omega) (z + k + 3) ks := by
  have hx : x.state = (⟨x.state.val, x.state.isLt⟩ : Fin q) := rfl
  have hk := h0 x.state x.cur
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
    (h0 : ∀ (s : Fin q) (a : Sym), pick (tab s a) 0 = some (s, a, Dir.stay))
    (r : PassRes q b) (hpass : passRun q b tab (Z + k + 3) (k + 1) (by omega) x ks hb = some r) :
    (simDrive q b tab s0).run (roundCostStay x Z k x.cur + r.steps)
      (passStart x x.state.val 0 x.state.isLt hc0 Z (k :: ks)) = passEnd r := by
  rw [DTM.run_add]
  rw [simDrive_dummy_round q b tab s0 x Z k hc0 hk hpre h0 ks]
  exact simDrive_pass q b tab s0 ks (Z + k + 3) (k + 1) (by omega) x x.state.val
    x.state.isLt rfl hpre hpost hb r hpass

end DTM

end Pnp
