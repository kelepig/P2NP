/-
  文件：Pnp/Machine/SimDriveNav.lean
  File: Pnp/Machine/SimDriveNav.lean

  主题：驱动 `simDrive` **导航层**的单步规格与分段运行引理（B5 阶段 3c-ii 第三块）。
  Topic: single-step specs and segmented run lemmas for the navigation layer of
  `simDrive` (B5 stage 3c-ii, third block).

  导航协议（auto-run-log #79）：一轮模拟结束后（相位 13，头在标记位），驱动依次：
  Navigation protocol (auto-run-log #79): after one simulation round (phase 13, head on
  the marker), the driver does, in order:
    1. `rewind`：左扫过模拟区编码，停在数字区左端分隔空白（子相位 0 → 1）；
       rewind: sweep left over the simulated-region encoding, stop on the separator
       blank at the left end of the digit area (subphase 0 → 1);
    2. `skip`：向左跳过已消费块的 0（子相位 1）；
       skip: move left over the zeros of already-consumed blocks (subphase 1);
    3. `count`：向左数当前块的 1（子相位 1 → 2），读到的数字 = 计数 − 1；
       count: count the ones of the current block going left (subphase 1 → 2), so the
       digit read is (count − 1);
    4. `erase`：向右返回，把读过的 1 擦写成 0，遇分隔空白进入找标记（子相位 3 → 4）；
       erase: walk back right erasing the counted ones to 0, then step into the marker
       search on the separator blank (subphase 3 → 4);
    5. `seek`：从模拟区左端逐格右扫，找到标记格（子相位 4/5/6 → 7）。
       seek: scan right from the left end of the simulated region, three symbols per
       cell, until the marker cell (subphases 4/5/6 → 7).
  子相位 7 的单步把选择数字 `c - 1` 带回模拟层相位 0（见 `simDrive_step_ph7`）。
  The subphase-7 step carries the choice digit `c - 1` back into simulation phase 0
  (see `simDrive_step_ph7`).

  本文件给出（全部经 `lake build`，无 `sorry`）：
  This file provides (all built with `lake build`, no `sorry`):
    - 子相位 0..7 的单步引理与对应的 `stepConfig` 版本；
      single-step lemmas for subphases 0..7 plus their `stepConfig` versions;
    - 五段运行规格：`simDrive_rewind`、`simDrive_skip`、`simDrive_count2`（固定终值版）、
      `simDrive_erase`、`simDrive_seek`；
      five run specs: `simDrive_rewind`, `simDrive_skip`, `simDrive_count2`
      (fixed final counter), `simDrive_erase`, `simDrive_seek`;
    - 下标同余小工具：`codeState_m_congr` / `codeState_c_congr`，用于避免对整段
      `Config` 做依赖搬运（那是 whnf 超时的根源）。
      index-congruence helpers `codeState_m_congr` / `codeState_c_congr`, which avoid
      dependent `Config` rewriting (the source of the earlier whnf timeouts).

  步数约定（易错）：`Tape.mk left right` 的头是 `right` 的头；左移把 `left` 的头
  压入 `right`，每一步的转移读的是**移动前**头下的符号。
  Step-counting convention (easy to get wrong): in `Tape.mk left right` the head symbol
  is `right`'s head; moving left pushes `left`'s head into `right`, and each transition
  reads the symbol under the head *before* the move.
-/

import Pnp.Machine.SimDrive
import Pnp.Machine.ReadDigit

set_option maxHeartbeats 2000000

namespace Pnp

namespace DTM

/-! ## 子相位单步规格 -/

/-- 由 `step` 规格得到 `stepConfig` 规格的小工具。 -/
theorem stepConfig_of_step (n : Nat) (M : DTM n) (c : Config n) (st' : Fin n) (a' : Sym)
    (d : Dir) (h : M.step c.state c.tape.read = (st', a', d)) :
    M.stepConfig c = Config.mk st' ((c.tape.write a').move d) := by
  unfold DTM.stepConfig
  rw [h]

/-- 代码状态与证明项无关：同一 `(m, c, z, ph)` 的不同界证明给出同一状态。 -/
theorem codeState_pi (q b m c z ph : Nat) (h1 h1' : m < q) (h2 h2' : c < 2 ^ b)
    (h3 h3' : z < 9) (h4 h4' : ph < 15) :
    (codeState q b m c z ph h1 h2 h3 h4 : Fin (stateCount q b)) =
      codeState q b m c z ph h1' h2' h3' h4' := by
  apply Fin.ext
  simp only [codeState_val]

/-- 状态下标的同余：`m = m'` 时两个代码状态相同（只在 `packIdx` 层做 Nat 改写）。
    Index congruence: equal `m` values give the same coded state (rewriting only at packIdx). -/
theorem codeState_m_congr (q b m m' c z ph : Nat) (he : m = m')
    (hm : m < q) (hm' : m' < q) (hc : c < 2 ^ b) (hz : z < 9) (hph : ph < 15) :
    codeState q b m c z ph hm hc hz hph =
      codeState q b m' c z ph hm' hc hz hph := by
  apply Fin.ext
  simp only [codeState_val, he]

/-- 选择编号的同余：`c = c'` 时两个代码状态相同。
    Choice-digit congruence: equal `c` values give the same coded state. -/
theorem codeState_c_congr (q b m c c' z ph : Nat) (he : c = c')
    (hm : m < q) (hc : c < 2 ^ b) (hc' : c' < 2 ^ b) (hz : z < 9) (hph : ph < 15) :
    codeState q b m c z ph hm hc hz hph =
      codeState q b m c' z ph hm hc' hz hph := by
  apply Fin.ext
  simp only [codeState_val, he]

theorem simDrive_step_ph0_blank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      none =
    (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)), none, Dir.left) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 0 hm hc (by decide) (by decide)]
  rw [if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph0_nonblank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ none) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      a =
    (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)), a, Dir.left) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 0 hm hc (by decide) (by decide)]
  rw [if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph1_true (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (hb : 1 < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
      (some true) =
    (embN (codeState q b m 1 0 2 hm hb (by decide) (by decide)), (some true), Dir.left) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 1 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 1 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 1 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 1 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 1 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

/-- **数字区耗尽**：子相位 1 在跳过零后读到左边界空白，说明已无剩余块，
    转入模拟层失败相位 14（原地）。放在空白上左移会在空白纸带上无限前进。
    Exhausted digit area: subphase 1 reads the left-boundary blank, meaning no block
    remains, so it enters simulation-layer failure phase 14 in place. -/
theorem simDrive_step_ph1_blank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
      none =
    (embS (codeState q b m c 0 14 hm hc (by decide) (by decide)), none, Dir.stay) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 1 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 1 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 1 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 1 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 1 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph1_false (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
      (some false) =
    (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)), (some false), Dir.left) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 1 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 1 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 1 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 1 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 1 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph2_true (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (hc1 : c + 1 < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 2 hm hc (by decide) (by decide)))
      (some true) =
    (embN (codeState q b m (c + 1) 0 2 hm hc1 (by decide) (by decide)), (some true), Dir.left) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 2 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 2 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 2 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 2 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 2 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph2_other (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ some true) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 2 hm hc (by decide) (by decide)))
      a =
    (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)), a, Dir.right) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 2 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 2 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 2 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 2 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 2 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph3_blank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
      none =
    (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)), none, Dir.right) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 3 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 3 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 3 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 3 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 3 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph3_nonblank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ none) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
      a =
    (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)), (some false), Dir.right) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 3 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 3 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 3 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 3 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 3 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph4 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
      a =
    (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)), a, Dir.right) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 4 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 4 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 4 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 4 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 4 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph5 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)))
      a =
    (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)), a, Dir.right) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 5 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 5 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 5 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 5 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 5 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph6_true (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)))
      (some true) =
    (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)), (some true), Dir.stay) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 6 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 6 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 6 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 6 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 6 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph6_other (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ some true) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)))
      a =
    (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)), a, Dir.right) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 6 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 6 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 6 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 6 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 6 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

theorem simDrive_step_ph7 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) :
    (simDrive q b tab s0).step
      (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)))
      a =
    (embS (codeState q b m (c - 1) 0 0 hm (by have := hc; omega) (by decide) (by decide)), a, Dir.stay) := by
  have h1 : ¬ (stateCount q b + (codeState q b m c 0 7 hm hc (by decide) (by decide)).val
      < stateCount q b) := by omega
  have h2 : ¬ (stateCount q b + (codeState q b m c 0 7 hm hc (by decide) (by decide)).val
      = 2 * stateCount q b) := by omega
  simp only [simDrive, dite_eq_right h1, dite_eq_right h2,
    embN, Fin.val_mk, Nat.add_sub_cancel_left,
    codeState_unpackPh q b m c 0 7 hm hc (by decide) (by decide),
    codeState_unpackM q b m c 0 7 hm hc (by decide) (by decide),
    codeState_unpackC q b m c 0 7 hm hc (by decide) (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  repeat' split
  all_goals first | omega | exact absurd trivial ‹¬True› | rfl | simp_all

/-! ## 子相位 `stepConfig` 规格 -/

theorem simDrive_stepConfig_ph0_blank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (Tape.mk L (none :: R))) =
      Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
        ((Tape.mk L (none :: R)).write none |>.move Dir.left) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph0_blank q b tab s0 m c hm hc)]

theorem simDrive_stepConfig_ph0_nonblank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ none) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write a |>.move Dir.left) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph0_nonblank q b tab s0 m c hm hc a ha)]

theorem simDrive_stepConfig_ph1_true (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (hb : 1 < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
        (Tape.mk L (some true :: R))) =
      Config.mk (embN (codeState q b m 1 0 2 hm hb (by decide) (by decide)))
        ((Tape.mk L (some true :: R)).write (some true) |>.move Dir.left) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph1_true q b tab s0 m c hm hc hb)]

theorem simDrive_stepConfig_ph1_blank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
        (Tape.mk L (none :: R))) =
      Config.mk (embS (codeState q b m c 0 14 hm hc (by decide) (by decide)))
        ((Tape.mk L (none :: R)).write none |>.move Dir.stay) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph1_blank q b tab s0 m c hm hc)]

theorem simDrive_stepConfig_ph1_false (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
        (Tape.mk L (some false :: R))) =
      Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
        ((Tape.mk L (some false :: R)).write (some false) |>.move Dir.left) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph1_false q b tab s0 m c hm hc)]

theorem simDrive_stepConfig_ph2_true (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (hc1 : c + 1 < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 2 hm hc (by decide) (by decide)))
        (Tape.mk L (some true :: R))) =
      Config.mk (embN (codeState q b m (c + 1) 0 2 hm hc1 (by decide) (by decide)))
        ((Tape.mk L (some true :: R)).write (some true) |>.move Dir.left) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph2_true q b tab s0 m c hm hc hc1)]

theorem simDrive_stepConfig_ph2_other (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 2 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write a |>.move Dir.right) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph2_other q b tab s0 m c hm hc a ha)]

theorem simDrive_stepConfig_ph3_blank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
        (Tape.mk L (none :: R))) =
      Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
        ((Tape.mk L (none :: R)).write none |>.move Dir.right) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph3_blank q b tab s0 m c hm hc)]

theorem simDrive_stepConfig_ph3_nonblank (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ none) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write (some false) |>.move Dir.right) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph3_nonblank q b tab s0 m c hm hc a ha)]

theorem simDrive_stepConfig_ph4 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write a |>.move Dir.right) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph4 q b tab s0 m c hm hc a)]

theorem simDrive_stepConfig_ph5 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write a |>.move Dir.right) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph5 q b tab s0 m c hm hc a)]

theorem simDrive_stepConfig_ph6_true (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)))
        (Tape.mk L (some true :: R))) =
      Config.mk (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)))
        ((Tape.mk L (some true :: R)).write (some true) |>.move Dir.stay) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph6_true q b tab s0 m c hm hc)]

theorem simDrive_stepConfig_ph6_other (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (ha : a ≠ some true) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write a |>.move Dir.right) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph6_other q b tab s0 m c hm hc a ha)]

theorem simDrive_stepConfig_ph7 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (a : Sym) (L R : List Sym) :
    (simDrive q b tab s0).stepConfig
      (Config.mk (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)))
        (Tape.mk L (a :: R))) =
      Config.mk (embS (codeState q b m (c - 1) 0 0 hm (by have := hc; omega) (by decide) (by decide)))
        ((Tape.mk L (a :: R)).write a |>.move Dir.stay) := by
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph7 q b tab s0 m c hm hc a)]

/-! ## 五段导航运行引理 -/

/-- **回扫**：相位 0 从标记位左扫，读标记 → 扫过 `L0` 的全部非空白格 → 读分隔空白，
    共 `|L0| + 2` 步，停在数字区首符号上，子相位 1。 -/
theorem simDrive_rewind (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (x : Sym) (L0 : List Sym), x ≠ none → (∀ y ∈ L0, y ≠ none) →
      ∀ (a0 : Sym) (Z' M : List Sym),
        (simDrive q b tab s0).run (L0.length + 2)
          (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (Tape.mk (L0 ++ none :: a0 :: Z') (x :: M))) =
        Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
          (Tape.mk Z' (a0 :: none :: L0.reverse ++ x :: M))
  | x, [], hx, _, a0, Z', M => by
      have hh : (simDrive q b tab s0).halted
          (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (Tape.mk (none :: a0 :: Z') (x :: M))) = false :=
        simDrive_halted_embN q b tab s0 _ _
      simp only [List.length_nil, List.nil_append, Nat.zero_add]
      rw [DTM.run_succ_of_not_halted _ 1 _ hh]
      rw [simDrive_stepConfig_ph0_nonblank q b tab s0 m c hm hc x hx
        (none :: a0 :: Z') M]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
        List.tail]
      have hh2 : (simDrive q b tab s0).halted
          (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (Tape.mk (a0 :: Z') (none :: x :: M))) = false :=
        simDrive_halted_embN q b tab s0 _ _
      rw [DTM.run_succ_of_not_halted _ 0 _ hh2]
      rw [simDrive_stepConfig_ph0_blank q b tab s0 m c hm hc (a0 :: Z') (x :: M)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
        List.tail, List.reverse_nil, List.nil_append]
      rfl
  | x, y :: ys, hx, hL0, a0, Z', M => by
      have hy : y ≠ none := hL0 y (by simp)
      have hys : ∀ z ∈ ys, z ≠ none := fun z hz => hL0 z (by simp [hz])
      have hh : (simDrive q b tab s0).halted
          (Config.mk (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (Tape.mk (y :: (ys ++ none :: a0 :: Z')) (x :: M))) = false :=
        simDrive_halted_embN q b tab s0 _ _
      simp only [List.length_cons, List.cons_append]
      rw [show ys.length + 1 + 2 = (ys.length + 2) + 1 from by omega]
      rw [DTM.run_succ_of_not_halted _ _ _ hh]
      rw [simDrive_stepConfig_ph0_nonblank q b tab s0 m c hm hc x hx
        (y :: (ys ++ none :: a0 :: Z')) M]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read,
        List.tail, List.cons_append, List.nil_append]
      rw [simDrive_rewind q b tab s0 m c hm hc y ys hy hys a0 Z' (x :: M)]
      simp only [List.reverse_cons, List.singleton_append, List.append_assoc, List.nil_append]
      rfl

/-- **跳过已消费块**：子相位 1 读到 0 就继续左移，共 `z + 1` 步（读入的头符号再加 `z` 个 0），
    最后头停在 `a0`（下一个 1 或块终结符）。 -/
theorem simDrive_skip (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (z : Nat) (a0 : Sym) (W' R0 : List Sym),
      (simDrive q b tab s0).run (z + 1)
        (Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
          (Tape.mk (List.replicate z (some false) ++ a0 :: W') ((some false) :: R0))) =
      Config.mk (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)))
        (Tape.mk W' ((a0) :: List.replicate (z + 1) (some false) ++ R0))
  | 0, a0, W', R0 => by
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 1 hm hc (by decide) (by decide))
        (Tape.mk (List.replicate 0 (some false) ++ a0 :: W') (some false :: R0))
      rw [DTM.run_succ_of_not_halted _ 0 _ hh]
      simp only [List.replicate_zero, List.nil_append]
      rw [simDrive_stepConfig_ph1_false q b tab s0 m c hm hc (a0 :: W') R0]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      rfl
  | z + 1, a0, W', R0 => by
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 1 hm hc (by decide) (by decide))
        (Tape.mk (List.replicate (z + 1) (some false) ++ a0 :: W') (some false :: R0))
      rw [DTM.run_succ_of_not_halted _ _ _ hh]
      rw [simDrive_stepConfig_ph1_false q b tab s0 m c hm hc
        (List.replicate (z + 1) (some false) ++ a0 :: W') R0]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail,
        List.replicate_succ, List.cons_append]
      rw [simDrive_skip q b tab s0 m c hm hc z a0 W' (some false :: R0)]
      simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append, replicate_append_cons]

/-- **计数 1 段（固定终值版 / fixed final counter）**：子相位 2 从计数 `i` 出发，
    左场还有 `k` 个 1，`k + 1` 步后计数到达固定值 `K`（`K = i + k + 1`）。
    Fixing the final counter `K` keeps every intermediate state syntactically identical,
    so the inductive step needs no dependent rewrite of the packed state. -/
theorem simDrive_count2 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m K : Nat) (hm : m < q) (hK : K < 2 ^ b) :
    ∀ (i k : Nat) (he : K = i + k + 1) (hi : i < 2 ^ b),
      ∀ (x : Sym) (X' R0 : List Sym), x ≠ some true →
      (simDrive q b tab s0).run (k + 1)
        (Config.mk (embN (codeState q b m i 0 2 hm hi (by decide) (by decide)))
          (Tape.mk (List.replicate k (some true) ++ x :: X') (some true :: R0))) =
      Config.mk (embN (codeState q b m K 0 2 hm hK (by decide) (by decide)))
        (Tape.mk X' (x :: List.replicate (k + 1) (some true) ++ R0))
  | i, 0, he, hi, x, X', R0, hx => by
      have hi1 : i + 1 < 2 ^ b := by omega
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m i 0 2 hm hi (by decide) (by decide))
        (Tape.mk (List.replicate 0 (some true) ++ x :: X') (some true :: R0))
      rw [DTM.run_succ_of_not_halted _ 0 _ hh]
      rw [simDrive_stepConfig_ph2_true q b tab s0 m i hm hi hi1
        (List.replicate 0 (some true) ++ x :: X') R0]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail,
        List.replicate_zero, List.replicate_succ, List.cons_append, List.nil_append]
      have hstate := codeState_c_congr q b m (i + 1) K 0 2 (by omega : i + 1 = K)
        hm hi1 hK (by decide) (by decide)
      rw [hstate]
      rfl
  | i, k + 1, he, hi, x, X', R0, hx => by
      have hi1 : i + 1 < 2 ^ b := by omega
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m i 0 2 hm hi (by decide) (by decide))
        (Tape.mk (List.replicate (k + 1) (some true) ++ x :: X') (some true :: R0))
      rw [DTM.run_succ_of_not_halted _ _ _ hh]
      rw [simDrive_stepConfig_ph2_true q b tab s0 m i hm hi hi1
        (List.replicate (k + 1) (some true) ++ x :: X') R0]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail,
        List.replicate_succ, List.cons_append]
      rw [simDrive_count2 q b tab s0 m K hm hK (i + 1) k (by omega)
        hi1 x X' (some true :: R0) hx]
      simp only [List.replicate_succ, List.cons_append, ← replicate_append_cons]

/-- **返回并擦除**：子相位 3 从已读块最右的 1 出发，向右把非空白符号全部改写成 0，
    读到分隔空白后进入子相位 4（`|D| + 1` 步）。 -/
theorem simDrive_erase (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (D : List Sym), (∀ x ∈ D, x ≠ none) →
      ∀ (a0 : Sym) (W' R2 : List Sym),
        (simDrive q b tab s0).run (D.length + 1)
          (Config.mk (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)))
            (Tape.mk (a0 :: W') (D ++ none :: R2))) =
        Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
          (Tape.mk (none :: List.replicate D.length (some false) ++ a0 :: W') R2)
  | [], _, a0, W', R2 => by
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 3 hm hc (by decide) (by decide))
        (Tape.mk (a0 :: W') (none :: R2))
      simp only [List.length_nil, List.nil_append]
      rw [DTM.run_succ_of_not_halted _ 0 _ hh]
      rw [simDrive_stepConfig_ph3_blank q b tab s0 m c hm hc (a0 :: W') R2]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      rfl
  | d :: Ds, hD, a0, W', R2 => by
      have hd : d ≠ none := hD d (by simp)
      have hDs : ∀ x ∈ Ds, x ≠ none := fun x hx => hD x (by simp [hx])
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 3 hm hc (by decide) (by decide))
        (Tape.mk (a0 :: W') ((d :: Ds) ++ none :: R2))
      simp only [List.length_cons]
      rw [show Ds.length + 1 + 1 = (Ds.length + 1) + 1 from by omega]
      rw [DTM.run_succ_of_not_halted _ _ _ hh]
      simp only [List.cons_append]
      rw [simDrive_stepConfig_ph3_nonblank q b tab s0 m c hm hc d hd
        (a0 :: W') (Ds ++ none :: R2)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail,
        List.cons_append]
      rw [simDrive_erase q b tab s0 m c hm hc Ds hDs (some false) (a0 :: W') R2]
      simp only [List.cons_append, replicate_append_cons, List.append_assoc,
        List.nil_append]
      rfl

/-- **找标记**：子相位 4 从模拟区左端出发，逐格扫描（每格 3 个符号），
    在 `3|cs|+3` 步后到达标记格，子相位 7，头停在标记符号上。 -/
theorem simDrive_seek (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) →
      ∀ (s : Sym) (rest : List (Sym × Bool)) (L : List Sym),
        (simDrive q b tab s0).run (3 * cs.length + 3)
          (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
            (Tape.mk L (codeCells cs ++ cellCode (s, true) ++ codeCells rest))) =
        Config.mk (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)))
          (Tape.mk (List.reverse (codeCells cs ++ symCode s) ++ L)
            (some true :: codeCells rest))
  | [], _, s, rest, L => by
      obtain ⟨b0, b1, hs⟩ : ∃ b0 b1 : Sym, symCode s = [b0, b1] := by
        cases s with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hcell : cellCode (s, true) = b0 :: b1 :: some true :: [] := by
        simp [cellCode, hs]
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, hcell, List.cons_append,
        List.nil_append, codeCells, List.flatMap_nil]
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 4 hm hc (by decide) (by decide))
        (Tape.mk L (b0 :: b1 :: some true :: List.flatMap cellCode rest))
      rw [show (3 : Nat) = 2 + 1 from rfl]
      rw [DTM.run_succ_of_not_halted _ 2 _ hh]
      rw [simDrive_stepConfig_ph4 q b tab s0 m c hm hc b0 L
        (b1 :: some true :: List.flatMap cellCode rest)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      have hh2 := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 5 hm hc (by decide) (by decide))
        (Tape.mk (b0 :: L) (b1 :: some true :: List.flatMap cellCode rest))
      rw [show (2 : Nat) = 1 + 1 from rfl]
      rw [DTM.run_succ_of_not_halted _ 1 _ hh2]
      rw [simDrive_stepConfig_ph5 q b tab s0 m c hm hc b1
        (b0 :: L) (some true :: List.flatMap cellCode rest)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      have hh3 := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 6 hm hc (by decide) (by decide))
        (Tape.mk (b1 :: b0 :: L) (some true :: List.flatMap cellCode rest))
      rw [DTM.run_succ_of_not_halted _ 0 _ hh3]
      rw [simDrive_stepConfig_ph6_true q b tab s0 m c hm hc (b1 :: b0 :: L)
        (List.flatMap cellCode rest)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      simp only [hs, List.reverse_cons, List.reverse_nil, List.nil_append]
      rfl
  | p :: ps, hmark, s, rest, L => by
      obtain ⟨b0, b1, hs⟩ : ∃ b0 b1 : Sym, symCode p.1 = [b0, b1] := by
        cases p.1 with
        | none => exact ⟨some false, some false, rfl⟩
        | some b => cases b <;> exact ⟨_, _, rfl⟩
      have hp : p.2 = false := hmark p (by simp)
      have hcell : cellCode p = b0 :: b1 :: some false :: [] := by
        simp [cellCode, hs, hp]
      have hps : ∀ q ∈ ps, q.2 = false := fun q hq => hmark q (by simp [hq])
      have hcs : codeCells (p :: ps) = cellCode p ++ codeCells ps := by
        simp [codeCells]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [show 3 * ps.length + 3 + 3 = ((3 * ps.length + 3) + 2) + 1 from by omega]
      rw [hcs, hcell]
      simp only [List.cons_append, List.nil_append]
      have hh := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 4 hm hc (by decide) (by decide))
        (Tape.mk L (b0 :: b1 :: some false :: (codeCells ps ++ cellCode (s, true)
          ++ codeCells rest)))
      rw [DTM.run_succ_of_not_halted _ ((3 * ps.length + 3) + 2) _ hh]
      rw [simDrive_stepConfig_ph4 q b tab s0 m c hm hc b0 L
        (b1 :: some false :: (codeCells ps ++ cellCode (s, true) ++ codeCells rest))]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      have hh2 := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 5 hm hc (by decide) (by decide))
        (Tape.mk (b0 :: L) (b1 :: some false :: (codeCells ps ++ cellCode (s, true)
          ++ codeCells rest)))
      rw [show ((3 * ps.length + 3) + 2) = ((3 * ps.length + 3) + 1) + 1 from by omega]
      rw [DTM.run_succ_of_not_halted _ ((3 * ps.length + 3) + 1) _ hh2]
      rw [simDrive_stepConfig_ph5 q b tab s0 m c hm hc b1
        (b0 :: L) (some false :: (codeCells ps ++ cellCode (s, true) ++ codeCells rest))]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      have hh3 := simDrive_halted_embN q b tab s0
        (codeState q b m c 0 6 hm hc (by decide) (by decide))
        (Tape.mk (b1 :: b0 :: L) (some false :: (codeCells ps ++ cellCode (s, true)
          ++ codeCells rest)))
      rw [DTM.run_succ_of_not_halted _ (3 * ps.length + 3) _ hh3]
      rw [simDrive_stepConfig_ph6_other q b tab s0 m c hm hc (some false) (by decide)
        (b1 :: b0 :: L) (codeCells ps ++ cellCode (s, true) ++ codeCells rest)]
      simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.read, List.tail]
      rw [simDrive_seek q b tab s0 m c hm hc ps hps s rest (some false :: b1 :: b0 :: L)]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        List.append_assoc, List.cons_append]
