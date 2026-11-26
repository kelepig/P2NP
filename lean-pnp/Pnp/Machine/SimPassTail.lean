/-
  文件：Pnp/Machine/SimPassTail.lean
  File: Pnp/Machine/SimPassTail.lean

  主题：通路读数的**尾部稳定性**——接受前缀通路之后无论数字区还剩什么块，
        观察机在通路结束前（`r.steps` 步内）看到的「被模拟状态读数」完全一致。
  Topic: tail stability of the pass reading — whatever digit blocks follow an
  accepted prefix, the observer's simulated-state reading inside the pass
  (`r.steps` steps) is unchanged.

  为什么需要它（docs/decisions/auto-run-log.md #139）：接受通路 `L1 ++ [k]`
  是分支块列表 `(L1 ++ [k]) ++ L2` 的前缀；观察机前 `r.steps` 步的读数只由
  前 `|L1| + 1` 轮决定，尾块从不被读到，故与尾部无关。
  Use (auto-run-log #139): the accepted path is a prefix of the branch block list,
  and the observer's reading in the first `r.steps` steps depends only on the first
  rounds, never on the trailing blocks.

  本文件给出：
    - `simDrive_run_driveM_nav_const`：导航层整段读数不变；
    - 三个方向的「轮内读数分段常量」引理 `simDrive_passStart_roundDriveM_*`；
    - 主定理 `simDrive_pass_readings_tail`。
  This file provides the navigation-layer reading constancy, the per-round piecewise
  reading lemmas for the three directions, and the main tail-stability theorem.
-/

import Pnp.Machine.SimPass
import Pnp.Machine.SimRoundM
import Pnp.Machine.SimObsRun

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-! ## 导航层读数不变 -/

/-- **导航段读数恒定**：若起点在范围内、且前 `L` 步的每个状态都在导航层
    （状态号 ≥ `stateCount`），则这 `L` 步内任意时刻的读数都等于起点的读数。
    Navigation-layer reading constancy: if every state in the first `L` steps stays
    in the navigation layer, the reading never changes. -/
theorem simDrive_run_driveM_nav_const (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    ∀ (c : Config (stateCountD q b)) (L : Nat),
      c.state.val < 2 * stateCount q b →
      (∀ i, i < L → stateCount q b ≤ ((simDrive q b tab s0).run i c).state.val) →
      ∀ i, i ≤ L →
        driveM q b ((simDrive q b tab s0).run i c).state = driveM q b c.state := by
  intro c L hrange hnav
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      have hiL : i < L := by omega
      have hrun := simDrive_run_range q b tab s0 i c hrange
      have hnh := simDrive_halted_false_of_range q b tab s0
        ((simDrive q b tab s0).run i c).state ((simDrive q b tab s0).run i c).tape hrun
      have hone : (simDrive q b tab s0).run (i + 1) c
          = (simDrive q b tab s0).stepConfig ((simDrive q b tab s0).run i c) :=
        DTM.run_succ_last (simDrive q b tab s0) i c hnh
      rw [hone]
      have hne : ¬ ((simDrive q b tab s0).run i c).state.val < stateCount q b := by
        have := hnav i hiL
        omega
      change driveM q b (((simDrive q b tab s0).step
        ((simDrive q b tab s0).run i c).state
        ((simDrive q b tab s0).run i c).tape.read).1) = driveM q b c.state
      rw [simDrive_step_driveM_nav q b tab s0 _ _ hne hrun]
      have hi' := ih (by omega)
      rw [driveM, ite_eq_right hne] at hi'
      exact hi'

/-! ## 轮内读数：分段常量 -/

/-- **整轮读数轨迹（原地 / stay）**：从 `passStart … Z (k :: ks)` 出发跑一轮，
    任意时刻 `i ≤ roundCostStay` 的读数只分两段：前 4 步是起点 `m`，其余是查表所得 `m'`。
    Per-round reading trajectory (stay): the reading is the start `m` for the first four
    steps and the looked-up `m'` afterwards. -/
theorem simDrive_passStart_roundDriveM_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat) (ks : List Nat)
    (hk : k + 2 < 2 ^ b) (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    ∀ i, i ≤ roundCostStay x Z k s' →
      driveM q b ((simDrive q b tab s0).run i (passStart x m c hm hc Z (k :: ks))).state
        = (if i ≤ 4 then m else m'.val) := by
  obtain ⟨xc, X', htail⟩ := digitArea_split ks
  have hxc : xc ≠ some true := digitArea_head_ne_true ks xc X' htail
  have hcfg : passStart x m c hm hc Z (k :: ks)
      = Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    exact passStart_tape_eq Z k ks xc X' htail
  intro i hi
  rw [hcfg]
  have hrange0 : (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (x.enc (none :: (some false) :: (List.replicate Z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))).state.val
      < 2 * stateCount q b := by
    simp only [embS, Fin.val_mk]
    have h1 := (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt
    have h2 : 0 < stateCount q b := stateCount_pos q b (by omega)
    omega
  have hnavM : ∀ d : Nat, 14 + d ≤ roundCostStay x Z k s' →
      driveM q b ((simDrive q b tab s0).run (14 + d)
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state = m'.val := by
    intro d
    induction d with
    | zero =>
        intro _
        rw [simDrive_run14_stay q b tab s0 m c hm hc x
          (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))
          m' s' hx h]
        rw [driveM_embN, codeState_unpackM]
    | succ d ih =>
        intro hC
        have hjC : 14 + d ≤ roundCostStay x Z k s' := by omega
        have hjlt : 14 + d < roundCostStay x Z k s' := by omega
        have h14 := ih hjC
        rw [show 14 + (d + 1) = 14 + d + 1 from by omega]
        have hconst := simDrive_run_driveM_nav_const q b tab s0
          ((simDrive q b tab s0).run (14 + d)
            (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
              (x.enc (none :: (some false) :: (List.replicate Z (some false)
                ++ (some true :: (List.replicate (k + 1) (some true)
                  ++ (xc :: X')))))))) 1
          (simDrive_run_range q b tab s0 (14 + d) _ hrange0)
          (by
            intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [simRun_zero]
            exact simDrive_roundFullNav_stay q b tab s0 m c hm hc x Z k (k + 2)
              hk rfl xc X' hxc hpre m' s' hx h (14 + d) (by omega) hjlt)
          1 (by omega)
        rw [DTM.run_add (simDrive q b tab s0) (14 + d) 1 _]
        rw [hconst, h14]
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · rw [ite_eq_left (by omega : i ≤ 4)]
    have hst : ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val < stateCount q b := by
      have hrun := simDrive_embS_run13 q b tab s0 m c hm hc
        (x.enc (none :: (some false) :: (List.replicate Z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) i (by omega)
      rw [hrun]
      simp only [embS, Fin.val_mk]
      exact Fin.isLt _
    rw [driveM, ite_eq_left hst]
    exact simDrive_roundM_le_stay q b tab s0 m c hm hc x Z k xc X' i (by omega)
  · rw [ite_eq_right (by omega : ¬ i ≤ 4)]
    by_cases hi13 : i ≤ 13
    · have hst : ((simDrive q b tab s0).run i
          (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (x.enc (none :: (some false) :: (List.replicate Z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true)
                ++ (xc :: X')))))))).state.val < stateCount q b := by
        have hrun := simDrive_embS_run13 q b tab s0 m c hm hc
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) i (by omega)
        rw [hrun]
        simp only [embS, Fin.val_mk]
        exact Fin.isLt _
      rw [driveM, ite_eq_left hst]
      exact simDrive_roundM_ge q b tab s0 m c hm hc x Z k xc X' m' s' (d := Dir.stay) hx h
        i hi5 hi13
    · have hi14 : 14 ≤ i := by omega
      rw [show i = 14 + (i - 14) from by omega]
      exact hnavM (i - 14) (by omega)

/-- **整轮读数轨迹（右移 / right）**：前 4 步读 `m`，其余读 `m'`。
    Per-round reading trajectory (right). -/
theorem simDrive_passStart_roundDriveM_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat) (ks : List Nat)
    (hk : k + 2 < 2 ^ b) (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    ∀ i, i ≤ roundCostRight x Z k p s' →
      driveM q b ((simDrive q b tab s0).run i (passStart x m c hm hc Z (k :: ks))).state
        = (if i ≤ 4 then m else m'.val) := by
  obtain ⟨xc, X', htail⟩ := digitArea_split ks
  have hxc : xc ≠ some true := digitArea_head_ne_true ks xc X' htail
  have hcfg : passStart x m c hm hc Z (k :: ks)
      = Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    exact passStart_tape_eq Z k ks xc X' htail
  intro i hi
  rw [hcfg]
  have hrange0 : (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (x.enc (none :: (some false) :: (List.replicate Z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))).state.val
      < 2 * stateCount q b := by
    simp only [embS, Fin.val_mk]
    have h1 := (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt
    have h2 : 0 < stateCount q b := stateCount_pos q b (by omega)
    omega
  have hnavM : ∀ d : Nat, 14 + d ≤ roundCostRight x Z k p s' →
      driveM q b ((simDrive q b tab s0).run (14 + d)
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state = m'.val := by
    intro d
    induction d with
    | zero =>
        intro _
        rw [simDrive_run14_right q b tab s0 m c hm hc x
          (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))
          p post' hp hpost m' s' hx h]
        rw [driveM_embN, codeState_unpackM]
    | succ d ih =>
        intro hC
        have hjC : 14 + d ≤ roundCostRight x Z k p s' := by omega
        have hjlt : 14 + d < roundCostRight x Z k p s' := by omega
        have h14 := ih hjC
        rw [show 14 + (d + 1) = 14 + d + 1 from by omega]
        have hconst := simDrive_run_driveM_nav_const q b tab s0
          ((simDrive q b tab s0).run (14 + d)
            (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
              (x.enc (none :: (some false) :: (List.replicate Z (some false)
                ++ (some true :: (List.replicate (k + 1) (some true)
                  ++ (xc :: X')))))))) 1
          (simDrive_run_range q b tab s0 (14 + d) _ hrange0)
          (by
            intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [simRun_zero]
            exact simDrive_roundFullNav_right q b tab s0 m c hm hc x Z k (k + 2)
              hk rfl xc X' hxc hpre p post' hp hpost m' s' hx h (14 + d) (by omega) hjlt)
          1 (by omega)
        rw [DTM.run_add (simDrive q b tab s0) (14 + d) 1 _]
        rw [hconst, h14]
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · rw [ite_eq_left (by omega : i ≤ 4)]
    have hst : ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val < stateCount q b := by
      have hrun := simDrive_embS_run13 q b tab s0 m c hm hc
        (x.enc (none :: (some false) :: (List.replicate Z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) i (by omega)
      rw [hrun]
      simp only [embS, Fin.val_mk]
      exact Fin.isLt _
    rw [driveM, ite_eq_left hst]
    exact simDrive_roundM_le_stay q b tab s0 m c hm hc x Z k xc X' i (by omega)
  · rw [ite_eq_right (by omega : ¬ i ≤ 4)]
    by_cases hi13 : i ≤ 13
    · have hst : ((simDrive q b tab s0).run i
          (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (x.enc (none :: (some false) :: (List.replicate Z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true)
                ++ (xc :: X')))))))).state.val < stateCount q b := by
        have hrun := simDrive_embS_run13 q b tab s0 m c hm hc
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) i (by omega)
        rw [hrun]
        simp only [embS, Fin.val_mk]
        exact Fin.isLt _
      rw [driveM, ite_eq_left hst]
      exact simDrive_roundM_ge q b tab s0 m c hm hc x Z k xc X' m' s' (d := Dir.right) hx h
        i hi5 hi13
    · have hi14 : 14 ≤ i := by omega
      rw [show i = 14 + (i - 14) from by omega]
      exact hnavM (i - 14) (by omega)

/-- **整轮读数轨迹（左移 / left）**：前 4 步读 `m`，其余读 `m'`。
    Per-round reading trajectory (left). -/
theorem simDrive_passStart_roundDriveM_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (Z k : Nat) (ks : List Nat)
    (hk : k + 2 < 2 ^ b) (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprel : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    ∀ i, i ≤ roundCostLeft (q := q) Z k pre' cq s' →
      driveM q b ((simDrive q b tab s0).run i (passStart x m c hm hc Z (k :: ks))).state
        = (if i ≤ 4 then m else m'.val) := by
  obtain ⟨xc, X', htail⟩ := digitArea_split ks
  have hxc : xc ≠ some true := digitArea_head_ne_true ks xc X' htail
  have hcfg : passStart x m c hm hc Z (k :: ks)
      = Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    exact passStart_tape_eq Z k ks xc X' htail
  intro i hi
  rw [hcfg]
  have hrange0 : (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (x.enc (none :: (some false) :: (List.replicate Z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))).state.val
      < 2 * stateCount q b := by
    simp only [embS, Fin.val_mk]
    have h1 := (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt
    have h2 : 0 < stateCount q b := stateCount_pos q b (by omega)
    omega
  have hnavM : ∀ d : Nat, 14 + d ≤ roundCostLeft (q := q) Z k pre' cq s' →
      driveM q b ((simDrive q b tab s0).run (14 + d)
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state = m'.val := by
    intro d
    induction d with
    | zero =>
        intro _
        rw [simDrive_run14_left q b tab s0 m c hm hc x
          (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))
          cq pre' hq hprel m' s' hx h]
        rw [driveM_embN, codeState_unpackM]
    | succ d ih =>
        intro hC
        have hjC : 14 + d ≤ roundCostLeft (q := q) Z k pre' cq s' := by omega
        have hjlt : 14 + d < roundCostLeft (q := q) Z k pre' cq s' := by omega
        have h14 := ih hjC
        rw [show 14 + (d + 1) = 14 + d + 1 from by omega]
        have hconst := simDrive_run_driveM_nav_const q b tab s0
          ((simDrive q b tab s0).run (14 + d)
            (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
              (x.enc (none :: (some false) :: (List.replicate Z (some false)
                ++ (some true :: (List.replicate (k + 1) (some true)
                  ++ (xc :: X')))))))) 1
          (simDrive_run_range q b tab s0 (14 + d) _ hrange0)
          (by
            intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [simRun_zero]
            exact simDrive_roundFullNav_left q b tab s0 m c hm hc x Z k (k + 2)
              hk rfl xc X' hxc hpre cq pre' hq hprel m' s' hx h (14 + d) (by omega) hjlt)
          1 (by omega)
        rw [DTM.run_add (simDrive q b tab s0) (14 + d) 1 _]
        rw [hconst, h14]
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · rw [ite_eq_left (by omega : i ≤ 4)]
    have hst : ((simDrive q b tab s0).run i
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true)
              ++ (xc :: X')))))))).state.val < stateCount q b := by
      have hrun := simDrive_embS_run13 q b tab s0 m c hm hc
        (x.enc (none :: (some false) :: (List.replicate Z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) i (by omega)
      rw [hrun]
      simp only [embS, Fin.val_mk]
      exact Fin.isLt _
    rw [driveM, ite_eq_left hst]
    exact simDrive_roundM_le_stay q b tab s0 m c hm hc x Z k xc X' i (by omega)
  · rw [ite_eq_right (by omega : ¬ i ≤ 4)]
    by_cases hi13 : i ≤ 13
    · have hst : ((simDrive q b tab s0).run i
          (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
            (x.enc (none :: (some false) :: (List.replicate Z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true)
                ++ (xc :: X')))))))).state.val < stateCount q b := by
        have hrun := simDrive_embS_run13 q b tab s0 m c hm hc
          (x.enc (none :: (some false) :: (List.replicate Z (some false)
            ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))) i (by omega)
        rw [hrun]
        simp only [embS, Fin.val_mk]
        exact Fin.isLt _
      rw [driveM, ite_eq_left hst]
      exact simDrive_roundM_ge q b tab s0 m c hm hc x Z k xc X' m' s' (d := Dir.left) hx h
        i hi5 hi13
    · have hi14 : 14 ≤ i := by omega
      rw [show i = 14 + (i - 14) from by omega]
      exact hnavM (i - 14) (by omega)


/-! ## 主定理：通路读数的尾部稳定性 -/

/-- **通路读数的尾部稳定性**：若前缀通路 `L1 ++ [k]` 成功（结果 `r`），则把它之后的
    数字区换成任意续块 `L2`（即整表 `L1 ++ (k :: L2)`）时，驱动层在 `r.steps` 步内
    每一时刻的「被模拟状态读数」都不变。
    注意：续写发生在前缀**之后**（`k :: L2`），这是 `passStart` 纸带差异只落在
    数字区最左端（远端尾部）的前提；`L2 = []` 时两条纸带完全相同。
    Tail stability of the pass reading: if the prefix pass `L1 ++ [k]` succeeds, then
    appending any blocks `L2` after it does not change the driver's simulated-state
    reading within `r.steps` steps. The continuation is appended after the prefix
    (`k :: L2`), so the two tapes differ only at the far tail of the digit area. -/
theorem simDrive_pass_readings_tail (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    ∀ (L1 : List Nat) (k : Nat) (L2 : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (m : Nat) (hm : m < q),
      x.state = (⟨m, hm⟩ : Fin q) →
      (∀ p0 ∈ x.pre, p0.2 = false) →
      (∀ p0 ∈ x.post, p0.2 = false) →
      (hb : ∀ k' ∈ L1 ++ [k], k' + 2 < 2 ^ b) →
      (hb2 : ∀ k' ∈ L1 ++ (k :: L2), k' + 2 < 2 ^ b) →
      ∀ (r : PassRes q b), passRun q b tab Z c hc x (L1 ++ [k]) hb = some r →
      ∀ i, i ≤ r.steps →
        driveM q b ((simDrive q b tab s0).run i (passStart x m c hm hc Z (L1 ++ [k]))).state
        = driveM q b ((simDrive q b tab s0).run i
            (passStart x m c hm hc Z (L1 ++ (k :: L2)))).state := by
  intro L1
  induction L1 with
  | nil =>
      intro k L2 Z c hc x m hm hx hpre hpost hb hb2 r hpass i hi
      simp only [List.nil_append] at hb hpass ⊢
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k [] hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k [] hb m' s' hpk] at hpass
              simp only [passRun, Option.map_some, Option.some.injEq] at hpass
              cases hpass
              have hk : k + 2 < 2 ^ b := hb2 k (by simp)
              have hi' : i ≤ roundCostStay x Z k s' := by simpa using hi
              rw [simDrive_passStart_roundDriveM_stay q b tab s0 x m c hm hc Z k []
                    hk hpre m' s' hx hpk i hi',
                  simDrive_passStart_roundDriveM_stay q b tab s0 x m c hm hc Z k L2
                    hk hpre m' s' hx hpk i hi']
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k [] hb m' s'
                    hpost0 hpk] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k [] hb m' s' p post'
                    hpost0 hpk] at hpass
                  simp only [passRun, Option.map_some, Option.some.injEq] at hpass
                  cases hpass
                  have hk : k + 2 < 2 ^ b := hb2 k (by simp)
                  have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                  have hi' : i ≤ roundCostRight x Z k p s' := by simpa using hi
                  rw [simDrive_passStart_roundDriveM_right q b tab s0 x m c hm hc Z k []
                        hk hpre p post' hp hpost0 m' s' hx hpk i hi',
                      simDrive_passStart_roundDriveM_right q b tab s0 x m c hm hc Z k L2
                        hk hpre p post' hp hpost0 m' s' hx hpk i hi']
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k [] hb m' s'
                    hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k [] hb m' s' cq preRev
                    hrev hpk] at hpass
                  simp only [passRun, Option.map_some, Option.some.injEq] at hpass
                  cases hpass
                  have hk : k + 2 < 2 ^ b := hb2 k (by simp)
                  have hprel : x.pre = preRev.reverse ++ [cq] := by
                    rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                  have hq : cq.2 = false :=
                    hpre cq (by rw [hprel]; exact List.mem_append_right _ (by simp))
                  have hi' : i ≤ roundCostLeft (q := q) Z k preRev.reverse cq s' := by
                    simpa using hi
                  rw [simDrive_passStart_roundDriveM_left q b tab s0 x m c hm hc Z k []
                        hk hpre cq preRev.reverse hq hprel m' s' hx hpk i hi',
                      simDrive_passStart_roundDriveM_left q b tab s0 x m c hm hc Z k L2
                        hk hpre cq preRev.reverse hq hprel m' s' hx hpk i hi']
  | cons k0 L1' ih =>
      intro k L2 Z c hc x m hm hx hpre hpost hb hb2 r hpass i hi
      simp only [List.cons_append] at hb hb2 hpass ⊢
      have hkb : k0 + 2 < 2 ^ b := hb k0 (by simp)
      have hb1 : ∀ k' ∈ L1' ++ [k], k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (List.mem_cons_of_mem k0 hk')
      have hb2' : ∀ k' ∈ L1' ++ (k :: L2), k' + 2 < 2 ^ b :=
        fun k' hk' => hb2 k' (List.mem_cons_of_mem k0 hk')
      obtain ⟨xc1, X1', htail1⟩ := digitArea_split (L1' ++ [k])
      obtain ⟨xc2, X2', htail2⟩ := digitArea_split (L1' ++ (k :: L2))
      have hxc1 : xc1 ≠ some true := digitArea_head_ne_true _ _ _ htail1
      have hxc2 : xc2 ≠ some true := digitArea_head_ne_true _ _ _ htail2
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k0 (L1' ++ [k]) hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k0 (L1' ++ [k]) hb m' s' hpk]
                at hpass
              cases hrec : passRun q b tab (Z + k0 + 3) (k0 + 1)
                  (by have := hb k0 (by simp); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post }
                  (L1' ++ [k]) hb1 with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  cases hpass
                  have hcK : k0 + 1 < 2 ^ b := by omega
                  rcases Nat.lt_or_ge i (roundCostStay x Z k0 s' + 1) with hiC | hiC
                  · have h1 := simDrive_passStart_roundDriveM_stay q b tab s0 x m c hm hc
                        Z k0 (L1' ++ [k]) hkb hpre m' s' hx hpk i (by omega)
                    have h2 := simDrive_passStart_roundDriveM_stay q b tab s0 x m c hm hc
                        Z k0 (L1' ++ (k :: L2)) hkb hpre m' s' hx hpk i (by omega)
                    rw [h1, h2]
                  · have hi' : i - roundCostStay x Z k0 s' ≤ r0.steps := by
                      have hi2 : i ≤ roundCostStay x Z k0 s' + r0.steps := by simpa using hi
                      omega
                    have hone1 : (simDrive q b tab s0).run i
                        (passStart x m c hm hc Z (k0 :: (L1' ++ [k])))
                        = (simDrive q b tab s0).run (i - roundCostStay x Z k0 s')
                            (passStart { state := m', pre := x.pre, cur := s', post := x.post }
                              m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3) (L1' ++ [k])) := by
                      conv =>
                        lhs
                        rw [show i = roundCostStay x Z k0 s'
                          + (i - roundCostStay x Z k0 s') from by omega]
                      rw [DTM.run_add]
                      rw [show (simDrive q b tab s0).run (roundCostStay x Z k0 s')
                            (passStart x m c hm hc Z (k0 :: (L1' ++ [k])))
                          = passStart { state := m', pre := x.pre, cur := s', post := x.post }
                              m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3) (L1' ++ [k]) from by
                        rw [simDrive_roundCanon_stay q b tab s0 m c hm hc x Z k0 (k0 + 2)
                          hkb rfl xc1 X1' hxc1 hpre m' s' hx hpk (L1' ++ [k]) htail1]
                        exact passStart_hc_irrel q b _ m'.val (k0 + 1) m'.isLt
                          (by omega) hcK (Z + k0 + 3) (L1' ++ [k])]
                    have hone2 : (simDrive q b tab s0).run i
                        (passStart x m c hm hc Z (k0 :: (L1' ++ (k :: L2))))
                        = (simDrive q b tab s0).run (i - roundCostStay x Z k0 s')
                            (passStart { state := m', pre := x.pre, cur := s', post := x.post }
                              m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                              (L1' ++ (k :: L2))) := by
                      conv =>
                        lhs
                        rw [show i = roundCostStay x Z k0 s'
                          + (i - roundCostStay x Z k0 s') from by omega]
                      rw [DTM.run_add]
                      rw [show (simDrive q b tab s0).run (roundCostStay x Z k0 s')
                            (passStart x m c hm hc Z (k0 :: (L1' ++ (k :: L2))))
                          = passStart { state := m', pre := x.pre, cur := s', post := x.post }
                              m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3) (L1' ++ (k :: L2)) from by
                        rw [simDrive_roundCanon_stay q b tab s0 m c hm hc x Z k0 (k0 + 2)
                          hkb rfl xc2 X2' hxc2 hpre m' s' hx hpk (L1' ++ (k :: L2)) htail2]
                        exact passStart_hc_irrel q b _ m'.val (k0 + 1) m'.isLt
                          (by omega) hcK (Z + k0 + 3) (L1' ++ (k :: L2))]
                    rw [hone1, hone2]
                    refine ih k L2 (Z + k0 + 3) (k0 + 1) hcK
                      { state := m', pre := x.pre, cur := s', post := x.post }
                      m'.val m'.isLt ?_ hpre hpost hb1 hb2' r0 hrec
                      (i - roundCostStay x Z k0 s') hi'
                    cases m'; rfl
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k0 (L1' ++ [k]) hb
                    m' s' hpost0 hpk] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k0 (L1' ++ [k]) hb m' s'
                    p post' hpost0 hpk] at hpass
                  cases hrec : passRun q b tab (Z + k0 + 3) (k0 + 1)
                      (by have := hb k0 (by simp); omega)
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      (L1' ++ [k]) hb1 with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                      have hpreR : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_append.mp hp0 with hp0' | hp0'
                        · exact hpre p0 hp0'
                        · rw [List.mem_singleton] at hp0'
                          subst hp0'
                          rfl
                      have hpostR : ∀ p0 ∈ post', p0.2 = false :=
                        fun p0 hp0 => hpost p0 (by rw [hpost0]; exact List.mem_cons_of_mem _ hp0)
                      have hcK : k0 + 1 < 2 ^ b := by omega
                      rcases Nat.lt_or_ge i (roundCostRight x Z k0 p s' + 1) with hiC | hiC
                      · have h1 := simDrive_passStart_roundDriveM_right q b tab s0 x m c hm hc
                            Z k0 (L1' ++ [k]) hkb hpre p post' hp hpost0 m' s' hx hpk i (by omega)
                        have h2 := simDrive_passStart_roundDriveM_right q b tab s0 x m c hm hc
                            Z k0 (L1' ++ (k :: L2)) hkb hpre p post' hp hpost0 m' s' hx hpk
                            i (by omega)
                        rw [h1, h2]
                      · have hi' : i - roundCostRight x Z k0 p s' ≤ r0.steps := by
                          have hi2 : i ≤ roundCostRight x Z k0 p s' + r0.steps := by simpa using hi
                          omega
                        have hone1 : (simDrive q b tab s0).run i
                            (passStart x m c hm hc Z (k0 :: (L1' ++ [k])))
                            = (simDrive q b tab s0).run (i - roundCostRight x Z k0 p s')
                                (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3) (L1' ++ [k])) := by
                          conv =>
                            lhs
                            rw [show i = roundCostRight x Z k0 p s'
                              + (i - roundCostRight x Z k0 p s') from by omega]
                          rw [DTM.run_add]
                          rw [show (simDrive q b tab s0).run (roundCostRight x Z k0 p s')
                                (passStart x m c hm hc Z (k0 :: (L1' ++ [k])))
                              = passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ [k]) from by
                            rw [simDrive_roundCanon_right q b tab s0 m c hm hc x Z k0 (k0 + 2)
                              hkb rfl xc1 X1' hxc1 hpre p post' hp hpost0 m' s' hx hpk
                              (L1' ++ [k]) htail1]
                            exact passStart_hc_irrel q b _ m'.val (k0 + 1) m'.isLt
                              (by omega) hcK (Z + k0 + 3) (L1' ++ [k])]
                        have hone2 : (simDrive q b tab s0).run i
                            (passStart x m c hm hc Z (k0 :: (L1' ++ (k :: L2))))
                            = (simDrive q b tab s0).run (i - roundCostRight x Z k0 p s')
                                (passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ (k :: L2))) := by
                          conv =>
                            lhs
                            rw [show i = roundCostRight x Z k0 p s'
                              + (i - roundCostRight x Z k0 p s') from by omega]
                          rw [DTM.run_add]
                          rw [show (simDrive q b tab s0).run (roundCostRight x Z k0 p s')
                                (passStart x m c hm hc Z (k0 :: (L1' ++ (k :: L2))))
                              = passStart { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ (k :: L2)) from by
                            rw [simDrive_roundCanon_right q b tab s0 m c hm hc x Z k0 (k0 + 2)
                              hkb rfl xc2 X2' hxc2 hpre p post' hp hpost0 m' s' hx hpk
                              (L1' ++ (k :: L2)) htail2]
                            exact passStart_hc_irrel q b _ m'.val (k0 + 1) m'.isLt
                              (by omega) hcK (Z + k0 + 3) (L1' ++ (k :: L2))]
                        rw [hone1, hone2]
                        refine ih k L2 (Z + k0 + 3) (k0 + 1) hcK
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                          m'.val m'.isLt ?_ hpreR hpostR hb1 hb2' r0 hrec
                          (i - roundCostRight x Z k0 p s') hi'
                        cases m'; rfl
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k0 (L1' ++ [k]) hb
                    m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k0 (L1' ++ [k]) hb m' s'
                    cq preRev hrev hpk] at hpass
                  cases hrec : passRun q b tab (Z + k0 + 3) (k0 + 1)
                      (by have := hb k0 (by simp); omega)
                      (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post))
                      (L1' ++ [k]) hb1 with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      have hprel : x.pre = preRev.reverse ++ [cq] := by
                        rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                      have hq : cq.2 = false :=
                        hpre cq (by rw [hprel]; exact List.mem_append_right _ (by simp))
                      have hpreL : ∀ p0 ∈ preRev.reverse, p0.2 = false := by
                        intro p0 hp0
                        exact hpre p0 (by rw [hprel]; exact List.mem_append_left _ hp0)
                      have hpostL : ∀ p0 ∈ (s', false) :: x.post, p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_cons.mp hp0 with hp0' | hp0'
                        · subst hp0'
                          rfl
                        · exact hpost p0 hp0'
                      have hcK : k0 + 1 < 2 ^ b := by omega
                      rcases Nat.lt_or_ge i (roundCostLeft (q := q) Z k0 preRev.reverse cq s' + 1)
                        with hiC | hiC
                      · have h1 := simDrive_passStart_roundDriveM_left q b tab s0 x m c hm hc
                            Z k0 (L1' ++ [k]) hkb hpre cq preRev.reverse hq hprel m' s' hx hpk
                            i (by omega)
                        have h2 := simDrive_passStart_roundDriveM_left q b tab s0 x m c hm hc
                            Z k0 (L1' ++ (k :: L2)) hkb hpre cq preRev.reverse hq hprel
                            m' s' hx hpk i (by omega)
                        rw [h1, h2]
                      · have hi' : i - roundCostLeft (q := q) Z k0 preRev.reverse cq s'
                            ≤ r0.steps := by
                          have hi2 : i ≤ roundCostLeft (q := q) Z k0 preRev.reverse cq s'
                            + r0.steps := by simpa using hi
                          omega
                        have hone1 : (simDrive q b tab s0).run i
                            (passStart x m c hm hc Z (k0 :: (L1' ++ [k])))
                            = (simDrive q b tab s0).run
                                (i - roundCostLeft (q := q) Z k0 preRev.reverse cq s')
                                (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ [k])) := by
                          conv =>
                            lhs
                            rw [show i = roundCostLeft (q := q) Z k0 preRev.reverse cq s'
                              + (i - roundCostLeft (q := q) Z k0 preRev.reverse cq s') from by omega]
                          rw [DTM.run_add]
                          rw [show (simDrive q b tab s0).run
                                (roundCostLeft (q := q) Z k0 preRev.reverse cq s')
                                (passStart x m c hm hc Z (k0 :: (L1' ++ [k])))
                              = passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ [k]) from by
                            rw [simDrive_roundCanon_left q b tab s0 m c hm hc x Z k0 (k0 + 2)
                              hkb rfl xc1 X1' hxc1 hpre cq preRev.reverse hq hprel m' s' hx hpk
                              (L1' ++ [k]) htail1]
                            exact passStart_hc_irrel q b _ m'.val (k0 + 1) m'.isLt
                              (by omega) hcK (Z + k0 + 3) (L1' ++ [k])]
                        have hone2 : (simDrive q b tab s0).run i
                            (passStart x m c hm hc Z (k0 :: (L1' ++ (k :: L2))))
                            = (simDrive q b tab s0).run
                                (i - roundCostLeft (q := q) Z k0 preRev.reverse cq s')
                                (passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ (k :: L2))) := by
                          conv =>
                            lhs
                            rw [show i = roundCostLeft (q := q) Z k0 preRev.reverse cq s'
                              + (i - roundCostLeft (q := q) Z k0 preRev.reverse cq s') from by omega]
                          rw [DTM.run_add]
                          rw [show (simDrive q b tab s0).run
                                (roundCostLeft (q := q) Z k0 preRev.reverse cq s')
                                (passStart x m c hm hc Z (k0 :: (L1' ++ (k :: L2))))
                              = passStart { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }
                                  m'.val (k0 + 1) m'.isLt hcK (Z + k0 + 3)
                                  (L1' ++ (k :: L2)) from by
                            rw [simDrive_roundCanon_left q b tab s0 m c hm hc x Z k0 (k0 + 2)
                              hkb rfl xc2 X2' hxc2 hpre cq preRev.reverse hq hprel m' s' hx hpk
                              (L1' ++ (k :: L2)) htail2]
                            exact passStart_hc_irrel q b _ m'.val (k0 + 1) m'.isLt
                              (by omega) hcK (Z + k0 + 3) (L1' ++ (k :: L2))]
                        rw [hone1, hone2]
                        refine ih k L2 (Z + k0 + 3) (k0 + 1) hcK
                          { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }
                          m'.val m'.isLt ?_ hpreL hpostL hb1 hb2' r0 hrec
                          (i - roundCostLeft (q := q) Z k0 preRev.reverse cq s') hi'
                        cases m'; rfl

end DTM

end Pnp
