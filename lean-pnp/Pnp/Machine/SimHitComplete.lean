/-
  文件：Pnp/Machine/SimHitComplete.lean
  主题：观察命中**完备性**（B5 反向方向 #115b）——通路成功且终态区域是接受态时，
        观察机必在通路步数预算内命中接受哨兵 `obsAcc`。

  这是 #115 的最后一块：`simObs_pass_obs_upto`（区间可观察性）给出「通路内部无接受态 ⇒
  全程可观察」，本文件把「终态接受」通过按块归纳转成「观察机在预算内命中」。
  单轮用 `simObs_run_accept` 在驱动第 5 步的接受态命中（第 6 步进哨兵）；
  多轮用 `DTM.run_add` 把首轮命中拼接，并把续段交归纳假设。

  Observer-hit completeness (#115b): a successful pass whose final region is
  accepting makes `simObs` reach `obsAcc` within the pass step budget.
-/

import Pnp.Machine.SimHitRange
import Pnp.Machine.PadBranch

set_option maxHeartbeats 2000000

namespace Pnp

namespace DTM

/-- 单轮（原地）耗时至少 14 步。A stay round costs at least 14 steps. -/
theorem roundCostStay_ge {q : Nat} (x : Reg q) (z k : Nat) (s' : Sym) :
    14 ≤ roundCostStay x z k s' := by
  unfold roundCostStay; omega

/-- 单轮（右移）耗时至少 14 步。A right round costs at least 14 steps. -/
theorem roundCostRight_ge {q : Nat} (x : Reg q) (z k : Nat) (p : Sym × Bool) (s' : Sym) :
    14 ≤ roundCostRight x z k p s' := by
  unfold roundCostRight; omega

/-- 单轮（左移）耗时至少 14 步。A left round costs at least 14 steps. -/
theorem roundCostLeft_ge {q : Nat} (z k : Nat) (pre' : List (Sym × Bool))
    (cq : Sym × Bool) (s' : Sym) :
    14 ≤ roundCostLeft (q := q) z k pre' cq s' := by
  unfold roundCostLeft; omega

/-- **单轮命中**（方向无关）：单轮通路成功、终态区域是接受态（即查表命中 `m' = accept`）
    时，观察机在第 6 步入接受哨兵，且 `6 ≤ r.steps`（单轮至少 14 步）。
    Single-round accept hit (direction-agnostic): if the looked-up next state is the
    accepting state, `simObs` reaches `obsAcc` at step 6, within the round budget. -/
theorem hit_of_single_round (q b : Nat) (M : NTM q)
    (x : Reg q) (m c Z : Nat) (hm : m < q) (hc : c < 2 ^ b) (k : Nat)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ k :: [], k' + 2 < 2 ^ b) (r : PassRes q b)
    (hpass : passRun q b (M.haltNorm).step Z c hc x (k :: []) hb = some r)
    (m' : Fin q) (s' : Sym) (d : Dir)
    (hpk : pick ((M.haltNorm).step x.state x.cur) c = some (m', s', d))
    (hmacc : m' = (M.haltNorm).accept)
    (hsteps : 6 ≤ r.steps) :
    ∃ n, n ≤ r.steps ∧
      ((simObs q b (M.haltNorm)).run n
        (obsStart q b M x m c Z hm hc (k :: []))).state = obsAcc q b := by
  -- 起点状态不是接受态（否则查表必失败，与 `hpk` 矛盾）
  have hxne : x.state ≠ (M.haltNorm).accept := by
    intro he
    have h0 := pick_haltNorm_none M x c (Or.inl he)
    rw [h0] at hpk; cases hpk
  have hmne : m ≠ (M.haltNorm).accept.val := by
    intro he
    apply hxne
    rw [hx]
    exact Fin.ext he
  have hN5 : 5 ≤ r.steps := by omega
  -- 前 5 步观察层状态都是起点 `m`（故非接受）
  have hobs := simObs_pass_obs_upto q b (M.haltNorm) (k :: []) Z c hc x m hm hx hpre hpost
    hb r hpass 5 hN5 (by
      intro i hi h
      rw [simDrive_passStart_unpackM_le q b (M.haltNorm).step (M.haltNorm).start
        x m c hm hc Z (k :: []) i (by omega)]
      exact hmne)
  -- 驱动第 5 步仍在模拟层且已是接受态
  have hlt5 : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run 5
      (passStart x m c hm hc Z (k :: []))).state.val < stateCount q b := by
    rw [simDrive_passStart_run13 q b (M.haltNorm).step (M.haltNorm).start
      x m c hm hc Z (k :: []) 5 (by decide)]
    simp only [Config.state, embS, Fin.val_mk]
    exact ((simStep q b (M.haltNorm).step (M.haltNorm).start).run 5 _).state.isLt
  have hacc5 : unpackM (2 ^ b) 9 15
      ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run 5
        (passStart x m c hm hc Z (k :: []))).state.val = (M.haltNorm).accept.val := by
    rw [simDrive_passStart_unpackM_ge q b (M.haltNorm).step (M.haltNorm).start
      x m c hm hc Z (k :: []) m' s' d hx hpk 5 (by decide) (by decide)]
    exact congrArg Fin.val hmacc
  refine ⟨6, hsteps, ?_⟩
  exact simObs_run_accept q b (M.haltNorm) 5 (passStart x m c hm hc Z (k :: []))
    (fun j hj => hobs j hj) hlt5 hacc5

/-- 区域一步的下一状态就是查表所得的状态（方向无关）。 -/
theorem regStep_state_of_pick {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (c : Nat) (x y : Reg q) (m' : Fin q) (s' : Sym) (d : Dir)
    (hpick : pick (tab x.state x.cur) c = some (m', s', d))
    (h : Reg.step tab c x = some y) : y.state = m' := by
  cases d with
  | stay =>
      rw [Reg.step, hpick] at h
      simp only [Option.some.injEq] at h
      rw [← h]
  | right =>
      cases hpost : x.post with
      | nil => rw [Reg.step, hpick, hpost] at h; cases h
      | cons p post' =>
          rw [Reg.step, hpick, hpost] at h
          simp only [Option.some.injEq] at h
          rw [← h]
  | left =>
      cases hrev : x.pre.reverse with
      | nil => rw [Reg.step, hpick, hrev] at h; cases h
      | cons cq preRev =>
          rw [Reg.step, hpick, hrev] at h
          simp only [Option.some.injEq] at h
          rw [← h]

/-- 非空通路至少 14 步（每轮至少 14 步，至少一轮）。 -/
theorem passRun_steps_ge (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b),
      L ≠ [] → passRun q b tab Z c hc x L hb = some r → 14 ≤ r.steps := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ hnil; exact absurd rfl hnil
  | cons k ks ih =>
      intro Z c hc x hb r hnil hpass
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1) _
                  ({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q) ks _ with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  have hr : r = ⟨roundCostStay x Z k s' + r0.steps, r0.z, r0.c, r0.hc, r0.reg⟩ :=
                    hpass.symm
                  rw [hr]
                  dsimp only
                  have := roundCostStay_ge x Z k s'
                  omega
          | right =>
              cases hpost : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hpost hpk] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) _
                      ({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        : Reg q) ks _ with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      have hr : r = ⟨roundCostRight x Z k p s' + r0.steps, r0.z, r0.c, r0.hc,
                        r0.reg⟩ := hpass.symm
                      rw [hr]
                      dsimp only
                      have := roundCostRight_ge x Z k p s'
                      omega
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) _
                      ({ state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) }
                        : Reg q) ks _ with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      have hr : r = ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r0.steps,
                        r0.z, r0.c, r0.hc, r0.reg⟩ := hpass.symm
                      rw [hr]
                      dsimp only
                      have := roundCostLeft_ge (q := q) Z k preRev.reverse cq s'
                      omega

/-- 单步迭代恰是一步 `Reg.step`。A singleton choice list iterates a single `Reg.step`. -/
theorem stepCs_singleton {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (c : Nat) (x : Reg q) : stepCs tab [c] x = Reg.step tab c x := by
  simp only [stepCs]
  cases Reg.step tab c x <;> rfl

/-- `passStart` 对计数器值做等价替换（依赖证明随之搬运）。
    `passStart` is invariant under a proof-carrying replacement of the counter value. -/
theorem passStart_c_irrel (q b : Nat) (x : Reg q) (m : Nat) (hm : m < q) (Z : Nat)
    (ks : List Nat) (c1 c2 : Nat) (hc1 : c1 < 2 ^ b) (hc2 : c2 < 2 ^ b) (h : c1 = c2) :
    passStart x m c1 hm hc1 Z ks = passStart x m c2 hm hc2 Z ks := by
  cases h
  exact passStart_hc_irrel q b x m _ hm _ _ Z ks

/-- **多轮组合核（方向无关）**：给定首轮可观察（`hnoacc`）、首轮末观察机到达续段起点
    （`hcan`）、以及续段命中的归纳结果（`ihit`），则整条通路也命中。
    Direction-agnostic multi-round core: first-round observability (`hnoacc`), the
    first-round canon (`hcan`) and the tail hit (`ihit`) combine to a whole-pass hit. -/
theorem hit_of_multi_round (q b : Nat) (M : NTM q)
    (x : Reg q) (m c Z : Nat) (hm : m < q) (hc : c < 2 ^ b) (k : Nat) (ks : List Nat)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b)
    (roundCost : Nat) (netReg : Reg q) (m' : Nat) (hm' : m' < q)
    (hcTail : (k + 1) < 2 ^ b)
    (r r0 : PassRes q b)
    (hpass : passRun q b (M.haltNorm).step Z c hc x (k :: ks) hb = some r)
    (hr : r.steps = roundCost + r0.steps)
    (hnoacc : ∀ i : Nat, i < roundCost → ∀ (h : ((simDrive q b (M.haltNorm).step
        (M.haltNorm).start).run i (passStart x m c hm hc Z (k :: ks))).state.val
        < stateCount q b), unpackM (2 ^ b) 9 15 ((simDrive q b (M.haltNorm).step
        (M.haltNorm).start).run i (passStart x m c hm hc Z (k :: ks))).state.val
        ≠ (M.haltNorm).accept.val)
    (hcan : (simDrive q b (M.haltNorm).step (M.haltNorm).start).run roundCost
              (passStart x m c hm hc Z (k :: ks))
              = passStart netReg m' (k + 1) hm' hcTail (Z + k + 3) ks)
    (ihit : ∃ n, n ≤ r0.steps ∧ ((simObs q b (M.haltNorm)).run n
              (obsStart q b M netReg m' (k + 1) (Z + k + 3) hm' hcTail ks)).state
              = obsAcc q b) :
    ∃ n, n ≤ r.steps ∧ ((simObs q b (M.haltNorm)).run n
              (obsStart q b M x m c Z hm hc (k :: ks))).state = obsAcc q b := by
  obtain ⟨n_tail, hnt, hhit⟩ := ihit
  have hN : roundCost ≤ r.steps := by rw [hr]; omega
  have hobs := simObs_pass_obs_upto q b (M.haltNorm) (k :: ks) Z c hc x m hm hx hpre
    hpost hb r hpass roundCost hN hnoacc
  have hchain : (simObs q b (M.haltNorm)).run roundCost
      (obsStart q b M x m c Z hm hc (k :: ks))
      = obsStart q b M netReg m' (k + 1) (Z + k + 3) hm' hcTail ks := by
    have hrun := simObs_run_delegate q b (M.haltNorm) roundCost
      (passStart x m c hm hc Z (k :: ks)) hobs
    simp only [obsStart]
    rw [hrun, hcan]
  refine ⟨roundCost + n_tail, ?_, ?_⟩
  · rw [hr]; omega
  · rw [DTM.run_add (simObs q b (M.haltNorm)) roundCost n_tail
      (obsStart q b M x m c Z hm hc (k :: ks)), hchain]
    exact hhit

/-- **观察命中完备性（#115b）**：通路成功且终态区域为接受态 ⇒ 观察机在通路步数预算内
    必命中接受哨兵 `obsAcc`。按块归纳：单轮用 `hit_of_single_round`；多轮用 `hit_of_multi_round`
    把首轮可观察、首轮规范形与续段归纳结果拼起来。
    Observer-hit completeness (#115b): a successful pass whose final region is accepting
    makes `simObs` reach `obsAcc` within the pass step budget. -/
theorem exists_obs_acc_of_passRun_accept (q b : Nat) (M : NTM q) :
    ∀ (L : List Nat), L ≠ [] →
      ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q),
        x.state = (⟨m, hm⟩ : Fin q) →
        (∀ p0 ∈ x.pre, p0.2 = false) →
        (∀ p0 ∈ x.post, p0.2 = false) →
        (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) →
        ∀ (r : PassRes q b), passRun q b (M.haltNorm).step Z c hc x L hb = some r →
          r.reg.state = (M.haltNorm).accept →
          ∃ n, n ≤ r.steps ∧
            ((simObs q b (M.haltNorm)).run n
              (obsStart q b M x m c Z hm hc L)).state = obsAcc q b := by
  intro L
  induction L with
  | nil => intro hnil; exact absurd rfl hnil
  | cons k ks ih =>
      intro _ Z c hc x m hm hx hpre hpost hb r hpass hacc
      cases ks with
      | nil =>
          -- 单轮
          cases hpk : pick ((M.haltNorm).step x.state x.cur) c with
          | none =>
              rw [passRun_none_unfold q b (M.haltNorm).step Z c hc x k [] hb hpk] at hpass
              cases hpass
          | some v =>
              obtain ⟨m', s', d⟩ := v
              have hreg := passRun_reg q b (M.haltNorm).step (k :: []) c Z hc x hb r hpass
              have hstep : Reg.step ((M.haltNorm).step) c x = some r.reg := by
                rw [show passChoices c (k :: []) = [c] from rfl, stepCs_singleton] at hreg
                exact hreg
              have hregst : r.reg.state = m' :=
                regStep_state_of_pick ((M.haltNorm).step) c x r.reg m' s' d hpk hstep
              have hmacc : m' = (M.haltNorm).accept := by rw [← hregst]; exact hacc
              have hsteps : 6 ≤ r.steps := by
                have h14 := passRun_steps_ge q b (M.haltNorm).step (k :: []) Z c hc x hb r
                  (by simp) hpass
                omega
              exact hit_of_single_round q b M x m c Z hm hc k hx hpre hpost hb r hpass
                m' s' d hpk hmacc hsteps
      | cons k' ks' =>
          obtain ⟨xc, X', htail⟩ := digitArea_split (k' :: ks')
          have hpassKeep : passRun q b (M.haltNorm).step Z c hc x (k :: (k' :: ks')) hb
              = some r := hpass
          have hxc := digitArea_head_ne_true (k' :: ks') xc X' htail
          have hkb : k + 2 < 2 ^ b := hb k (by rw [List.mem_cons]; exact Or.inl rfl)
          cases hpk : pick ((M.haltNorm).step x.state x.cur) c with
          | none =>
              rw [passRun_none_unfold q b (M.haltNorm).step Z c hc x k (k' :: ks') hb hpk]
                at hpass
              cases hpass
          | some v =>
              obtain ⟨m', s', d⟩ := v
              -- 起点状态非接受（由查表成功得）
              have hmnev_start : m ≠ (M.haltNorm).accept.val := by
                intro hev
                have hstate : x.state = M.accept := by rw [hx]; exact Fin.ext hev
                have hnone := pick_haltNorm_none M x c (Or.inl hstate)
                rw [hnone] at hpk; cases hpk
              cases d with
              | stay =>
                  rw [passRun_stay_unfold q b (M.haltNorm).step Z c hc x k (k' :: ks') hb m' s'
                    hpk] at hpass
                  cases hrec : passRun q b (M.haltNorm).step (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      { state := m', pre := x.pre, cur := s', post := x.post } (k' :: ks')
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      have hr_full : r = ⟨roundCostStay x Z k s' + r0.steps, r0.z, r0.c,
                        r0.hc, r0.reg⟩ := hpass.symm
                      have hr : r.steps = roundCostStay x Z k s' + r0.steps := by rw [hr_full]
                      have hacc0 : r0.reg.state = (M.haltNorm).accept := by
                        rw [hr_full] at hacc; exact hacc
                      have hx' : ({ state := m', pre := x.pre, cur := s', post := x.post }
                          : Reg q).state = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                      have ih_tail := ih (by simp) (Z + k + 3) (k + 1)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt
                        hx' hpre hpost
                        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                        hacc0
                      have hmne : m' ≠ (M.haltNorm).accept := by
                        intro he
                        obtain ⟨v2, hpv2⟩ := exists_pick_of_passRun_cons q b (M.haltNorm).step
                          (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := x.pre, cur := s', post := x.post } k' ks'
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                        have hstate : ({ state := m', pre := x.pre, cur := s', post := x.post }
                            : Reg q).state = M.accept := by show m' = M.accept; exact he
                        have hnone := pick_haltNorm_none M
                          { state := m', pre := x.pre, cur := s', post := x.post } (k + 1)
                          (Or.inl hstate)
                        rw [hnone] at hpv2; cases hpv2
                      have hmnev : m'.val ≠ (M.haltNorm).accept.val :=
                        fun hev => hmne (Fin.ext hev)
                      have hcan : (simDrive q b (M.haltNorm).step (M.haltNorm).start).run
                          (roundCostStay x Z k s') (passStart x m c hm hc Z (k :: (k' :: ks')))
                          = passStart ({ state := m', pre := x.pre, cur := s', post := x.post }
                              : Reg q) m'.val (k + 1) m'.isLt
                              (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                              (Z + k + 3) (k' :: ks') := by
                        have hcan0 := simDrive_roundCanon_stay q b (M.haltNorm).step
                          (M.haltNorm).start m c hm hc x Z k (k + 2) hkb rfl xc X' hxc hpre m' s'
                          hx hpk (k' :: ks') htail
                        rw [hcan0]
                        exact passStart_c_irrel q b
                          { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt
                          (Z + k + 3) (k' :: ks') ((k + 2) - 1) (k + 1) _
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          (by omega)
                      exact hit_of_multi_round q b M x m c Z hm hc k (k' :: ks') hx hpre hpost hb
                        (roundCostStay x Z k s')
                        { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        r r0 hpassKeep hr (by
                          intro i hi h
                          rcases simDrive_passStart_roundM_stay q b (M.haltNorm).step
                            (M.haltNorm).start x m c hm hc Z k (k' :: ks') xc X' htail hkb hxc
                            hpre m' s' hx hpk i (by omega) h with heq | heq
                          · rw [heq]; exact hmnev_start
                          · rw [heq]; exact hmnev) hcan ih_tail
              | right =>
                  cases hpost0 : x.post with
                  | nil =>
                      rw [passRun_right_nil_unfold q b (M.haltNorm).step Z c hc x k (k' :: ks') hb
                        m' s' hpost0 hpk] at hpass
                      cases hpass
                  | cons p post' =>
                      rw [passRun_right_unfold q b (M.haltNorm).step Z c hc x k (k' :: ks') hb m'
                        s' p post' hpost0 hpk] at hpass
                      have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                      have hpre' : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_append.mp hp0 with hp0' | hp0'
                        · exact hpre p0 hp0'
                        · rw [List.mem_singleton] at hp0'; subst hp0'; rfl
                      have hpost' : ∀ p0 ∈ post', p0.2 = false :=
                        fun p0 hp0 => hpost p0 (by rw [hpost0]; exact List.mem_cons_of_mem _ hp0)
                      cases hrec : passRun q b (M.haltNorm).step (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                          (k' :: ks')
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                      | none => rw [hrec] at hpass; cases hpass
                      | some r0 =>
                          rw [hrec] at hpass
                          simp only [Option.map_some, Option.some.injEq] at hpass
                          have hr_full : r = ⟨roundCostRight x Z k p s' + r0.steps, r0.z, r0.c,
                            r0.hc, r0.reg⟩ := hpass.symm
                          have hr : r.steps = roundCostRight x Z k p s' + r0.steps := by
                            rw [hr_full]
                          have hacc0 : r0.reg.state = (M.haltNorm).accept := by
                            rw [hr_full] at hacc; exact hacc
                          have hx' : (Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' : Reg q).state
                              = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                          have ih_tail := ih (by simp) (Z + k + 3) (k + 1)
                            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                            { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                            m'.val m'.isLt hx' hpre' hpost'
                            (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                            hacc0
                          have hmne : m' ≠ (M.haltNorm).accept := by
                            intro he
                            obtain ⟨v2, hpv2⟩ := exists_pick_of_passRun_cons q b (M.haltNorm).step
                              (Z + k + 3) (k + 1)
                              (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                              { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                              k' ks'
                              (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                            have hstate : (Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' : Reg q).state
                                = M.accept := by
                              show m' = M.accept; exact he
                            have hnone := pick_haltNorm_none M
                              { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                              (k + 1) (Or.inl hstate)
                            rw [hnone] at hpv2; cases hpv2
                          have hmnev : m'.val ≠ (M.haltNorm).accept.val :=
                            fun hev => hmne (Fin.ext hev)
                          have hcan : (simDrive q b (M.haltNorm).step (M.haltNorm).start).run
                              (roundCostRight x Z k p s')
                              (passStart x m c hm hc Z (k :: (k' :: ks')))
                              = passStart ({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } : Reg q) m'.val (k + 1) m'.isLt
                                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                                  (Z + k + 3) (k' :: ks') := by
                            have hcan0 := simDrive_roundCanon_right q b (M.haltNorm).step
                              (M.haltNorm).start m c hm hc x Z k (k + 2) hkb rfl xc X' hxc hpre p
                              post' hp hpost0 m' s' hx hpk (k' :: ks') htail
                            rw [hcan0]
                            exact passStart_c_irrel q b
                              { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                              m'.val m'.isLt (Z + k + 3) (k' :: ks') ((k + 2) - 1) (k + 1) _
                              (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                              (by omega)
                          exact hit_of_multi_round q b M x m c Z hm hc k (k' :: ks') hx hpre hpost hb
                            (roundCostRight x Z k p s')
                            { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                            m'.val m'.isLt
                            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                            r r0 hpassKeep hr (by
                              intro i hi h
                              rcases simDrive_passStart_roundM_right q b (M.haltNorm).step
                                (M.haltNorm).start x m c hm hc Z k (k' :: ks') xc X' htail hkb hxc
                                hpre p post' hp hpost0 m' s' hx hpk i (by omega) h with heq | heq
                              · rw [heq]; exact hmnev_start
                              · rw [heq]; exact hmnev) hcan ih_tail
              | left =>
                  cases hrev : x.pre.reverse with
                  | nil =>
                      rw [passRun_left_nil_unfold q b (M.haltNorm).step Z c hc x k (k' :: ks') hb
                        m' s' hrev hpk] at hpass
                      cases hpass
                  | cons cq preRev =>
                      rw [passRun_left_unfold q b (M.haltNorm).step Z c hc x k (k' :: ks') hb m'
                        s' cq preRev hrev hpk] at hpass
                      have hpre2 : x.pre = preRev.reverse ++ [cq] := by
                        rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                      have hq : cq.2 = false :=
                        hpre cq (by rw [hpre2]; exact List.mem_append_right _ (by simp))
                      have hpre' : ∀ p0 ∈ preRev.reverse, p0.2 = false := by
                        intro p0 hp0
                        exact hpre p0 (by rw [hpre2]; exact List.mem_append_left _ hp0)
                      have hpost' : ∀ p0 ∈ (s', false) :: x.post, p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_cons.mp hp0 with rfl | hp0'
                        · rfl
                        · exact hpost p0 hp0'
                      cases hrec : passRun q b (M.haltNorm).step (Z + k + 3) (k + 1)
                          (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                          { state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } (k' :: ks')
                          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                      | none => rw [hrec] at hpass; cases hpass
                      | some r0 =>
                          rw [hrec] at hpass
                          simp only [Option.map_some, Option.some.injEq] at hpass
                          have hr_full : r = ⟨roundCostLeft (q := q) Z k preRev.reverse cq s'
                            + r0.steps, r0.z, r0.c, r0.hc, r0.reg⟩ := hpass.symm
                          have hr : r.steps = roundCostLeft (q := q) Z k preRev.reverse cq s'
                            + r0.steps := by rw [hr_full]
                          have hacc0 : r0.reg.state = (M.haltNorm).accept := by
                            rw [hr_full] at hacc; exact hacc
                          have hx' : (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post) : Reg q).state
                              = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                          have ih_tail := ih (by simp) (Z + k + 3) (k + 1)
                            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                            { state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } m'.val m'.isLt hx' hpre' hpost'
                            (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                            hacc0
                          have hmne : m' ≠ (M.haltNorm).accept := by
                            intro he
                            obtain ⟨v2, hpv2⟩ := exists_pick_of_passRun_cons q b (M.haltNorm).step
                              (Z + k + 3) (k + 1)
                              (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                              { state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } k' ks'
                              (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                            have hstate : (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)
                                : Reg q).state = M.accept := by
                              show m' = M.accept; exact he
                            have hnone := pick_haltNorm_none M
                              { state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } (k + 1) (Or.inl hstate)
                            rw [hnone] at hpv2; cases hpv2
                          have hmnev : m'.val ≠ (M.haltNorm).accept.val :=
                            fun hev => hmne (Fin.ext hev)
                          have hcan : (simDrive q b (M.haltNorm).step (M.haltNorm).start).run
                              (roundCostLeft (q := q) Z k preRev.reverse cq s')
                              (passStart x m c hm hc Z (k :: (k' :: ks')))
                              = passStart ({ state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } : Reg q) m'.val (k + 1) m'.isLt
                                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                                  (Z + k + 3) (k' :: ks') := by
                            have hcan0 := simDrive_roundCanon_left q b (M.haltNorm).step
                              (M.haltNorm).start m c hm hc x Z k (k + 2) hkb rfl xc X' hxc hpre cq
                              preRev.reverse hq hpre2 m' s' hx hpk (k' :: ks') htail
                            rw [hcan0]
                            exact passStart_c_irrel q b
                              { state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } m'.val m'.isLt (Z + k + 3)
                              (k' :: ks') ((k + 2) - 1) (k + 1) _
                              (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                              (by omega)
                          exact hit_of_multi_round q b M x m c Z hm hc k (k' :: ks') hx hpre hpost hb
                            (roundCostLeft (q := q) Z k preRev.reverse cq s')
                            { state := m', pre := preRev.reverse, cur := cq.1, post := ((s', false) :: x.post) } m'.val m'.isLt
                            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                            r r0 hpassKeep hr (by
                              intro i hi h
                              rcases simDrive_passStart_roundM_left q b (M.haltNorm).step
                                (M.haltNorm).start x m c hm hc Z k (k' :: ks') xc X' htail hkb hxc
                                hpre cq preRev.reverse hq hpre2 m' s' hx hpk i (by omega) h with
                                heq | heq
                              · rw [heq]; exact hmnev_start
                              · rw [heq]; exact hmnev) hcan ih_tail

end DTM

end Pnp
