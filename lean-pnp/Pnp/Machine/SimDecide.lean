/-
  文件：Pnp/Machine/SimDecide.lean
  主题：分支观察机 `simObs`——在驱动 `simDrive` 之上加「接受检查」与「死亡检查」，
        把一条选择序列的模拟变成可观测的三值结局（接受 / 分支失败 / 继续）。

  背景（docs/decisions/auto-run-log.md #86 / #87）：
    - `simDrive` 在相位 13 无条件进入导航；相位 14（查表越界）原地停留。
      两者都不会停机，因此判定层必须显式观察状态号：
        * 模拟层状态 + 被模拟状态 `m = M.accept` → 接受哨兵（覆盖 t ≤ T 的全部接受）；
        * 模拟层相位 14（正常形机器 `haltNorm` 下即「跑到拒绝态或选择越界」）
          → 分支失败哨兵，由更外层的枚举换下一条选择序列；
        * 其余状态一律委托 `simDrive` 一步。
    - 接受检查放在**每个状态**上（而不是某条相位），这样「一轮内部是否出现接受」
      直接由状态轨迹决定，后续与通路层 `simDrive_pass` 组合时只需假设
      「途经状态 m ≠ accept」，不需要分析相位 0 出现的时机。
    - 步数上限由外层枚举（步数计数器）负责，本机自身**不做计数**。

  状态布局（共 `stateCountD + 2` 个状态）：
    - `0 .. stateCountD - 1`：原样对应 `simDrive` 状态空间；
    - `stateCountD`：接受哨兵；`stateCountD + 1`：分支失败哨兵；到达后原地停留。

  本文件给出：状态空间、`simObs` 定义、四种单步规格、「原状态不停机」与
  **观察投影**（可观察状态上 `simObs` 运行 = `simDrive` 运行的重编码）。
-/

import Pnp.Machine.SimPass

namespace Pnp

namespace DTM

/-- 观察层状态总数：驱动状态空间 + 接受哨兵 + 分支失败哨兵。 -/
def stateCountO (q b : Nat) : Nat := stateCountD q b + 2

/-- 驱动状态空间非空。 -/
theorem stateCountD_pos (q b : Nat) : 0 < stateCountD q b := by
  unfold stateCountD
  omega

/-- 观察层状态嵌入：驱动状态号原样放进观察层。 -/
def embO (q b : Nat) : Fin (stateCountD q b) → Fin (stateCountO q b) :=
  fun s => ⟨s.val, by have := s.isLt; unfold stateCountO; omega⟩

/-- 观察层接受哨兵。 -/
def obsAcc (q b : Nat) : Fin (stateCountO q b) :=
  ⟨stateCountD q b, by unfold stateCountO; omega⟩

/-- 观察层分支失败哨兵。 -/
def obsFail (q b : Nat) : Fin (stateCountO q b) :=
  ⟨stateCountD q b + 1, by unfold stateCountO; omega⟩

/-- 观察机转移：模拟层接受态 → 接受哨兵；相位 14 → 失败哨兵；其余委托 `simDrive`。 -/
def simObs (q b : Nat) (M : NTM q) : DTM (stateCountO q b) where
  step := fun s a =>
    if hw : s.val < stateCountD q b then
      if hi : s.val < stateCount q b then
        let m := unpackM (2 ^ b) 9 15 s.val
        if m = M.accept.val then
          -- 被模拟状态已是接受态：接受哨兵
          (obsAcc q b, a, Dir.stay)
        else if unpackPh (2 ^ b) 9 15 s.val = 14 then
          -- 查表越界：分支失败哨兵
          (obsFail q b, a, Dir.stay)
        else
          let r := (simDrive q b M.step M.start).step ⟨s.val, hw⟩ a
          (embO q b r.1, r.2.1, r.2.2)
      else
        -- 导航层：照搬 `simDrive`
        let r := (simDrive q b M.step M.start).step
          ⟨s.val, by unfold stateCountD at hw ⊢; omega⟩ a
        (embO q b r.1, r.2.1, r.2.2)
    else (s, a, Dir.stay)
  start := embO q b (simDrive q b M.step M.start).start
  accept := obsAcc q b
  reject := obsFail q b

/-- 观察层状态号与其在驱动层的原像一致。 -/
theorem embO_val (q b : Nat) (st : Fin (stateCountD q b)) : (embO q b st).val = st.val := rfl

/-! ## 单步规格 -/

/-- 模拟层且非接受、非相位 14：照搬 `simDrive` 一步。 -/
theorem simObs_step_delegate (q b : Nat) (M : NTM q)
    (s : Fin (stateCountO q b)) (hlt : s.val < stateCountD q b)
    (hin : s.val < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 s.val ≠ M.accept.val)
    (h14 : unpackPh (2 ^ b) 9 15 s.val ≠ 14) (a : Sym) :
    (simObs q b M).step s a =
    (⟨((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).1.val, by
        have := ((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).1.isLt
        unfold stateCountO
        omega⟩,
      ((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).2.1,
      ((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).2.2) := by
  unfold simObs
  dsimp only
  rw [dif_pos hlt]
  rw [dif_pos hin]
  rw [if_neg hacc, if_neg h14]
  rfl

/-- 导航层（状态号 ≥ 模拟层状态数）：照搬 `simDrive` 一步。 -/
theorem simObs_step_nav (q b : Nat) (M : NTM q)
    (s : Fin (stateCountO q b)) (hlt : s.val < stateCountD q b)
    (hge : ¬ s.val < stateCount q b) (a : Sym) :
    (simObs q b M).step s a =
    (⟨((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).1.val, by
        have := ((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).1.isLt
        unfold stateCountO
        omega⟩,
      ((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).2.1,
      ((simDrive q b M.step M.start).step ⟨s.val, hlt⟩ a).2.2) := by
  unfold simObs
  dsimp only
  rw [dif_pos hlt]
  rw [dif_neg hge]
  rfl

/-- 模拟层接受态：进入接受哨兵并原地停留。 -/
theorem simObs_step_accept (q b : Nat) (M : NTM q)
    (s : Fin (stateCountO q b)) (hlt : s.val < stateCountD q b)
    (hin : s.val < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 s.val = M.accept.val) (a : Sym) :
    (simObs q b M).step s a = (obsAcc q b, a, Dir.stay) := by
  unfold simObs
  dsimp only
  rw [dif_pos hlt]
  rw [dif_pos hin]
  rw [if_pos hacc]

/-- 模拟层相位 14：进入分支失败哨兵并原地停留。 -/
theorem simObs_step_fail (q b : Nat) (M : NTM q)
    (s : Fin (stateCountO q b)) (hlt : s.val < stateCountD q b)
    (hin : s.val < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 s.val ≠ M.accept.val)
    (h14 : unpackPh (2 ^ b) 9 15 s.val = 14) (a : Sym) :
    (simObs q b M).step s a = (obsFail q b, a, Dir.stay) := by
  unfold simObs
  dsimp only
  rw [dif_pos hlt]
  rw [dif_pos hin]
  rw [if_neg hacc]
  rw [if_pos h14]

/-- 原驱动空间内的状态在观察层不会停机（哨兵在驱动空间之外）。 -/
theorem simObs_halted_inner (q b : Nat) (M : NTM q)
    (s : Fin (stateCountO q b)) (hlt : s.val < stateCountD q b) (t : Tape) :
    (simObs q b M).halted (Config.mk s t) = false := by
  have hne1 : s ≠ obsAcc q b := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [obsAcc, Fin.val_mk] at hv
    omega
  have hne2 : s ≠ obsFail q b := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [obsFail, Fin.val_mk] at hv
    omega
  rw [DTM.halted]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, simObs]
  exact ⟨hne1, hne2⟩

/-! ## 观察投影：`simObs` 与 `simDrive` 的逐步一致 -/

/-- 可观察条件：状态在驱动空间内且不是哨兵；模拟层状态既不接受也不是相位 14。
    Observable condition: inside the drive space (not a sentinel), and in the
    simulation layer neither accepting nor in phase 14. -/
def observeState (q b : Nat) (M : NTM q) (st : Fin (stateCountD q b)) : Prop :=
  st.val < 2 * stateCount q b ∧
    ∀ (h : st.val < stateCount q b),
      unpackM (2 ^ b) 9 15 st.val ≠ M.accept.val ∧
        unpackPh (2 ^ b) 9 15 st.val ≠ 14

/-- 可观察状态下 `simDrive` 不停机。 -/
theorem simDrive_halted_of_observe (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (t : Tape) (hd : observeState q b M st) :
    (simDrive q b M.step M.start).halted (Config.mk st t) = false := by
  obtain ⟨hlt, -⟩ := hd
  have hne1 : st ≠ (simDrive q b M.step M.start).accept := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [simDrive, Fin.val_mk] at hv
    omega
  have hne2 : st ≠ (simDrive q b M.step M.start).reject := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [simDrive, Fin.val_mk] at hv
    omega
  rw [DTM.halted]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨hne1, hne2⟩

/-- 可观察状态下观察机与驱动层的单步格局一致。 -/
theorem simObs_stepConfig_delegate (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (t : Tape) (hd : observeState q b M st) :
    (simObs q b M).stepConfig (Config.mk (embO q b st) t)
      = Config.mk
          (embO q b
            ((simDrive q b M.step M.start).stepConfig (Config.mk st t)).state)
          ((simDrive q b M.step M.start).stepConfig (Config.mk st t)).tape := by
  obtain ⟨hlt, hph⟩ := hd
  by_cases h : st.val < stateCount q b
  · obtain ⟨hacc, h14⟩ := hph h
    have hs := simObs_step_delegate q b M (embO q b st) st.isLt h hacc h14 t.read
    rw [DTM.stepConfig, DTM.stepConfig]
    simp only [hs]
    rfl
  · have hs := simObs_step_nav q b M (embO q b st) st.isLt h t.read
    rw [DTM.stepConfig, DTM.stepConfig]
    simp only [hs]
    refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, rfl⟩
    apply Fin.ext
    simp only [embO, Fin.val_mk]

/-- **观察投影**：只要途经状态都可观察，`simObs` 的运行就是 `simDrive` 运行的
    重新编码（纸带与状态完全一致）。
    Observation projection: as long as every visited state is observable,
    `simObs` follows `simDrive` exactly. -/
theorem simObs_run_delegate (q b : Nat) (M : NTM q) :
    ∀ (n : Nat) (c : Config (stateCountD q b)),
      (∀ i : Nat, i < n → observeState q b M ((simDrive q b M.step M.start).run i c).state) →
      (simObs q b M).run n (Config.mk (embO q b c.state) c.tape)
        = Config.mk (embO q b ((simDrive q b M.step M.start).run n c).state)
            ((simDrive q b M.step M.start).run n c).tape := by
  intro n
  induction n with
  | zero =>
      intro c _
      simp only [DTM.run]
  | succ n ih =>
      intro c hd
      have hd0 := hd 0 (Nat.succ_pos n)
      have hSDhalt : (simDrive q b M.step M.start).halted c = false :=
        simDrive_halted_of_observe q b M c.state c.tape hd0
      have hWhalt : (simObs q b M).halted (Config.mk (embO q b c.state) c.tape) = false :=
        simObs_halted_inner q b M (embO q b c.state) c.state.isLt c.tape
      have hshift : ∀ i : Nat, i < n →
          observeState q b M ((simDrive q b M.step M.start).run i
            ((simDrive q b M.step M.start).run 1 c)).state := by
        intro i hi
        have h1 : (simDrive q b M.step M.start).run 1 c
            = (simDrive q b M.step M.start).stepConfig c :=
          DTM.run_succ_of_not_halted (simDrive q b M.step M.start) 0 c hSDhalt
        rw [h1]
        rw [← DTM.run_succ_of_not_halted (simDrive q b M.step M.start) i c hSDhalt]
        exact hd (i + 1) (by omega)
      have hstep := simObs_stepConfig_delegate q b M c.state c.tape hd0
      rw [DTM.run_succ_of_not_halted (simObs q b M) n
          (Config.mk (embO q b c.state) c.tape) hWhalt,
        DTM.run_succ_of_not_halted (simDrive q b M.step M.start) n c hSDhalt]
      rw [hstep]
      have h1 : (simDrive q b M.step M.start).run 1 c
          = (simDrive q b M.step M.start).stepConfig c :=
        DTM.run_succ_of_not_halted (simDrive q b M.step M.start) 0 c hSDhalt
      rw [← h1]
      exact ih ((simDrive q b M.step M.start).run 1 c) hshift

/-! ## 驱动层状态范围 -/

/-- 模拟层嵌入状态落在 `[0, 2·stateCount)` 内。 -/
theorem embS_range {q b : Nat} (st : Fin (stateCount q b)) :
    (embS st).val < 2 * stateCount q b := by
  simp only [embS, Fin.val_mk]
  have := st.isLt
  omega

/-- 导航层嵌入状态落在 `[0, 2·stateCount)` 内。 -/
theorem embN_range {q b : Nat} (st : Fin (stateCount q b)) :
    (embN st).val < 2 * stateCount q b := by
  simp only [embN, Fin.val_mk]
  have := st.isLt
  omega

/-- 范围内状态在驱动层不停机（停机哨兵号是 `2·stateCount`）。 -/
theorem simDrive_halted_of_range (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCountD q b)) (t : Tape) (h : st.val < 2 * stateCount q b) :
    (simDrive q b tab s0).halted (Config.mk st t) = false := by
  have hne1 : st ≠ (simDrive q b tab s0).accept := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [simDrive, Fin.val_mk] at hv
    omega
  have hne2 : st ≠ (simDrive q b tab s0).reject := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [simDrive, Fin.val_mk] at hv
    omega
  rw [DTM.halted]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨hne1, hne2⟩

/-- 驱动层一步保持状态范围。 -/
theorem simDrive_step_range (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCountD q b)) (a : Sym) (h : st.val < 2 * stateCount q b) :
    ((simDrive q b tab s0).step st a).1.val < 2 * stateCount q b := by
  by_cases hlt : st.val < stateCount q b
  · -- 模拟层：相位 13 进导航层，其余委托 `simStep`
    unfold simDrive
    dsimp only
    rw [dif_pos hlt]
    by_cases h13 : unpackPh (2 ^ b) 9 15 st.val = 13
    · rw [if_pos h13]
      by_cases ha : a = none
      · rw [if_pos ha]
        exact embN_range _
      · rw [if_neg ha]
        exact embN_range _
    · rw [if_neg h13]
      exact embS_range _
  · -- 导航层：所有出口都是嵌入或原地状态
    unfold simDrive
    dsimp only
    rw [dif_neg hlt]
    split
    · omega
    · repeat'
        first
        | split
        | exact h
        | exact embS_range _
        | exact embN_range _

/-- 驱动层运行保持状态范围。 -/
theorem simDrive_run_range (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    ∀ (n : Nat) (c : Config (stateCountD q b)),
      c.state.val < 2 * stateCount q b →
      ((simDrive q b tab s0).run n c).state.val < 2 * stateCount q b := by
  intro n
  induction n with
  | zero => intro c h; exact h
  | succ n ih =>
      intro c h
      by_cases hh : (simDrive q b tab s0).halted c = true
      · rw [DTM.run]
        simp only [hh, ite_true]
        exact h
      · have hf : (simDrive q b tab s0).halted c = false := by
          cases hv : (simDrive q b tab s0).halted c <;> simp_all
        rw [DTM.run]
        simp only [hf, Bool.false_eq_true, ite_false]
        apply ih
        have hstep : ((simDrive q b tab s0).stepConfig c).state.val
            < 2 * stateCount q b := by
          simp only [DTM.stepConfig, Config.state]
          exact simDrive_step_range q b tab s0 c.state c.tape.read h
        exact hstep

/-- 阶段 14 时 `simStep` 的下一步状态就是原状态（终止态）。 -/
theorem simStep_step_state_phase14 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    ((simStep q b tab s0).step st a).1 = st := by
  have hs := congrArg Config.state
    (simStep_step_phase14 q b tab s0 st a [] [] hP)
  simpa only [DTM.stepConfig, Config.state, Tape.read, List.headD] using hs

/-- 驱动层在模拟层阶段 14 的一步：状态不变。 -/
theorem simDrive_step_state_phase14 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    ((simDrive q b tab s0).step (embS st) a).1 = embS st := by
  have h13 : unpackPh (2 ^ b) 9 15 (embS st).val ≠ 13 := by
    simp only [embS, Fin.val_mk, hP]
    decide
  rw [simDrive_step_embS q b tab s0 st h13 a]
  simp only [simStep_step_state_phase14 q b tab s0 st a hP]

/-- 驱动层在模拟层阶段 14 的状态是死点：一步后状态不变。 -/
theorem simDrive_stepConfig_state_phase14 (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (st : Fin (stateCount q b)) (t : Tape)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    ((simDrive q b tab s0).stepConfig (Config.mk (embS st) t)).state = embS st := by
  rw [stepConfig_state]
  exact simDrive_step_state_phase14 q b tab s0 st t.read hP

/-- 一旦驱动层跑到阶段 14 的死点，其后 `m` 步的状态始终与死点相同。 -/
theorem simDrive_run_phase14_state (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Config (stateCountD q b)) (st : Fin (stateCount q b)) (i : Nat)
    (h : ((simDrive q b tab s0).run i c).state = embS st)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    ∀ m : Nat, ((simDrive q b tab s0).run (i + m) c).state = embS st := by
  intro m
  induction m with
  | zero => simpa using h
  | succ m ih =>
      rw [Nat.add_succ]
      have hcur : ((simDrive q b tab s0).run (i + m) c).state = embS st := ih
      have hrange : ((simDrive q b tab s0).run (i + m) c).state.val
          < 2 * stateCount q b := by
        rw [hcur]
        exact embS_range st
      have hnh : (simDrive q b tab s0).halted ((simDrive q b tab s0).run (i + m) c)
          = false :=
        simDrive_halted_of_range q b tab s0 _ _ hrange
      rw [run_succ_last _ _ _ hnh, stepConfig_state, hcur]
      exact simDrive_step_state_phase14 q b tab s0 st _ hP

/-- 起点格局的状态号在模拟层内。 -/
theorem passStart_state_lt (q b : Nat) (x : Reg q) (m c : Nat) (hm : m < q)
    (hc : c < 2 ^ b) (Z : Nat) (ks : List Nat) :
    (passStart x m c hm hc Z ks).state.val < stateCount q b := by
  simp only [passStart, Config.state, embS, Fin.val_mk]
  exact (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt

/-- 终点格局的状态号在模拟层内。 -/
theorem passEnd_state_lt (q b : Nat) (r : PassRes q b) :
    (passEnd r).state.val < stateCount q b := by
  simp only [passEnd, Config.state, embS, Fin.val_mk]
  exact (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
    (by decide) (by decide)).isLt

/-- 终点格局的阶段是 0。 -/
theorem passEnd_unpackPh (q b : Nat) (r : PassRes q b) :
    unpackPh (2 ^ b) 9 15 (passEnd r).state.val = 0 := by
  simp only [passEnd, Config.state, embS, Fin.val_mk]
  rw [codeState_unpackPh]

/-- **通路可观察性**：通路成功且内部无接受态时，`r.steps` 内途经的驱动状态
    都满足 `observeState`（范围 + 非接受 + 非阶段 14）。
    Observability along a successful pass: no accept and no stuck phase 14. -/
theorem simObs_pass_obs (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b M.step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b M.step M.start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b M.step M.start).run i
            (passStart x m c hm hc Z L)).state.val ≠ M.accept.val) :
    ∀ i : Nat, i < r.steps →
      observeState q b M ((simDrive q b M.step M.start).run i
        (passStart x m c hm hc Z L)).state := by
  intro i hi
  have hrun := simDrive_pass q b M.step M.start L Z c hc x m hm hx hpre hpost hb r hpass
  constructor
  · -- 状态范围
    have h0 : (passStart x m c hm hc Z L).state.val < 2 * stateCount q b := by
      have := passStart_state_lt q b x m c hm hc Z L
      omega
    exact simDrive_run_range q b M.step M.start i (passStart x m c hm hc Z L) h0
  · -- 非接受、非阶段 14
    intro hlt
    constructor
    · exact hnoacc i hi hlt
    · -- 阶段 14 是死点，会与终点阶段 0 矛盾
      intro h14
      have hstuck := simDrive_run_phase14_state q b M.step M.start
        (passStart x m c hm hc Z L) ⟨_, hlt⟩ i rfl h14 (r.steps - i)
      rw [show i + (r.steps - i) = r.steps from by omega, hrun] at hstuck
      have hp0 := passEnd_unpackPh q b r
      rw [hstuck] at hp0
      simp only [embS, Fin.val_mk] at hp0
      rw [h14] at hp0
      omega

/-- **观察机通路定理**：通路成功且内部不出现接受态时，观察机在同样步数后到达
    重编码的终点格局。
    Observer pass theorem: on a successful pass whose interior never accepts,
    `simObs` reaches the re-encoded end configuration in the same number of steps. -/
theorem simObs_pass (q b : Nat) (M : NTM q) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q),
      x.state = (⟨m, hm⟩ : Fin q) →
      (∀ p0 ∈ x.pre, p0.2 = false) →
      (∀ p0 ∈ x.post, p0.2 = false) →
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) →
      ∀ (r : PassRes q b), passRun q b M.step Z c hc x L hb = some r →
        (∀ i : Nat, i < r.steps →
          ∀ (h : ((simDrive q b M.step M.start).run i
              (passStart x m c hm hc Z L)).state.val < stateCount q b),
            unpackM (2 ^ b) 9 15
              ((simDrive q b M.step M.start).run i
                (passStart x m c hm hc Z L)).state.val ≠ M.accept.val) →
        (simObs q b M).run r.steps
            (Config.mk (embO q b (passStart x m c hm hc Z L).state)
              (passStart x m c hm hc Z L).tape)
          = Config.mk (embO q b (passEnd r).state) (passEnd r).tape := by
  intro L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
  have hrun := simDrive_pass q b M.step M.start L Z c hc x m hm hx hpre hpost hb r hpass
  have hobs := simObs_pass_obs q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
  rw [simObs_run_delegate q b M r.steps (passStart x m c hm hc Z L) hobs, hrun]


/-- 接受态的单步：观察机一步进入接受哨兵（状态层面）。 -/
theorem simObs_stepConfig_accept_state (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (t : Tape)
    (hlt : st.val < stateCountD q b) (hin : st.val < stateCount q b)
    (hacc : unpackM (2 ^ b) 9 15 st.val = M.accept.val) :
    ((simObs q b M).stepConfig (Config.mk (embO q b st) t)).state = obsAcc q b := by
  rw [stepConfig_state]
  rw [simObs_step_accept q b M (embO q b st) hlt hin hacc t.read]

/-- 观察机进入接受哨兵后不再离开（接受态是停机态）。 -/
theorem simObs_run_accept_persists (q b : Nat) (M : NTM q) :
    ∀ (n m : Nat) (c : Config (stateCountO q b)),
      ((simObs q b M).run n c).state = obsAcc q b →
      ((simObs q b M).run (n + m) c).state = obsAcc q b := by
  intro n m c h
  induction m with
  | zero => simpa using h
  | succ m ih =>
      have hhalt : (simObs q b M).halted ((simObs q b M).run (n + m) c) = true := by
        rw [halted_of_accept_or_reject (simObs q b M) _ (Or.inl ih)]
      rw [show n + (m + 1) = (n + m) + 1 from by omega,
        DTM.run_add (simObs q b M) (n + m) 1 c,
        run_of_halted (simObs q b M) ((simObs q b M).run (n + m) c) hhalt 1]
      exact ih

/-- **伴随引理**：若第 i 步的模拟状态已是接受态，则观察机在第 i+1 步进入接受哨兵
    （前提：前 i 步都可观察）。
    Companion: if the drive reaches `m = M.accept` at step i, `simObs` accepts at step i+1. -/
theorem simObs_run_accept (q b : Nat) (M : NTM q) :
    ∀ (i : Nat) (c : Config (stateCountD q b)),
      (∀ j : Nat, j < i →
        observeState q b M ((simDrive q b M.step M.start).run j c).state) →
      (hlt : ((simDrive q b M.step M.start).run i c).state.val < stateCount q b) →
      unpackM (2 ^ b) 9 15 ((simDrive q b M.step M.start).run i c).state.val
        = M.accept.val →
      ((simObs q b M).run (i + 1) (Config.mk (embO q b c.state) c.tape)).state
        = obsAcc q b := by
  intro i c hobs hlt hacc
  have hrun := simObs_run_delegate q b M i c hobs
  have hltD : (embO q b ((simDrive q b M.step M.start).run i c).state).val
      < stateCountD q b := by
    rw [embO_val]
    exact ((simDrive q b M.step M.start).run i c).state.isLt
  have hhalt : (simObs q b M).halted
      ((simObs q b M).run i (Config.mk (embO q b c.state) c.tape)) = false := by
    rw [hrun]
    exact simObs_halted_inner q b M (embO q b ((simDrive q b M.step M.start).run i c).state)
      hltD ((simDrive q b M.step M.start).run i c).tape
  rw [run_succ_last (simObs q b M) i (Config.mk (embO q b c.state) c.tape) hhalt, hrun]
  exact simObs_stepConfig_accept_state q b M
    ((simDrive q b M.step M.start).run i c).state
    ((simDrive q b M.step M.start).run i c).tape
    ((simDrive q b M.step M.start).run i c).state.isLt hlt hacc

/-- 驱动层状态的嵌入不会等于接受哨兵（状态号不同）。 -/
theorem embO_ne_obsAcc (q b : Nat) (st : Fin (stateCountD q b)) :
    embO q b st ≠ obsAcc q b := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [embO, obsAcc, Fin.val_mk] at hv
  omega

/-- 驱动层状态的嵌入不会等于失败哨兵。 -/
theorem embO_ne_obsFail (q b : Nat) (st : Fin (stateCountD q b)) :
    embO q b st ≠ obsFail q b := by
  intro hh
  have hv := congrArg Fin.val hh
  simp only [embO, obsFail, Fin.val_mk] at hv
  omega

/-- **通路成功的终态形态**：观察机跑满 `r.steps` 后处于重编码的 `passEnd`，
    因此既不是接受哨兵也不是失败哨兵。 -/
theorem simObs_pass_state (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b M.step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b M.step M.start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b M.step M.start).run i
            (passStart x m c hm hc Z L)).state.val ≠ M.accept.val) :
    ((simObs q b M).run r.steps
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state
      = embO q b (passEnd r).state := by
  have h := simObs_pass q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
  exact congrArg Config.state h

/-- 通行成功的分支不会命中接受哨兵。 -/
theorem simObs_pass_not_acc (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b M.step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b M.step M.start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b M.step M.start).run i
            (passStart x m c hm hc Z L)).state.val ≠ M.accept.val) :
    ((simObs q b M).run r.steps
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  rw [simObs_pass_state q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc]
  exact embO_ne_obsAcc q b (passEnd r).state

/-- **反推**：若观察机在 `N` 步内始终没到接受哨兵，则驱动层在前 `N-1` 步内
    途经的模拟状态都不是接受态。 -/
theorem simObs_no_accept_of_no_acc (q b : Nat) (M : NTM q)
    (N : Nat) (c : Config (stateCountD q b))
    (hN : ∀ j : Nat, j ≤ N →
      ((simObs q b M).run j (Config.mk (embO q b c.state) c.tape)).state ≠ obsAcc q b)
    (i : Nat) (hi : i + 1 ≤ N)
    (hobs : ∀ j : Nat, j < i →
      observeState q b M ((simDrive q b M.step M.start).run j c).state)
    (hlt : ((simDrive q b M.step M.start).run i c).state.val < stateCount q b) :
    unpackM (2 ^ b) 9 15 ((simDrive q b M.step M.start).run i c).state.val
      ≠ M.accept.val := by
  intro hacc
  exact hN (i + 1) hi
    (simObs_run_accept q b M i c hobs hlt hacc)

/-- **分支预算内不误接受**：通路成功且内部无接受态时，观察机在 `r.steps` 以内的
    任何时刻都不会处于接受哨兵。
    Within the pass budget, the observer never reaches the accept sentinel. -/
theorem simObs_no_acc_upto (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b M.step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b M.step M.start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b M.step M.start).run i
            (passStart x m c hm hc Z L)).state.val ≠ M.accept.val)
    (j : Nat) (hj : j ≤ r.steps) :
    ((simObs q b M).run j
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  by_cases hlt : j < r.steps
  · -- 前缀：观察投影给出「驱动状态的嵌入」
    have hobs := simObs_pass_obs q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
    have hrun := simObs_run_delegate q b M j (passStart x m c hm hc Z L)
      (fun i hi => hobs i (by omega))
    rw [hrun]
    exact embO_ne_obsAcc q b _
  · -- 终点：恰为 `passEnd` 的重编码
    have hje : j = r.steps := by omega
    subst hje
    exact simObs_pass_not_acc q b M L Z c hc x m hm hx hpre hpost hb r hpass hnoacc





/-! ## 由观察层命中反推驱动层接受态 -/

/-- 进入失败哨兵后不再离开。 -/
theorem simObs_run_fail_persists (q b : Nat) (M : NTM q) :
    ∀ (n m : Nat) (c : Config (stateCountO q b)),
      ((simObs q b M).run n c).state = obsFail q b →
      ((simObs q b M).run (n + m) c).state = obsFail q b := by
  intro n m c h
  induction m with
  | zero => simpa using h
  | succ m ih =>
      have hhalt : (simObs q b M).halted ((simObs q b M).run (n + m) c) = true :=
        halted_of_accept_or_reject (simObs q b M) _ (Or.inr ih)
      rw [show n + (m + 1) = (n + m) + 1 from by omega,
        DTM.run_add (simObs q b M) (n + m) 1 c,
        run_of_halted (simObs q b M) ((simObs q b M).run (n + m) c) hhalt 1]
      exact ih

/-- 嵌入状态一步落到接受哨兵，只能经由「模拟层且已是接受态」这一分支。
    An embO-state can hit the accept sentinel only via the accepting branch. -/
theorem simObs_step_embO_acc (q b : Nat) (M : NTM q)
    (st : Fin (stateCountD q b)) (a : Sym)
    (h : ((simObs q b M).step (embO q b st) a).1 = obsAcc q b) :
    st.val < stateCount q b ∧ unpackM (2 ^ b) 9 15 st.val = M.accept.val := by
  by_cases hin : st.val < stateCount q b
  · by_cases hacc : unpackM (2 ^ b) 9 15 st.val = M.accept.val
    · exact ⟨hin, hacc⟩
    · by_cases h14 : unpackPh (2 ^ b) 9 15 st.val = 14
      · exfalso
        have hs := simObs_step_fail q b M (embO q b st) st.isLt hin hacc h14 a
        rw [hs] at h
        have h1 := congrArg Fin.val h
        simp only [obsFail, obsAcc, Fin.val_mk] at h1
        omega
      · exfalso
        have hs := simObs_step_delegate q b M (embO q b st) st.isLt hin hacc h14 a
        rw [hs] at h
        have h1 := congrArg Fin.val h
        have h2 := ((simDrive q b M.step M.start).step
          ⟨(embO q b st).val, st.isLt⟩ a).1.isLt
        simp only [obsAcc, Fin.val_mk] at h1
        omega
  · exfalso
    have hs := simObs_step_nav q b M (embO q b st) st.isLt hin a
    rw [hs] at h
    have h1 := congrArg Fin.val h
    have h2 := ((simDrive q b M.step M.start).step
      ⟨(embO q b st).val, st.isLt⟩ a).1.isLt
    simp only [obsAcc, Fin.val_mk] at h1
    omega

/-- **逆投影**：若驱动层前 `n` 步都可观察，观察机第 `n` 步命中接受哨兵，且更早各步
    都未命中，则驱动层在上一步正处于模拟层接受态。
    Converse projection: an observer accept hit (first hit) means the drive layer was
    at an accepting simulation-layer state one step earlier. -/
theorem simObs_acc_hit (q b : Nat) (M : NTM q)
    (n : Nat) (c : Config (stateCountD q b))
    (hobs : ∀ j : Nat, j < n →
      observeState q b M ((simDrive q b M.step M.start).run j c).state)
    (hacc : ((simObs q b M).run n
      (Config.mk (embO q b c.state) c.tape)).state = obsAcc q b)
    (hno : ∀ k : Nat, k < n →
      ((simObs q b M).run k (Config.mk (embO q b c.state) c.tape)).state
        ≠ obsAcc q b) :
    ∃ i, i < n ∧
      ∃ (hlt : ((simDrive q b M.step M.start).run i c).state.val
          < stateCount q b),
        unpackM (2 ^ b) 9 15 ((simDrive q b M.step M.start).run i c).state.val
          = M.accept.val := by
  let X : Config (stateCountO q b) := Config.mk (embO q b c.state) c.tape
  cases n with
  | zero =>
      -- 起点是嵌入状态，不可能是接受哨兵
      exfalso
      have h0 : ((simObs q b M).run 0 X).state = (embO q b c.state) := rfl
      rw [h0] at hacc
      exact embO_ne_obsAcc q b c.state hacc
  | succ k =>
      have hacc1 : ((simObs q b M).run (k + 1) X).state = obsAcc q b := hacc
      -- 第 k 步不是接受哨兵，也不是失败哨兵（否则会一直失败）
      have hkacc : ((simObs q b M).run k X).state ≠ obsAcc q b :=
        hno k (by omega)
      have hkfail : ((simObs q b M).run k X).state ≠ obsFail q b := by
        intro hf
        have hp := simObs_run_fail_persists q b M k 1 X hf
        simp only [Nat.add_one] at hp
        have hv : (obsFail q b).val = (obsAcc q b).val := by rw [← hp, hacc]
        simp only [obsFail, obsAcc, Fin.val_mk] at hv
        omega
      -- 非哨兵状态必是嵌入状态
      have hltD : ((simObs q b M).run k X).state.val < stateCountD q b := by
        have hv : ((simObs q b M).run k X).state.val < stateCountD q b + 2 := by
          have h := ((simObs q b M).run k X).state.isLt
          unfold stateCountO at h
          exact h
        have h1 : ((simObs q b M).run k X).state.val ≠ stateCountD q b := by
          intro hh
          apply hkacc
          apply Fin.ext
          rw [hh]
          rfl
        have h2 : ((simObs q b M).run k X).state.val ≠ stateCountD q b + 1 := by
          intro hh
          apply hkfail
          apply Fin.ext
          rw [hh]
          rfl
        omega
      -- 观察投影：第 k 步的观察状态是驱动状态的重编码
      have hrun := simObs_run_delegate q b M k c (fun j hj => hobs j (by omega))
      have hWhalt : (simObs q b M).halted ((simObs q b M).run k X) = false := by
        rw [hrun]
        exact simObs_halted_inner q b M
          (embO q b ((simDrive q b M.step M.start).run k c).state)
          (by rw [embO_val]; exact
            ((simDrive q b M.step M.start).run k c).state.isLt) _
      have hstep : (simObs q b M).stepConfig ((simObs q b M).run k X)
          = (simObs q b M).run (k + 1) X :=
        (run_succ_last (simObs q b M) k X hWhalt).symm
      -- 第 k 步的驱动状态：模拟层且接受
      have hacc' : ((simObs q b M).step
          (embO q b ((simDrive q b M.step M.start).run k c).state)
          ((simDrive q b M.step M.start).run k c).tape.read).1 = obsAcc q b := by
        have h1 := hacc1
        rw [← hstep, hrun, stepConfig_state] at h1
        exact h1
      obtain ⟨hlti, hacci⟩ := simObs_step_embO_acc q b M _ _ hacc'
      exact ⟨k, by omega, hlti, hacci⟩

end DTM

end Pnp
