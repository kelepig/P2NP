/-
  文件：Pnp/Machine/SimDrive.lean
  主题：带「导航层」的模拟驱动状态空间（B5 阶段 3c-ii 的装配骨架）。

  背景：`simStep` 用压缩状态 `codeState q b m c z ph`（相位 0..14）模拟被模拟机
  的一步，但 NP 的接受语义要求**每一步可以用不同的选择编号**。因此驱动需要在
  两轮模拟之间把读写头移到模拟区左侧的「选择数字区」，读出下一轮的选择编号。

  本文件把状态空间扩成两层（总数 `2 * stateCount + 1`）：

    - 上层（`st.val < stateCount`）＝模拟层，转移与 `simStep` 完全一致，
      只有相位 13（一轮结束、头停在标记位）改走「进入导航」；
    - 下层（`stateCount ≤ st.val < 2 * stateCount`）＝导航层，相位字段改作
      导航子相位（回扫、读数字块、计数、返回、逐格找标记、到位）；
    - 最后一个状态 `2 * stateCount` 未使用，用作 accept/reject 哨兵：
      任何转移都不会产生它，因此本机在运行中**永不假停机**。

  本文件给出（第一阶段）：
    - `stateCountD` / `embS` / `embN`：状态总数与两层嵌入；
    - `simDrive`：驱动状态空间上的转移函数；
    - `simDrive_halted_embS` / `simDrive_halted_embN`：嵌入状态未停机；
    - `simDrive_step_embS`：模拟层与 `simStep` 的逐步一致（相位 ≠ 13）；
    - `simStep_ph_step` / `simStep_run_ph`：相位推进界（`≤ 相位+1` 或死相位 14）；
    - `simDrive_run_embS`：`n` 步模拟层的 `run` 与 `simStep` 一致
      （前提是 `n` 步内不经过相位 13）。

  导航层的跑通与整轮定理留作第二阶段（`docs/07-B5-模拟器设计.md`）。
-/

import Pnp.Machine.SimRegion

namespace Pnp

namespace DTM

/-- 驱动状态总数：两层各 `stateCount q b` 个，末尾一个哨兵状态。 -/
def stateCountD (q b : Nat) : Nat := 2 * stateCount q b + 1

/-- 模拟层状态号落在驱动状态空间内。 -/
theorem stateCount_lt_stateCountD (q b n : Nat) (hn : n < stateCount q b) :
    n < stateCountD q b := by
  unfold stateCountD
  omega

/-- 导航层状态号落在驱动状态空间内。 -/
theorem stateCount_layer1_lt (q b n : Nat) (hn : n < stateCount q b) :
    stateCount q b + n < stateCountD q b := by
  unfold stateCountD
  omega

/-- 模拟层嵌入：原样保存压缩状态号。 -/
def embS {q b : Nat} (st : Fin (stateCount q b)) : Fin (stateCountD q b) :=
  ⟨st.val, stateCount_lt_stateCountD q b st.val st.isLt⟩

/-- 导航层嵌入：状态号加 `stateCount q b`。 -/
def embN {q b : Nat} (st : Fin (stateCount q b)) : Fin (stateCountD q b) :=
  ⟨stateCount q b + st.val, stateCount_layer1_lt q b st.val st.isLt⟩

/-- 驱动转移函数：模拟层照抄 `simStep`（相位 13 例外，进入导航层），
    导航层按子相位工作。 -/
def simDrive (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    DTM (stateCountD q b) where
  step := fun st a =>
    if h : st.val < stateCount q b then
      -- 模拟层
      if unpackPh (2 ^ b) 9 15 st.val = 13 then
        -- 一轮结束：进入导航层。选择计数器清零，保存被模拟状态 m。
        let m := unpackM (2 ^ b) 9 15 st.val
        let hm : m < q := unpackM_lt q b st.val h
        if a = none then
          (embN (codeState q b m 0 0 1 hm (Nat.two_pow_pos b) (by decide) (by decide)),
            a, Dir.left)
        else
          (embN (codeState q b m 0 0 0 hm (Nat.two_pow_pos b) (by decide) (by decide)),
            a, Dir.left)
      else
        let r := (simStep q b tab s0).step ⟨st.val, h⟩ a
        (embS r.1, r.2.1, r.2.2)
    else
      -- 导航层：子相位在相位字段里
      let inner : Fin (stateCount q b) :=
        if hsent : st.val = 2 * stateCount q b then
          ⟨0, stateCount_pos q b (by have := s0.isLt; omega)⟩
        else
          ⟨st.val - stateCount q b, by
            have := st.isLt
            unfold stateCountD at this
            omega⟩
      let m := unpackM (2 ^ b) 9 15 inner.val
      let c := unpackC (2 ^ b) 9 15 inner.val
      let ph := unpackPh (2 ^ b) 9 15 inner.val
      let hm : m < q := unpackM_lt q b inner.val inner.isLt
      let hc : c < 2 ^ b := unpackC_lt (2 ^ b) 9 15 inner.val (Nat.two_pow_pos b)
      if ph = 0 then
        -- 回扫：向左直到空白（区域左端的分隔符）
        if a = none then
          (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)), a, Dir.left)
        else
          (embN (codeState q b m c 0 0 hm hc (by decide) (by decide)), a, Dir.left)
      else if ph = 1 then
        -- 跳过分隔 0：已消费的块与块终结符都是 `some false`，向左直到遇见 1
        match a with
        | some true =>
            if hb : 1 < 2 ^ b then
              (embN (codeState q b m 1 0 2 hm hb (by decide) (by decide)), a, Dir.left)
            else (embN inner, a, Dir.stay)
        | none =>
            -- 数字区已耗尽（跳过零后越过左边界）：转入模拟层失败相位 14，
            -- 使分支通路在预算用尽处终止，而不是在空白纸带上无限左移。
            -- Digit area exhausted: switch to simulation-layer failure phase 14,
            -- so a branch pass terminates at its budget instead of marching left forever.
            (embS (codeState q b m c 0 14 hm hc (by decide) (by decide)), a, Dir.stay)
        | some false =>
            (embN (codeState q b m c 0 1 hm hc (by decide) (by decide)), a, Dir.left)
      else if ph = 2 then
        -- 计数 1 段：读到 1 就加一并向左；读到别的就是下个块的 0（或空白）
        match a with
        | some true =>
            if hc1 : c + 1 < 2 ^ b then
              (embN (codeState q b m (c + 1) 0 2 hm hc1 (by decide) (by decide)),
                a, Dir.left)
            else (embN inner, a, Dir.stay)
        | _ =>
            (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)), a, Dir.right)
      else if ph = 3 then
        -- 返回并擦除：向右把已读块的 1 改写成 0（消费），遇到分隔空白进入找标记
        if a = none then
          (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)), a, Dir.right)
        else
          (embN (codeState q b m c 0 3 hm hc (by decide) (by decide)), some false,
            Dir.right)
      else if ph = 4 then
        -- 逐格找标记：第 1 个编码符号，右移
        (embN (codeState q b m c 0 5 hm hc (by decide) (by decide)), a, Dir.right)
      else if ph = 5 then
        -- 逐格找标记：第 2 个编码符号，右移
        (embN (codeState q b m c 0 6 hm hc (by decide) (by decide)), a, Dir.right)
      else if ph = 6 then
        -- 逐格找标记：第 3 个符号即标记位
        if a = some true then
          (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)), a, Dir.stay)
        else
          (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)), a, Dir.right)
      else if ph = 7 then
        -- 已到标记位：块编码为 `1^(d+1) 0`，故选择编号 = 计数 − 1；
        -- 带着它回到模拟层相位 0
        (embS (codeState q b m (c - 1) 0 0 hm (by have := hc; omega) (by decide)
          (by decide)), a, Dir.stay)
      else (st, a, Dir.stay)
  start := embS (simStep q b tab s0).start
  accept := ⟨2 * stateCount q b, by unfold stateCountD; omega⟩
  reject := ⟨2 * stateCount q b, by unfold stateCountD; omega⟩

/-- 模拟层嵌入状态未停机（哨兵状态不可达）。 -/
theorem simDrive_halted_embS (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (t : Tape) :
    (simDrive q b tab s0).halted (Config.mk (embS st) t) = false := by
  have hlt : (embS st).val < 2 * stateCount q b := by
    have := st.isLt
    simp only [embS, Fin.val_mk]
    omega
  have hne : (embS st) ≠ (⟨2 * stateCount q b, by unfold stateCountD; omega⟩ :
      Fin (stateCountD q b)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [embS, Fin.val_mk, Fin.val_mk] at hv
    omega
  unfold DTM.halted simDrive
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 导航层嵌入状态未停机（哨兵状态不可达）。 -/
theorem simDrive_halted_embN (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (t : Tape) :
    (simDrive q b tab s0).halted (Config.mk (embN st) t) = false := by
  have hlt : (embN st).val < 2 * stateCount q b := by
    have := st.isLt
    simp only [embN, Fin.val_mk]
    omega
  have hne : (embN st) ≠ (⟨2 * stateCount q b, by unfold stateCountD; omega⟩ :
      Fin (stateCountD q b)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [embN, Fin.val_mk, Fin.val_mk] at hv
    omega
  unfold DTM.halted simDrive
  rw [beq_eq_false_iff_ne.mpr hne]
  rfl

/-- 模拟层（相位 ≠ 13）的单步与 `simStep` 完全一致。 -/
theorem simDrive_step_embS (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b))
    (hph : unpackPh (2 ^ b) 9 15 st.val ≠ 13) (a : Sym) :
    (simDrive q b tab s0).step (embS st) a =
      (embS ((simStep q b tab s0).step st a).1, ((simStep q b tab s0).step st a).2) := by
  simp only [simDrive, embS, Fin.val_mk, dite_eq_left st.isLt, hph, if_false]



/-- 相位推进界：相位 `p ≤ 12` 的状态走一步后，相位变 `p + 1`，或阶段 4 查表失败进入死相位 14。 -/
theorem simStep_ph_step (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val ≤ 12) :
    unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).step st a).1.val
        = unpackPh (2 ^ b) 9 15 st.val + 1
      ∨ unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).step st a).1.val = 14 := by
  have hcases : unpackPh (2 ^ b) 9 15 st.val = 0
      ∨ unpackPh (2 ^ b) 9 15 st.val = 1
      ∨ unpackPh (2 ^ b) 9 15 st.val = 2
      ∨ unpackPh (2 ^ b) 9 15 st.val = 3
      ∨ unpackPh (2 ^ b) 9 15 st.val = 4
      ∨ unpackPh (2 ^ b) 9 15 st.val = 5
      ∨ unpackPh (2 ^ b) 9 15 st.val = 6
      ∨ unpackPh (2 ^ b) 9 15 st.val = 7
      ∨ unpackPh (2 ^ b) 9 15 st.val = 8
      ∨ unpackPh (2 ^ b) 9 15 st.val = 9
      ∨ unpackPh (2 ^ b) 9 15 st.val = 10
      ∨ unpackPh (2 ^ b) 9 15 st.val = 11
      ∨ unpackPh (2 ^ b) 9 15 st.val = 12 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 0 := h0
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 1 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase0 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 1 := h1
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (symIdx a) 2 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (by have := symIdx_lt a; omega) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase1 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 2 := h2
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (symIdxOfCode a (symOfIdx (unpackZ (2 ^ b) 9 15 st.val))) 3 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (by have := symIdxOfCode_lt a (symOfIdx (unpackZ (2 ^ b) 9 15 st.val)); omega) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase2 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 3 := h3
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 4 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase3 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 4 := h4
    cases hl : lookupRes q b tab st with
    | none =>
        right
        have hstate : ((simStep q b tab s0).step st a).1 =
            codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 14 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
          have := congrArg Config.state
            (simStep_step_phase4_none q b tab s0 st a [] [] hp' hl)
          simpa [DTM.stepConfig, Tape.read, List.headD] using this
        rw [hstate]
        simp only [codeState_val]
        rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    | some v =>
        obtain ⟨m', s', d⟩ := v
        left
        have hstate : ((simStep q b tab s0).step st a).1 =
            codeState q b (m'.val) (unpackC (2 ^ b) 9 15 st.val) (symIdx s' * 3 + dirVal d) 5 m'.isLt (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
              (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) := by
          have := congrArg Config.state
            (simStep_step_phase4_some q b tab s0 st a [] [] hp' m' s' d hl)
          simpa [DTM.stepConfig, Tape.read, List.headD] using this
        rw [hstate]
        simp only [codeState_val]
        rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
        omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 5 := h5
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 6 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase5 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 6 := h6
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 7 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase6 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 7 := h7
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 8 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase7 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 8 := h8
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 9 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase8 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 9 := h9
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 10 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase9 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 10 := h10
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 11 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase10 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 11 := h11
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 12 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase11 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega
  · have hp' : unpackPh (2 ^ b) 9 15 st.val = 12 := h12
    have hstate : ((simStep q b tab s0).step st a).1 =
        codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 13 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide) := by
      have := congrArg Config.state
        (simStep_step_phase12 q b tab s0 st a [] [] hp')
      simpa [DTM.stepConfig, Tape.read, List.headD] using this
    left
    rw [hstate]
    simp only [codeState_val]
    rw [unpackPh_pack_of_lt (2 ^ b) 9 15 _ _ _ _ (by decide)]
    omega


/-- 死相位 14 走一步后仍是 14（查表失败的分支不再移动）。 -/
theorem simStep_ph14_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).step st a).1.val = 14 := by
  have h := congrArg Config.state (simStep_step_phase14 q b tab s0 st a [] [] hP)
  simp only [DTM.stepConfig, Tape.read, List.headD] at h
  rw [h, hP]

/-- 相位推进界（`stepConfig` 形式）。 -/
theorem simStep_ph_stepConfig (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (stC : Config (stateCount q b))
    (hP : unpackPh (2 ^ b) 9 15 stC.state.val ≤ 12) :
    unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).stepConfig stC).state.val
        = unpackPh (2 ^ b) 9 15 stC.state.val + 1
      ∨ unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).stepConfig stC).state.val = 14 := by
  have h := simStep_ph_step q b tab s0 stC.state stC.tape.read hP
  simpa [DTM.stepConfig] using h

/-- 死相位 14 保持（`stepConfig` 形式）。 -/
theorem simStep_ph14_stepConfig (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (stC : Config (stateCount q b))
    (hP : unpackPh (2 ^ b) 9 15 stC.state.val = 14) :
    unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).stepConfig stC).state.val = 14 := by
  have h := simStep_ph14_stay q b tab s0 stC.state stC.tape.read hP
  simpa [DTM.stepConfig] using h

/-- 模拟层一步（`stepConfig` 形式）：与 `simStep` 完全一致。 -/
theorem simDrive_stepConfig_embS (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (c : Config (stateCount q b))
    (hph : unpackPh (2 ^ b) 9 15 c.state.val ≠ 13) :
    (simDrive q b tab s0).stepConfig (Config.mk (embS c.state) c.tape)
      = Config.mk (embS ((simStep q b tab s0).stepConfig c).state)
          ((simStep q b tab s0).stepConfig c).tape := by
  simp only [DTM.stepConfig, simDrive_step_embS q b tab s0 c.state hph c.tape.read]

/-- 相位 ≠ 13 的模拟层状态未停机（accept/reject 都编码为相位 13）。 -/
theorem simStep_halted_ph_ne (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b))
    (hph : unpackPh (2 ^ b) 9 15 st.val ≠ 13) (t : Tape) :
    (simStep q b tab s0).halted (Config.mk st t) = false := by
  have hacc : (simStep q b tab s0).accept
      = codeState q b s0.val 0 0 13 s0.isLt (Nat.two_pow_pos b) (by decide) (by decide) := rfl
  have hne : st ≠ (simStep q b tab s0).accept := by
    intro heq
    have hv : unpackPh (2 ^ b) 9 15 st.val
        = unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).accept).val := by rw [heq]
    rw [hacc, codeState_unpackPh] at hv
    exact hph hv
  have hrej : st ≠ (simStep q b tab s0).reject := by
    rw [show (simStep q b tab s0).reject = (simStep q b tab s0).accept from rfl]
    exact hne
  simp only [DTM.halted]
  rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hrej]
  rfl

/-- 相位不变量：从相位 0 出发、跑 `k ≤ 13` 步后，相位 ≤ k 或已是死相位 14。 -/
theorem simStep_run_ph (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (c : Config (stateCount q b))
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0) :
    ∀ k, k ≤ 13 →
      unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≤ k
        ∨ unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val = 14 := by
  intro k
  induction k with
  | zero =>
      intro _
      left
      simp [DTM.run, h0]
  | succ k ih =>
      intro hk
      have hk' : k ≤ 13 := by omega
      have hik := ih hk'
      have hhalt : (simStep q b tab s0).halted
          ((simStep q b tab s0).run k c) = false := by
        apply simStep_halted_ph_ne
        omega
      have hone : (simStep q b tab s0).run 1 ((simStep q b tab s0).run k c)
          = (simStep q b tab s0).stepConfig ((simStep q b tab s0).run k c) := by
        have h := DTM.run_succ_of_not_halted (simStep q b tab s0) 0
          ((simStep q b tab s0).run k c) hhalt
        simpa [DTM.run] using h
      rw [DTM.run_add (simStep q b tab s0) k 1 c, hone]
      rcases hik with hle | h14
      · have hstep := simStep_ph_stepConfig q b tab s0
          ((simStep q b tab s0).run k c) (by omega)
        rcases hstep with hs | hs
        · left; omega
        · right; exact hs
      · have hstep := simStep_ph14_stepConfig q b tab s0
          ((simStep q b tab s0).run k c) h14
        right
        exact hstep

/-- `k < 13` 步内相位永远不是 13（13 只在第 13 步出现）。 -/
theorem simStep_run_ph_ne13 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (c : Config (stateCount q b))
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0) :
    ∀ k, k < 13 →
      unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≠ 13 := by
  intro k hk
  have hinv := simStep_run_ph q b tab s0 c h0 k (by omega)
  omega

/-- 模拟层 `n` 步运行与 `simStep` 完全一致（`n` 步内不经过相位 13）。 -/
theorem simDrive_run_embS (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) :
    ∀ (n : Nat) (c : Config (stateCount q b)),
      (∀ k, k < n →
        unpackPh (2 ^ b) 9 15 ((simStep q b tab s0).run k c).state.val ≠ 13) →
      (simDrive q b tab s0).run n (Config.mk (embS c.state) c.tape)
        = Config.mk (embS ((simStep q b tab s0).run n c).state)
            ((simStep q b tab s0).run n c).tape
  | 0, c, _ => by simp [DTM.run]
  | n + 1, c, hph => by
      have hnhS : (simStep q b tab s0).halted c = false :=
        simStep_halted_ph_ne q b tab s0 c.state (hph 0 (Nat.zero_lt_succ n)) c.tape
      have hstep := simDrive_stepConfig_embS q b tab s0 c
        (hph 0 (Nat.zero_lt_succ n))
      rw [DTM.run_succ_of_not_halted (simDrive q b tab s0) n
        (Config.mk (embS c.state) c.tape)
        (simDrive_halted_embS q b tab s0 c.state c.tape)]
      rw [DTM.run_succ_of_not_halted (simStep q b tab s0) n c hnhS]
      refine Eq.trans (congrArg ((simDrive q b tab s0).run n) hstep) ?_
      exact simDrive_run_embS q b tab s0 n ((simStep q b tab s0).stepConfig c) (fun k hk => by
          rw [← DTM.run_succ_of_not_halted (simStep q b tab s0) k c hnhS]
          exact hph (k + 1) (by omega))


/-- 相位 0 状态跑满 13 步不遇相位 13，因此驱动与 `simStep` 的整轮搬运成立。 -/
theorem simDrive_run13_embS (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (c : Config (stateCount q b))
    (h0 : unpackPh (2 ^ b) 9 15 c.state.val = 0) :
    (simDrive q b tab s0).run 13 (Config.mk (embS c.state) c.tape)
      = Config.mk (embS ((simStep q b tab s0).run 13 c).state)
          ((simStep q b tab s0).run 13 c).tape :=
  simDrive_run_embS q b tab s0 13 c (simStep_run_ph_ne13 q b tab s0 c h0)

/-- 驱动整轮（原地）：区域表述。 -/
theorem simDrive_round_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (L : List Sym) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simDrive q b tab s0).run 13
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (embS (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q).enc L) := by
  obtain ⟨st, pre, cur, post⟩ := x
  simp only at h hx
  subst hx
  have htr := simDrive_run13_embS q b tab s0
    (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
      ((Reg.mk ⟨m, hm⟩ pre cur post).enc L))
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
  simp only [Reg.enc] at htr
  simp only [Reg.enc]
  rw [htr]
  have hmain := simStep_round_stay q b tab s0 m c hm hc cur pre post L m' s' h
  rw [tape_marker_left cur pre L] at hmain
  rw [hmain]
  rw [tape_marker_left s' pre L]

/-- 驱动整轮（右移）：区域表述。 -/
theorem simDrive_round_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (L : List Sym) (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post') (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simDrive q b tab s0).run 13
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (embS (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)))
      (({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } :
        Reg q).enc L) := by
  obtain ⟨st, pre, cur, post⟩ := x
  simp only at h hpost hx
  subst hpost
  subst hx
  have htr := simDrive_run13_embS q b tab s0
    (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
      ((Reg.mk ⟨m, hm⟩ pre cur (p :: post')).enc L))
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
  simp only [Reg.enc] at htr
  simp only [Reg.enc]
  rw [htr]
  have hmain := simStep_round_right q b tab s0 m c hm hc cur pre p post' L hp m' s' h
  rw [tape_marker_left cur pre L] at hmain
  rw [hmain]
  rfl

/-- 驱动整轮（左移）：区域表述。 -/
theorem simDrive_round_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (L : List Sym) (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre : x.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simDrive q b tab s0).run 13
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (embS (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)))
      (({ state := m', pre := pre', cur := cq.1, post := (s', false) :: x.post } :
        Reg q).enc L) := by
  obtain ⟨st, pre, cur, post⟩ := x
  simp only at h hpre hx
  subst hpre
  subst hx
  have htr := simDrive_run13_embS q b tab s0
    (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
      ((Reg.mk ⟨m, hm⟩ (pre' ++ [cq]) cur post).enc L))
    (codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide))
  simp only [Reg.enc] at htr
  simp only [Reg.enc]
  rw [htr]
  have hmain := simStep_round_left q b tab s0 m c hm hc cur pre' cq post L hq m' s' h
  simp only [codeCells, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    cellCode, symCode_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc, Bool.false_eq_true, ite_false, hq]
  simp only [codeCells, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    cellCode, symCode_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc, Bool.false_eq_true, ite_false, hq] at hmain
  rw [hmain]

end DTM

end Pnp
