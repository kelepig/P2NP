/-
  文件：Pnp/Machine/SimAll.lean
  主题：外层多轮模拟机 `simAll`：把 `simStep` 的一轮 13 步重复 `T` 轮。

  `simStep` 是「阶段机」：一轮结束停在阶段 13（成功）或 14（查表失败），
  此时它的单步转移是「不动」，不会自动进入下一轮。`simAll` 负责这件事：

      状态号 = k * stateCount q b + inner       （k = 轮计数器，inner = simStep 状态）

  - 轮内（`unpackPh inner ≠ 13, 14`）：完全照搬 `simStep` 的转移；
  - 一轮成功（阶段 13）：k+1 < T 时清零 `z`、进入下一轮阶段 0；
    否则转入接受态 `T * stateCount q b`；
  - 查表失败（阶段 14）：转入拒绝态 `T * stateCount q b + 1`。

  这样「连续 T 轮模拟」就变成一条 *固定* 的确定性图灵机，且停机由外层控制。
-/

import Pnp.Machine.SimStep

namespace Pnp

namespace DTM

/-- 状态总数是正数（`q > 0`）。 -/
theorem stateCount_pos (q b : Nat) (hq : 0 < q) : 0 < stateCount q b := by
  unfold stateCount
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hq (Nat.two_pow_pos b)) (by decide)) (by decide)

/-- 压缩后的「计数 + 局部状态」仍在外层状态空间内。 -/
theorem pack_in_bound {T SC k r : Nat} (hk : k < T) (hr : r < SC) :
    k * SC + r < T * SC := by
  calc k * SC + r < k * SC + SC := Nat.add_lt_add_left hr _
    _ = (k + 1) * SC := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ T * SC := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hk)

/-- 外层多轮模拟机：`T` 轮、每轮 13 步的 `simStep`。 -/
def simAll (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    DTM (T * stateCount q b + 2) where
  step := fun s a =>
    if h : s.val < T * stateCount q b then
      let k := s.val / stateCount q b
      let inner := s.val % stateCount q b
      let ph := unpackPh (2 ^ b) 9 15 inner
      if ph = 13 then
        if hk : k + 1 < T then
          (⟨(k + 1) * stateCount q b +
              packIdx (2 ^ b) 9 15 (unpackM (2 ^ b) 9 15 inner)
                (unpackC (2 ^ b) 9 15 inner) 0 0,
              by
                have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
                have hSC := stateCount_pos q b hq
                have hm : unpackM (2 ^ b) 9 15 inner < q :=
                  unpackM_lt q b inner (Nat.mod_lt _ hSC)
                have hc : unpackC (2 ^ b) 9 15 inner < 2 ^ b :=
                  unpackC_lt (2 ^ b) 9 15 inner (Nat.two_pow_pos b)
                have hp : packIdx (2 ^ b) 9 15 (unpackM (2 ^ b) 9 15 inner)
                    (unpackC (2 ^ b) 9 15 inner) 0 0 < stateCount q b := by
                  unfold stateCount
                  exact packIdx_lt (Nat.two_pow_pos b) (by decide) (by decide)
                    hm hc (by decide) (by decide)
                have hb := pack_in_bound hk hp
                omega⟩, a, Dir.stay)
        else
          (⟨T * stateCount q b, by
            have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
            have := stateCount_pos q b hq; omega⟩, a, Dir.stay)
      else if ph = 14 then
        (⟨T * stateCount q b + 1, by
          have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
          have := stateCount_pos q b hq; omega⟩, a, Dir.stay)
      else
        let r := (simStep q b tab s0).step ⟨inner, by
          have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
          exact Nat.mod_lt _ (stateCount_pos q b hq)⟩ a
        (⟨k * stateCount q b + r.1.val, by
          have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
          have hSC := stateCount_pos q b hq
          have hk' : k < T := by
            have h' : s.val < stateCount q b * T := by
              calc s.val < T * stateCount q b := h
                _ = stateCount q b * T := Nat.mul_comm _ _
            exact Nat.div_lt_of_lt_mul h'
          have hb := pack_in_bound hk' r.1.isLt
          omega⟩, r.2.1, r.2.2)
    else (s, a, Dir.stay)
  start := ⟨packIdx (2 ^ b) 9 15 s0.val 0 0 0, by
    unfold stateCount
    have hp : packIdx (2 ^ b) 9 15 s0.val 0 0 0 < q * 2 ^ b * 9 * 15 :=
      packIdx_lt (D := 2 ^ b) (Z := 9) (P := 15) (q := q) (m := s0.val)
        (c := 0) (z := 0) (ph := 0)
        (Nat.two_pow_pos b) (by decide) (by decide) s0.isLt
        (Nat.two_pow_pos b) (by decide) (by decide)
    have hle : q * 2 ^ b * 9 * 15 ≤ T * (q * 2 ^ b * 9 * 15) :=
      Nat.le_mul_of_pos_left _ hT
    omega⟩
  accept := ⟨T * stateCount q b, by
    have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
    have := stateCount_pos q b hq; omega⟩
  reject := ⟨T * stateCount q b + 1, by
    have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
    have := stateCount_pos q b hq; omega⟩

/-- 轮内的一步：`simAll` 完全照搬 `simStep` 的转移（阶段既非 13 也非 14）。 -/
theorem simAll_step_inner (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k inner : Nat) (hk : k < T) (hin : inner < stateCount q b)
    (h13 : unpackPh (2 ^ b) 9 15 inner ≠ 13)
    (h14 : unpackPh (2 ^ b) 9 15 inner ≠ 14) (a : Sym) :
    (simAll q b T hT tab s0).step
      (⟨k * stateCount q b + inner, by have := pack_in_bound hk hin; omega⟩ :
        Fin (T * stateCount q b + 2)) a
      = (⟨k * stateCount q b + ((simStep q b tab s0).step ⟨inner, hin⟩ a).1.val,
            by have := pack_in_bound hk ((simStep q b tab s0).step ⟨inner, hin⟩ a).1.isLt
               omega⟩,
          ((simStep q b tab s0).step ⟨inner, hin⟩ a).2.1,
          ((simStep q b tab s0).step ⟨inner, hin⟩ a).2.2) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hdiv : (k * stateCount q b + inner) / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + inner) % stateCount q b = inner := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  unfold simAll
  simp only [Fin.val_mk, hdiv, hmod]
  rw [dif_pos (by have := pack_in_bound hk hin; omega)]
  rw [if_neg h13, if_neg h14]

/-- 一轮成功后重启下一步：清零 `z`、轮计数 +1、回到阶段 0。 -/
theorem simAll_step_restart (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k inner : Nat) (hk : k < T) (hk1 : k + 1 < T) (hin : inner < stateCount q b)
    (h13 : unpackPh (2 ^ b) 9 15 inner = 13) (a : Sym) :
    (simAll q b T hT tab s0).step
      (⟨k * stateCount q b + inner, by have := pack_in_bound hk hin; omega⟩ :
        Fin (T * stateCount q b + 2)) a
      = (⟨(k + 1) * stateCount q b +
            packIdx (2 ^ b) 9 15 (unpackM (2 ^ b) 9 15 inner)
              (unpackC (2 ^ b) 9 15 inner) 0 0,
          by
            have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
            have hSC := stateCount_pos q b hq
            have hm : unpackM (2 ^ b) 9 15 inner < q := unpackM_lt q b inner hin
            have hc : unpackC (2 ^ b) 9 15 inner < 2 ^ b :=
              unpackC_lt (2 ^ b) 9 15 inner (Nat.two_pow_pos b)
            have hp : packIdx (2 ^ b) 9 15 (unpackM (2 ^ b) 9 15 inner)
                (unpackC (2 ^ b) 9 15 inner) 0 0 < stateCount q b := by
              unfold stateCount
              exact packIdx_lt (Nat.two_pow_pos b) (by decide) (by decide)
                hm hc (by decide) (by decide)
            have hb := pack_in_bound hk1 hp
            omega⟩, a, Dir.stay) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hdiv : (k * stateCount q b + inner) / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + inner) % stateCount q b = inner := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  unfold simAll
  simp only [Fin.val_mk, hdiv, hmod]
  rw [dif_pos (by have := pack_in_bound hk hin; omega)]
  rw [if_pos h13]
  rw [dif_pos hk1]

/-- 最后一轮结束后转入接受态。 -/
theorem simAll_step_accept (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k inner : Nat) (hk : k < T) (hkn : ¬(k + 1 < T)) (hin : inner < stateCount q b)
    (h13 : unpackPh (2 ^ b) 9 15 inner = 13) (a : Sym) :
    (simAll q b T hT tab s0).step
      (⟨k * stateCount q b + inner, by have := pack_in_bound hk hin; omega⟩ :
        Fin (T * stateCount q b + 2)) a
      = (⟨T * stateCount q b, by
          have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
          have := stateCount_pos q b hq; omega⟩, a, Dir.stay) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hdiv : (k * stateCount q b + inner) / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + inner) % stateCount q b = inner := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  unfold simAll
  simp only [Fin.val_mk, hdiv, hmod]
  rw [dif_pos (by have := pack_in_bound hk hin; omega)]
  rw [if_pos h13]
  rw [dif_neg hkn]

/-- 查表失败（阶段 14）转入拒绝态。 -/
theorem simAll_step_reject (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k inner : Nat) (hk : k < T) (hin : inner < stateCount q b)
    (h14 : unpackPh (2 ^ b) 9 15 inner = 14) (a : Sym) :
    (simAll q b T hT tab s0).step
      (⟨k * stateCount q b + inner, by have := pack_in_bound hk hin; omega⟩ :
        Fin (T * stateCount q b + 2)) a
      = (⟨T * stateCount q b + 1, by
          have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
          have := stateCount_pos q b hq; omega⟩, a, Dir.stay) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hdiv : (k * stateCount q b + inner) / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + inner) % stateCount q b = inner := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  unfold simAll
  simp only [Fin.val_mk, hdiv, hmod]
  rw [dif_pos (by have := pack_in_bound hk hin; omega)]
  rw [if_neg (by intro hh; rw [hh] at h14; omega)]
  rw [if_pos h14]

/-- 第 `k` 轮的状态嵌入。 -/
def embK (q b T : Nat) (k : Nat) (hk : k < T) : Fin (stateCount q b) → Fin (T * stateCount q b + 2) :=
  fun s => ⟨k * stateCount q b + s.val, by have := pack_in_bound hk s.isLt; omega⟩

/-- 轮内状态不会停机（accept/reject 都在计数边界之外）。 -/
theorem simAll_halted_inner (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k inner : Nat) (hk : k < T) (hin : inner < stateCount q b) (t : Tape) :
    (simAll q b T hT tab s0).halted
      (Config.mk (⟨k * stateCount q b + inner,
        by have := pack_in_bound hk hin; omega⟩ : Fin (T * stateCount q b + 2)) t) = false := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hlt := pack_in_bound hk hin
  have hne1 : (⟨k * stateCount q b + inner,
        by have := pack_in_bound hk hin; omega⟩ : Fin (T * stateCount q b + 2))
      ≠ (simAll q b T hT tab s0).accept := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [simAll, Fin.val_mk] at hv
    omega
  have hne2 : (⟨k * stateCount q b + inner,
        by have := pack_in_bound hk hin; omega⟩ : Fin (T * stateCount q b + 2))
      ≠ (simAll q b T hT tab s0).reject := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [simAll, Fin.val_mk] at hv
    omega
  unfold DTM.halted
  have h1 : ((⟨k * stateCount q b + inner,
        by have := pack_in_bound hk hin; omega⟩ : Fin (T * stateCount q b + 2))
      == (simAll q b T hT tab s0).accept) = false := beq_eq_false_iff_ne.mpr hne1
  have h2 : ((⟨k * stateCount q b + inner,
        by have := pack_in_bound hk hin; omega⟩ : Fin (T * stateCount q b + 2))
      == (simAll q b T hT tab s0).reject) = false := beq_eq_false_iff_ne.mpr hne2
  rw [h1, h2]
  rfl

/-- `simAll` 的轮内一步 = `simStep` 一步经 `embK` 搬运（阶段非 13/14）。 -/
theorem simAll_step_emb (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) (a : Sym) (h13 : ph ≠ 13) (h14 : ph ≠ 14) :
    (simAll q b T hT tab s0).step
      (embK q b T k hk (codeState q b m c z ph hm hc hz hph)) a
      = (embK q b T k hk ((simStep q b tab s0).step
            (codeState q b m c z ph hm hc hz hph) a).1,
         ((simStep q b tab s0).step (codeState q b m c z ph hm hc hz hph) a).2.1,
         ((simStep q b tab s0).step (codeState q b m c z ph hm hc hz hph) a).2.2) := by
  have h13' : unpackPh (2 ^ b) 9 15 (codeState q b m c z ph hm hc hz hph).val ≠ 13 := by
    rw [codeState_val, unpackPh_pack_of_lt (2 ^ b) 9 15 m c z ph hph]
    exact h13
  have h14' : unpackPh (2 ^ b) 9 15 (codeState q b m c z ph hm hc hz hph).val ≠ 14 := by
    rw [codeState_val, unpackPh_pack_of_lt (2 ^ b) 9 15 m c z ph hph]
    exact h14
  unfold embK
  rw [simAll_step_inner q b T hT tab s0 k _ hk _ h13' h14' a]

/-- 试验：`simAll` 轮内一步（阶段 0 → 1）。 -/
theorem simAll_stepC0 (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simAll q b T hT tab s0).step
      (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (some true)
      = (embK q b T k hk (codeState q b m c 0 1 hm hc (by decide) (by decide)),
         some true, Dir.left) := by
  rw [simAll_step_emb q b T hT tab s0 k hk m c 0 0 hm hc (by decide) (by decide) (some true)
    (by decide) (by decide)]
  have hP := codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)
  have hM := codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide)
  have hC := codeState_unpackC q b m c 0 0 hm hc (by decide) (by decide)
  have hZ := codeState_unpackZ q b m c 0 0 hm hc (by decide) (by decide)
  simp only [simStep, hP, hM, hC, hZ, Tape.read, Tape.write, Tape.move, Tape.moveLeft,
    Tape.moveRight, Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- `simAll_step_emb` 的展开形式（不出现 `embK`，便于在 `run` 链中 `rw`）。 -/
theorem simAll_step_emb' (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) (a : Sym) (h13 : ph ≠ 13) (h14 : ph ≠ 14) :
    (simAll q b T hT tab s0).step
      (⟨k * stateCount q b + (codeState q b m c z ph hm hc hz hph).val,
        by have := pack_in_bound hk (codeState q b m c z ph hm hc hz hph).isLt; omega⟩ :
        Fin (T * stateCount q b + 2)) a
      = (⟨k * stateCount q b + ((simStep q b tab s0).step
            (codeState q b m c z ph hm hc hz hph) a).1.val,
          by have := pack_in_bound hk ((simStep q b tab s0).step
            (codeState q b m c z ph hm hc hz hph) a).1.isLt; omega⟩,
         ((simStep q b tab s0).step (codeState q b m c z ph hm hc hz hph) a).2.1,
         ((simStep q b tab s0).step (codeState q b m c z ph hm hc hz hph) a).2.2) := by
  simpa only [embK] using simAll_step_emb q b T hT tab s0 k hk m c z ph hm hc hz hph a h13 h14


/-- 试验：`simAll` 的阶段 0 一步（stepConfig 级）。 -/
theorem simAll_stepC0step (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (L' R' : List Sym) :
    (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (Tape.mk L' (some true :: R'))) =
    Config.mk (embK q b T k hk (codeState q b m c 0 1 hm hc (by decide) (by decide)))
      ((Tape.mk L' (some true :: R')).move Dir.left) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hin : (codeState q b m c 0 0 hm hc (by decide) (by decide)).val < stateCount q b :=
    (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt
  have hdiv : (k * stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val)
      / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val)
      % stateCount q b = (codeState q b m c 0 0 hm hc (by decide) (by decide)).val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  have hP := codeState_unpackPh q b m c 0 0 hm hc (by decide) (by decide)
  have hM := codeState_unpackM q b m c 0 0 hm hc (by decide) (by decide)
  have hC := codeState_unpackC q b m c 0 0 hm hc (by decide) (by decide)
  have hZ := codeState_unpackZ q b m c 0 0 hm hc (by decide) (by decide)
  have hlt : k * stateCount q b + (codeState q b m c 0 0 hm hc (by decide) (by decide)).val
      < T * stateCount q b := pack_in_bound hk hin
  simp only [DTM.stepConfig, simAll, embK, hdiv, hmod, hP, hM, hC, hZ, simStep_stepC0,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Prod.fst, Prod.snd,
    List.headD, List.tail]
  repeat' first
    | rw [dif_pos hlt]
    | rw [if_neg (by decide)]
    | rw [if_pos (by decide)]

/-- `simAll` 在轮内的一步（stepConfig 级）：给定 `simStep` 的一步结果，
    `simAll` 的一步就是它经 `embK` 的搬运。 -/
theorem simAll_stepConfig_eq (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) (L R : List Sym) (a : Sym)
    (h13 : ph ≠ 13) (h14 : ph ≠ 14) (s2 : Fin (stateCount q b)) (bw : Sym) (dd : Dir)
    (hs : (simStep q b tab s0).step (codeState q b m c z ph hm hc hz hph) a
      = (s2, bw, dd)) :
    (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m c z ph hm hc hz hph))
        (Tape.mk L (a :: R))) =
    Config.mk (embK q b T k hk s2) (((Tape.mk L (a :: R)).write bw).move dd) := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hin : (codeState q b m c z ph hm hc hz hph).val < stateCount q b :=
    (codeState q b m c z ph hm hc hz hph).isLt
  have hdiv : (k * stateCount q b + (codeState q b m c z ph hm hc hz hph).val)
      / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + (codeState q b m c z ph hm hc hz hph).val)
      % stateCount q b = (codeState q b m c z ph hm hc hz hph).val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  have hP := codeState_unpackPh q b m c z ph hm hc hz hph
  have hM := codeState_unpackM q b m c z ph hm hc hz hph
  have hC := codeState_unpackC q b m c z ph hm hc hz hph
  have hZ := codeState_unpackZ q b m c z ph hm hc hz hph
  have hlt : k * stateCount q b + (codeState q b m c z ph hm hc hz hph).val
      < T * stateCount q b := pack_in_bound hk hin
  simp only [DTM.stepConfig, simAll, embK, hdiv, hmod, hP, hM, hC, hZ, hs,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Prod.fst, Prod.snd,
    List.headD, List.tail]
  repeat' first
    | rw [dif_pos hlt]
    | rw [if_neg h13]
    | rw [if_neg h14]
    | rw [if_neg (by decide)]
    | rw [if_pos (by decide)]

/-- `simAll_stepConfig_eq` 的展开形式（不出现 `embK`）。 -/
theorem simAll_stepConfig_eq' (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) (L R : List Sym) (a : Sym)
    (h13 : ph ≠ 13) (h14 : ph ≠ 14) (s2 : Fin (stateCount q b)) (bw : Sym) (dd : Dir)
    (hs : (simStep q b tab s0).step (codeState q b m c z ph hm hc hz hph) a
      = (s2, bw, dd)) :
    (simAll q b T hT tab s0).stepConfig
      (Config.mk (⟨k * stateCount q b + (codeState q b m c z ph hm hc hz hph).val,
          by have := pack_in_bound hk (codeState q b m c z ph hm hc hz hph).isLt; omega⟩ :
          Fin (T * stateCount q b + 2))
        (Tape.mk L (a :: R))) =
    Config.mk (⟨k * stateCount q b + s2.val,
        by have := pack_in_bound hk s2.isLt; omega⟩ : Fin (T * stateCount q b + 2))
      (((Tape.mk L (a :: R)).write bw).move dd) := by
  simpa only [embK] using simAll_stepConfig_eq q b T hT tab s0 k hk m c z ph hm hc
    hz hph L R a h13 h14 s2 bw dd hs


/-- 13 步链：给定 13 个 `stepConfig` 等式与未停机证据。 -/
theorem run_thirteen_of_steps (M : DTM q) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : Config q}
    (h0 : M.halted c0 = false)
    (h1 : M.halted c1 = false)
    (h2 : M.halted c2 = false)
    (h3 : M.halted c3 = false)
    (h4 : M.halted c4 = false)
    (h5 : M.halted c5 = false)
    (h6 : M.halted c6 = false)
    (h7 : M.halted c7 = false)
    (h8 : M.halted c8 = false)
    (h9 : M.halted c9 = false)
    (h10 : M.halted c10 = false)
    (h11 : M.halted c11 = false)
    (h12 : M.halted c12 = false)
    (e0 : M.stepConfig c0 = c1)
    (e1 : M.stepConfig c1 = c2)
    (e2 : M.stepConfig c2 = c3)
    (e3 : M.stepConfig c3 = c4)
    (e4 : M.stepConfig c4 = c5)
    (e5 : M.stepConfig c5 = c6)
    (e6 : M.stepConfig c6 = c7)
    (e7 : M.stepConfig c7 = c8)
    (e8 : M.stepConfig c8 = c9)
    (e9 : M.stepConfig c9 = c10)
    (e10 : M.stepConfig c10 = c11)
    (e11 : M.stepConfig c11 = c12)
    (e12 : M.stepConfig c12 = c13) :
    M.run 13 c0 = c13 := by
  rw [show (13 : Nat) = 12 + 1 by rfl,
    DTM.run_succ_of_not_halted M 12 c0 h0, e0]
  rw [show (12 : Nat) = 11 + 1 by rfl,
    DTM.run_succ_of_not_halted M 11 c1 h1, e1]
  rw [show (11 : Nat) = 10 + 1 by rfl,
    DTM.run_succ_of_not_halted M 10 c2 h2, e2]
  rw [show (10 : Nat) = 9 + 1 by rfl,
    DTM.run_succ_of_not_halted M 9 c3 h3, e3]
  rw [show (9 : Nat) = 8 + 1 by rfl,
    DTM.run_succ_of_not_halted M 8 c4 h4, e4]
  rw [show (8 : Nat) = 7 + 1 by rfl,
    DTM.run_succ_of_not_halted M 7 c5 h5, e5]
  rw [show (7 : Nat) = 6 + 1 by rfl,
    DTM.run_succ_of_not_halted M 6 c6 h6, e6]
  rw [show (6 : Nat) = 5 + 1 by rfl,
    DTM.run_succ_of_not_halted M 5 c7 h7, e7]
  rw [show (5 : Nat) = 4 + 1 by rfl,
    DTM.run_succ_of_not_halted M 4 c8 h8, e8]
  rw [show (4 : Nat) = 3 + 1 by rfl,
    DTM.run_succ_of_not_halted M 3 c9 h9, e9]
  rw [show (3 : Nat) = 2 + 1 by rfl,
    DTM.run_succ_of_not_halted M 2 c10 h10, e10]
  rw [show (2 : Nat) = 1 + 1 by rfl,
    DTM.run_succ_of_not_halted M 1 c11 h11, e11]
  rw [DTM.run_succ_of_not_halted M 0 c12 h12, e12]
  simp [DTM.run]

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- 一整轮模拟（原地）在 `simAll` 上的 13 步搬运版。 -/
theorem simAll_round_stay (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.stay)) :
    (simAll q b T hT tab s0).run 13
      (Config.mk (embK q b T k hk
        (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))) =
    Config.mk (embK q b T k hk
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)) := by
  refine run_thirteen_of_steps (simAll q b T hT tab s0)
    (c0 := Config.mk (embK q b T k hk
      (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))
    (c1 := Config.mk (embK q b T k hk
      (codeState q b m c 0 1 hm hc (by decide) (by decide)))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post)))
    (c2 := Config.mk (embK q b T k hk
      (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)))
      (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s :: (some true) :: codeCells post)))
    (c3 := Config.mk (embK q b T k hk
      (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post)))
    (c4 := Config.mk (embK q b T k hk
      (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))
    (c5 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))
    (c6 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post)))
    (c7 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: (some true) :: codeCells post)))
    (c8 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: (some true) :: codeCells post)))
    (c9 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))
    (c10 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some false) :: codeCells post)))
    (c11 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some false) :: codeCells post)))
    (c12 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some false) :: codeCells post)))
    (c13 := Config.mk (embK q b T k hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))
    (h0 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c 0 0 hm hc (by decide) (by decide)).val hk (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h1 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c 0 1 hm hc (by decide) (by decide)).val hk (codeState q b m c 0 1 hm hc (by decide) (by decide)).isLt (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h2 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).val hk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).isLt (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h3 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).val hk (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h4 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)).val hk (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h5 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h6 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h7 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h8 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h9 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h10 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some false) :: codeCells post))
      simpa only [embK] using hh)
    (h11 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some false) :: codeCells post))
      simpa only [embK] using hh)
    (h12 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some false) :: codeCells post))
      simpa only [embK] using hh)
    (e0 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m c 0 0 hm hc (by decide) (by decide)
      (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some true)) (by decide) (by decide)
      (codeState q b m c 0 1 hm hc (by decide) (by decide)) ((some true)) Dir.left
      (simStep_stepC0 q b tab s0 m c hm hc))
    (e1 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m c 0 1 hm hc (by decide) (by decide)
      (codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post) (codeSnd s) (by decide) (by decide)
      (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)) (codeSnd s) Dir.left
      (simStep_stepC1 q b tab s0 m c hm hc s s' Dir.stay))
    (e2 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)
      ((List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells post) (codeFst s) (by decide) (by decide)
      (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)) (codeFst s) Dir.right
      (simStep_stepC2 q b tab s0 m c hm hc s s' Dir.stay))
    (e3 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)
      (codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post) (codeSnd s) (by decide) (by decide)
      (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)) (codeSnd s) Dir.right
      (simStep_stepC3 q b tab s0 m c hm hc s s' Dir.stay))
    (e4 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)
      (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some true)) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) ((some true)) Dir.stay
      (simStep_stepC4 q b tab s0 m c hm hc s s' Dir.stay m' h))
    (e5 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some true)) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) ((some true)) Dir.left
      (simStep_stepC5 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay))
    (e6 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post) (codeSnd s) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) (codeSnd s') Dir.left
      (simStep_stepC6 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay))
    (e7 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      ((List.reverse (codeCells pre) ++ L)) (codeSnd s' :: (some true) :: codeCells post) (codeFst s) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) (codeFst s') Dir.right
      (simStep_stepC7 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay))
    (e8 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post) (codeSnd s') (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) (codeSnd s') Dir.right
      (simStep_stepC8 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay))
    (e9 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some true)) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) ((some false)) Dir.stay
      (by rw [simStep_stepC9 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay];
          rw [dirOf_mod_three s' Dir.stay]))
    (e10 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some false)) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) ((some false)) Dir.stay
      (by rw [simStep_stepC10 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay];
          rw [dirOf_mod_three s' Dir.stay]))
    (e11 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some false)) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) ((some false)) Dir.stay
      (by rw [simStep_stepC11 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay];
          rw [dirOf_mod_three s' Dir.stay]))
    (e12 := simAll_stepConfig_eq' q b T hT tab s0 k hk
      m'.val c (symIdx s' * 3 + dirVal Dir.stay) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)
      (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeCells post) ((some false)) (by decide) (by decide)
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)) ((some true)) Dir.stay
      (simStep_stepC12 q b tab s0 m'.val c m'.isLt hc s s' Dir.stay))

/-- 阶段 13（一轮成功）且 `k + 1 < T`：重启——清零 `z`，进入第 `k+1` 轮。 -/
theorem simAll_step13_restart (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k m c z : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (t : Tape) (hne : t.right ≠ []) :
    (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m c z 13 hm hc hz (by decide))) t) =
    Config.mk (embK q b T (k + 1) hk1
      (codeState q b m c 0 0 hm hc (by decide) (by decide))) t := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hin : (codeState q b m c z 13 hm hc hz (by decide)).val < stateCount q b :=
    (codeState q b m c z 13 hm hc hz (by decide)).isLt
  have hdiv : (k * stateCount q b + (codeState q b m c z 13 hm hc hz (by decide)).val)
      / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + (codeState q b m c z 13 hm hc hz (by decide)).val)
      % stateCount q b = (codeState q b m c z 13 hm hc hz (by decide)).val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  have hP := codeState_unpackPh q b m c z 13 hm hc hz (by decide)
  have hM := codeState_unpackM q b m c z 13 hm hc hz (by decide)
  have hC := codeState_unpackC q b m c z 13 hm hc hz (by decide)
  have hlt : k * stateCount q b + (codeState q b m c z 13 hm hc hz (by decide)).val
      < T * stateCount q b := pack_in_bound hk hin
  simp only [DTM.stepConfig, simAll, embK, hdiv, hmod, hP, hM, hC,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Prod.fst, Prod.snd,
    List.headD, List.tail]
  repeat' first
    | rw [dif_pos hlt]
    | rw [dif_pos hk1]
    | rw [if_pos (by decide)]
    | rw [if_neg (by decide)]
  simp only [Prod.fst, Prod.snd, Tape.move, Tape.write, Tape.read, List.headD,
    List.tail, codeState_val]
  cases t with
  | mk l r =>
    cases r with
    | nil => exact absurd rfl hne
    | cons x xs => rfl

/-- 阶段 13 且 `k + 1 = T`：接受（停在 `T*stateCount` 状态）。 -/
theorem simAll_step13_accept (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k m c z : Nat) (hk : k < T) (hkT : k + 1 = T)
    (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (t : Tape) (hne : t.right ≠ []) :
    (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m c z 13 hm hc hz (by decide))) t) =
    Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2)) t := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hin : (codeState q b m c z 13 hm hc hz (by decide)).val < stateCount q b :=
    (codeState q b m c z 13 hm hc hz (by decide)).isLt
  have hdiv : (k * stateCount q b + (codeState q b m c z 13 hm hc hz (by decide)).val)
      / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + (codeState q b m c z 13 hm hc hz (by decide)).val)
      % stateCount q b = (codeState q b m c z 13 hm hc hz (by decide)).val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  have hP := codeState_unpackPh q b m c z 13 hm hc hz (by decide)
  have hM := codeState_unpackM q b m c z 13 hm hc hz (by decide)
  have hC := codeState_unpackC q b m c z 13 hm hc hz (by decide)
  have hlt : k * stateCount q b + (codeState q b m c z 13 hm hc hz (by decide)).val
      < T * stateCount q b := pack_in_bound hk hin
  have hk1n : ¬ k + 1 < T := by omega
  simp only [DTM.stepConfig, simAll, embK, hdiv, hmod, hP, hM, hC,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Prod.fst, Prod.snd,
    List.headD, List.tail]
  repeat' first
    | rw [dif_pos hlt]
    | rw [dif_neg hk1n]
    | rw [if_pos (by decide)]
    | rw [if_neg (by decide)]
  simp only [Prod.fst, Prod.snd, Tape.move, Tape.write, Tape.read, List.headD,
    List.tail, codeState_val]
  cases t with
  | mk l r =>
    cases r with
    | nil => exact absurd rfl hne
    | cons x xs => rfl

/-- 阶段 14（失败）：拒绝（停在 `T*stateCount + 1` 状态）。 -/
theorem simAll_step14_reject (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k m c z : Nat) (hk : k < T)
    (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (t : Tape) (hne : t.right ≠ []) :
    (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m c z 14 hm hc hz (by decide))) t) =
    Config.mk (⟨T * stateCount q b + 1, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2)) t := by
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hSC := stateCount_pos q b hq
  have hin : (codeState q b m c z 14 hm hc hz (by decide)).val < stateCount q b :=
    (codeState q b m c z 14 hm hc hz (by decide)).isLt
  have hdiv : (k * stateCount q b + (codeState q b m c z 14 hm hc hz (by decide)).val)
      / stateCount q b = k := by
    rw [Nat.mul_comm k (stateCount q b), Nat.mul_add_div hSC, Nat.div_eq_of_lt hin,
      Nat.add_zero]
  have hmod : (k * stateCount q b + (codeState q b m c z 14 hm hc hz (by decide)).val)
      % stateCount q b = (codeState q b m c z 14 hm hc hz (by decide)).val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]
  have hP := codeState_unpackPh q b m c z 14 hm hc hz (by decide)
  have hM := codeState_unpackM q b m c z 14 hm hc hz (by decide)
  have hC := codeState_unpackC q b m c z 14 hm hc hz (by decide)
  have hlt : k * stateCount q b + (codeState q b m c z 14 hm hc hz (by decide)).val
      < T * stateCount q b := pack_in_bound hk hin
  simp only [DTM.stepConfig, simAll, embK, hdiv, hmod, hP, hM, hC,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, Prod.fst, Prod.snd,
    List.headD, List.tail]
  repeat' first
    | rw [dif_pos hlt]
    | rw [if_pos (by decide)]
    | rw [if_neg (by decide)]
  simp only [Prod.fst, Prod.snd, Tape.move, Tape.write, Tape.read, List.headD,
    List.tail, codeState_val]
  cases t with
  | mk l r =>
    cases r with
    | nil => exact absurd rfl hne
    | cons x xs => rfl

/-- 一整轮模拟（原地）+ 重启：14 步从第 `k` 轮回到第 `k+1` 轮的轮首。 -/
theorem simAll_round_stay14 (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.stay)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        ((Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))) =
    Config.mk (embK q b T (k + 1) hk1
        (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide)))
      ((Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))) := by
  -- 13 步整轮搬运
  have h13 := simAll_round_stay q b T hT tab s0 k hk m c hm hc s pre post L m' s' h
  -- 阶段 13 在轮内，未停机
  have hhalt : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))
    simpa only [embK] using hh
  -- 一步重启
  have hstep : (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))) =
      Config.mk (embK q b T (k + 1) hk1
        (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)) :=
    simAll_step13_restart q b T hT tab s0 k m'.val c (symIdx s' * 3 + dirVal Dir.stay) hk hk1 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega)
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)) (by simp)
  -- 14 = 13 + 1：先整轮，再重启一步（用 calc，避免改写 1 时误伤 k+1）
  calc (simAll q b T hT tab s0).run 14
        (Config.mk (embK q b T k hk
          (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))
      = (simAll q b T hT tab s0).run 1
          ((simAll q b T hT tab s0).run 13
            (Config.mk (embK q b T k hk
              (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)))) := by
        rw [show (14 : Nat) = 13 + 1 by rfl, DTM.run_add]
    _ = (simAll q b T hT tab s0).run 1
          (Config.mk (embK q b T k hk
            (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post))) := by
        rw [h13]
    _ = Config.mk (embK q b T (k + 1) hk1
          (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post)) := by
        change (simAll q b T hT tab s0).run (0 + 1) _ = _
        rw [DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
        simp [DTM.run]


set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in
/-- `simAll` 整轮 13 步（模拟头向 right 移动）。 -/
theorem simAll_round_right (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym) (hp : p.2 = false) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.right)) :
    (simAll q b T hT tab s0).run 13
      (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')))) =
    Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post')) := by
  refine run_thirteen_of_steps (simAll q b T hT tab s0)
    (c0 := Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post'))))
    (c1 := Config.mk (embK q b T k hk (codeState q b m c 0 1 hm hc (by decide) (by decide))) (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post'))))
    (c2 := Config.mk (embK q b T k hk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide))) (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s :: (some true) :: codeCells (p :: post'))))
    (c3 := Config.mk (embK q b T k hk (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide))) (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post'))))
    (c4 := Config.mk (embK q b T k hk (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post'))))
    (c5 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post'))))
    (c6 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post'))))
    (c7 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: (some true) :: codeCells (p :: post'))))
    (c8 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: (some true) :: codeCells (p :: post'))))
    (c9 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post'))))
    (c10 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk ((some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: (if p.2 then some true else some false) :: codeCells post')))
    (c11 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: (if p.2 then some true else some false) :: codeCells post')))
    (c12 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((if p.2 then some true else some false) :: codeCells post')))
    (c13 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post')))
    (h0 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c 0 0 hm hc (by decide) (by decide)).val hk (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h1 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c 0 1 hm hc (by decide) (by decide)).val hk (codeState q b m c 0 1 hm hc (by decide) (by decide)).isLt (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h2 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).val hk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).isLt (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s :: (some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h3 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).val hk (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h4 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)).val hk (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h5 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h6 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h7 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: (some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h8 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: (some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h9 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')))
      simpa only [embK] using hh)
    (h10 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk ((some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: (if p.2 then some true else some false) :: codeCells post'))
      simpa only [embK] using hh)
    (h11 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: (if p.2 then some true else some false) :: codeCells post'))
      simpa only [embK] using hh)
    (h12 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((if p.2 then some true else some false) :: codeCells post'))
      simpa only [embK] using hh)
    (e0 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c 0 0 hm hc (by decide) (by decide) (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells (p :: post')) ((some true)) (by decide) (by decide) (codeState q b m c 0 1 hm hc (by decide) (by decide)) ((some true)) Dir.left (simStep_stepC0 q b tab s0 m c hm hc))
    (e1 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c 0 1 hm hc (by decide) (by decide) (codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')) (codeSnd s) (by decide) (by decide) (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)) (codeSnd s) Dir.left (simStep_stepC1 q b tab s0 m c hm hc s s' Dir.right))
    (e2 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide) ((List.reverse (codeCells pre) ++ L)) (codeSnd s :: (some true) :: codeCells (p :: post')) (codeFst s) (by decide) (by decide) (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)) (codeFst s) Dir.right (simStep_stepC2 q b tab s0 m c hm hc s s' Dir.right))
    (e3 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide) (codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')) (codeSnd s) (by decide) (by decide) (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)) (codeSnd s) Dir.right (simStep_stepC3 q b tab s0 m c hm hc s s' Dir.right))
    (e4 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide) (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells (p :: post')) ((some true)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) ((some true)) Dir.stay (simStep_stepC4 q b tab s0 m c hm hc s s' Dir.right m' h))
    (e5 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells (p :: post')) ((some true)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) ((some true)) Dir.left (simStep_stepC5 q b tab s0 m'.val c m'.isLt hc s s' Dir.right))
    (e6 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')) (codeSnd s) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) (codeSnd s') Dir.left (simStep_stepC6 q b tab s0 m'.val c m'.isLt hc s s' Dir.right))
    (e7 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) ((List.reverse (codeCells pre) ++ L)) (codeSnd s' :: (some true) :: codeCells (p :: post')) (codeFst s) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) (codeFst s') Dir.right (simStep_stepC7 q b tab s0 m'.val c m'.isLt hc s s' Dir.right))
    (e8 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')) (codeSnd s') (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) (codeSnd s') Dir.right (simStep_stepC8 q b tab s0 m'.val c m'.isLt hc s s' Dir.right))
    (e9 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeCells (p :: post')) ((some true)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) ((some false)) Dir.right (by rw [simStep_stepC9 q b tab s0 m'.val c m'.isLt hc s s' Dir.right]; rw [dirOf_mod_three s' Dir.right])
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hp,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)
    (e10 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) ((some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: (if p.2 then some true else some false) :: codeCells post') (codeFst p.1) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) ((codeFst p.1)) Dir.right (by rw [simStep_stepC10' q b tab s0 m'.val c m'.isLt hc s s' Dir.right (codeFst p.1)]; rw [dirOf_mod_three s' Dir.right])
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hp,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)
    (e11 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((if p.2 then some true else some false) :: codeCells post') (codeSnd p.1) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) ((codeSnd p.1)) Dir.right (by rw [simStep_stepC11' q b tab s0 m'.val c m'.isLt hc s s' Dir.right (codeSnd p.1)]; rw [dirOf_mod_three s' Dir.right])
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hp,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)
    (e12 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.right) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeCells post') ((if p.2 then some true else some false)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)) ((some true)) Dir.stay (simStep_stepC12' q b tab s0 m'.val c m'.isLt hc s s' Dir.right (if p.2 then some true else some false))
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hp,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)

set_option maxHeartbeats 1000000 in
/-- `simAll` 整轮 + 重启 14 步（模拟头向 right 移动）。 -/
theorem simAll_round_right14 (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym) (hp : p.2 = false) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.right)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post')))) =
    (Config.mk (embK q b T (k + 1) hk1 (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))) := by
  have h13 := simAll_round_right q b T hT tab s0 k hk m c hm hc s p post' pre L hp m' s' h
  have hhalt : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))
    simpa only [embK] using hh
  have hstep : (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))) =
      (Config.mk (embK q b T (k + 1) hk1 (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))) :=
    simAll_step13_restart q b T hT tab s0 k m'.val c (symIdx s' * 3 + dirVal Dir.right) hk hk1
      m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post')) (by simp [hp])
  calc (simAll q b T hT tab s0).run 14
        (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post'))))
      = (simAll q b T hT tab s0).run 1
          ((simAll q b T hT tab s0).run 13
            (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells (p :: post'))))) := by
        rw [show (14 : Nat) = 13 + 1 by rfl, DTM.run_add]
    _ = (simAll q b T hT tab s0).run 1
          (Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))) := by
        rw [h13]
    _ = (Config.mk (embK q b T (k + 1) hk1 (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post'))) := by
        change (simAll q b T hT tab s0).run (0 + 1) _ = _
        rw [DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
        simp [DTM.run]

set_option maxHeartbeats 1000000 in
/-- `simAll` 整轮 13 步（模拟头向 left 移动）。 -/
theorem simAll_round_left (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) (hq : cq.2 = false) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.left)) :
    (simAll q b T hT tab s0).run 13
      (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post))) =
    Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post)) := by
  refine run_thirteen_of_steps (simAll q b T hT tab s0)
    (c0 := Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post)))
    (c1 := Config.mk (embK q b T k hk (codeState q b m c 0 1 hm hc (by decide) (by decide))) (Tape.mk (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post)))
    (c2 := Config.mk (embK q b T k hk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide))) (Tape.mk ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s :: (some true) :: codeCells post)))
    (c3 := Config.mk (embK q b T k hk (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide))) (Tape.mk (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post)))
    (c4 := Config.mk (embK q b T k hk (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post)))
    (c5 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post)))
    (c6 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post)))
    (c7 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s' :: (some true) :: codeCells post)))
    (c8 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: (some true) :: codeCells post)))
    (c9 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd s' :: codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post)))
    (c10 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: (some false) :: codeCells post)))
    (c11 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: (some false) :: codeCells post)))
    (c12 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some false) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post)))
    (c13 := Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post)))
    (h0 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c 0 0 hm hc (by decide) (by decide)).val hk (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h1 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c 0 1 hm hc (by decide) (by decide)).val hk (codeState q b m c 0 1 hm hc (by decide) (by decide)).isLt (Tape.mk (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h2 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).val hk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).isLt (Tape.mk ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h3 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).val hk (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt (Tape.mk (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h4 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)).val hk (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h5 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h6 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h7 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s' :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h8 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: (some true) :: codeCells post))
      simpa only [embK] using hh)
    (h9 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post))
      simpa only [embK] using hh)
    (h10 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: (some false) :: codeCells post))
      simpa only [embK] using hh)
    (h11 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: (some false) :: codeCells post))
      simpa only [embK] using hh)
    (h12 := by
      have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some false) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))
      simpa only [embK] using hh)
    (e0 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c 0 0 hm hc (by decide) (by decide) (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeCells post) ((some true)) (by decide) (by decide) (codeState q b m c 0 1 hm hc (by decide) (by decide)) ((some true)) Dir.left (simStep_stepC0 q b tab s0 m c hm hc))
    (e1 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c 0 1 hm hc (by decide) (by decide) (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post) (codeSnd s) (by decide) (by decide) (codeState q b m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)) (codeSnd s) Dir.left (simStep_stepC1 q b tab s0 m c hm hc s s' Dir.left))
    (e2 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c (symIdx (codeSnd s)) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide) ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: (some true) :: codeCells post) (codeFst s) (by decide) (by decide) (codeState q b m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide)) (codeFst s) Dir.right (simStep_stepC2 q b tab s0 m c hm hc s s' Dir.left))
    (e3 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c (symIdx s) 3 hm hc (by have := symIdx_lt s; omega) (by decide) (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post) (codeSnd s) (by decide) (by decide) (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide)) (codeSnd s) Dir.right (simStep_stepC3 q b tab s0 m c hm hc s s' Dir.left))
    (e4 := simAll_stepConfig_eq' q b T hT tab s0 k hk m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide) (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeCells post) ((some true)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) ((some true)) Dir.stay (simStep_stepC4 q b tab s0 m c hm hc s s' Dir.left m' h))
    (e5 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 5 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeCells post) ((some true)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) ((some true)) Dir.left (simStep_stepC5 q b tab s0 m'.val c m'.isLt hc s s' Dir.left))
    (e6 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 6 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post) (codeSnd s) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) (codeSnd s') Dir.left (simStep_stepC6 q b tab s0 m'.val c m'.isLt hc s s' Dir.left))
    (e7 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 7 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: (some true) :: codeCells post) (codeFst s) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) (codeFst s') Dir.right (simStep_stepC7 q b tab s0 m'.val c m'.isLt hc s s' Dir.left))
    (e8 := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 8 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post) (codeSnd s') (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) (codeSnd s') Dir.right (simStep_stepC8 q b tab s0 m'.val c m'.isLt hc s s' Dir.left))
    (e9 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 9 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (codeSnd s' :: codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeCells post) ((some true)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) ((some false)) Dir.left (by rw [simStep_stepC9 q b tab s0 m'.val c m'.isLt hc s s' Dir.left]; rw [dirOf_mod_three s' Dir.left])
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hq,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)
    (e10 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 10 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (codeFst s' :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some false) :: codeCells post) (codeSnd s') (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) ((codeSnd s')) Dir.left (by rw [simStep_stepC10' q b tab s0 m'.val c m'.isLt hc s s' Dir.left (codeSnd s')]; rw [dirOf_mod_three s' Dir.left])
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hq,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)
    (e11 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 11 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) ((some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: (some false) :: codeCells post) (codeFst s') (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) ((codeFst s')) Dir.left (by rw [simStep_stepC11' q b tab s0 m'.val c m'.isLt hc s s' Dir.left (codeFst s')]; rw [dirOf_mod_three s' Dir.left])
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hq,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)
    (e12 := by
      have h := simAll_stepConfig_eq' q b T hT tab s0 k hk m'.val c (symIdx s' * 3 + dirVal Dir.left) 12 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: (some false) :: codeCells post) ((some false)) (by decide) (by decide) (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)) ((some true)) Dir.stay (simStep_stepC12' q b tab s0 m'.val c m'.isLt hc s s' Dir.left (some false))
      simpa only [embK, codeCells, List.flatMap_cons, cellCode, symCode_eq, hq,
        Bool.false_eq_true, ite_false, List.cons_append, List.singleton_append,
        List.append_assoc, List.nil_append, List.tail, Tape.write, Tape.moveLeft,Tape.moveRight, Tape.move] using h)

set_option maxHeartbeats 1000000 in
/-- `simAll` 整轮 + 重启 14 步（模拟头向 left 移动）。 -/
theorem simAll_round_left14 (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) (hq : cq.2 = false) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.left)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post))) =
    (Config.mk (embK q b T (k + 1) hk1 (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))) := by
  have h13 := simAll_round_left q b T hT tab s0 k hk m c hm hc s cq pre' post L hq m' s' h
  have hhalt : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))
    simpa only [embK] using hh
  have hstep : (simAll q b T hT tab s0).stepConfig
      (Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))) =
      (Config.mk (embK q b T (k + 1) hk1 (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))) :=
    simAll_step13_restart q b T hT tab s0 k m'.val c (symIdx s' * 3 + dirVal Dir.left) hk hk1
      m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post)) (by simp [hq])
  calc (simAll q b T hT tab s0).run 14
        (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post)))
      = (simAll q b T hT tab s0).run 1
          ((simAll q b T hT tab s0).run 13
            (Config.mk (embK q b T k hk (codeState q b m c 0 0 hm hc (by decide) (by decide))) (Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post)))) := by
        rw [show (14 : Nat) = 13 + 1 by rfl, DTM.run_add]
    _ = (simAll q b T hT tab s0).run 1
          (Config.mk (embK q b T k hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))) := by
        rw [h13]
    _ = (Config.mk (embK q b T (k + 1) hk1 (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide))) (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post))) := by
        change (simAll q b T hT tab s0).run (0 + 1) _ = _
        rw [DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
        simp [DTM.run]

end DTM

end Pnp
