/-
  文件：Pnp/Machine/SimStep.lean
  主题：单带模拟器的「一步」机 `simStep`：读符号 → 查转移表 → 改写并移标记。

  `simStep q b tab s0` 的状态被压成一个自然数（见 `PackIndex.lean`）：

      状态号 = packIdx (2^b) 9 15 m c z ph

  其中 m 是被模拟状态、c 是本次选择编号、z 是「符号编号 × 3 + 方向编号」
  （读符号期间临时存 b1 的编号），ph 是阶段：

      0  在标记位 → 左移
      1  在第二编码符号 → 记录其编号，左移
      2  在第一编码符号 → 解码出符号编号，右移
      3  在第二编码符号 → 右移（回到标记位）
      4  在标记位 → 查 `tab m s` 的第 c 项：
           越界 → 阶段 14（失败）；命中 → 记 (m', 符号编号, 方向) 并进入阶段 5
      5  在标记位 → 左移（以下即 `writeCell` 的 8 步脚本）
      6  在第二编码符号 → 写新编码第二符号，左移
      7  在第一编码符号 → 写新编码第一符号，右移
      8  在第二编码符号 → 右移
      9  在标记位 → 写 `some false`，按方向移动
      10 沿方向走一格
      11 沿方向再走一格
      12 在相邻格写 `some true`，进入阶段 13（成功）
      13 成功终止；14 失败终止

  本文件先证明**查表那一步**（阶段 4）的规格 `simStep_step_phase4`：
  它不再移动、不写纸带，只按 `pick (tab m s) c` 的结果把状态换成
  成功（携带 m'、新符号编号、方向）或失败。其余阶段留待下一步逐个证明。
-/

import Pnp.Machine.ReadCell
import Pnp.Machine.PackIndex

namespace Pnp

namespace DTM

/-- 移动方向编号：left ↦ 0，right ↦ 1，stay ↦ 2。 -/
def dirVal : Dir → Nat
  | Dir.left => 0
  | Dir.right => 1
  | Dir.stay => 2

/-- 编号还原移动方向。 -/
def dirOf : Nat → Dir
  | 0 => Dir.left
  | 1 => Dir.right
  | _ => Dir.stay

/-- 方向编号小于 3。 -/
theorem dirVal_lt (d : Dir) : dirVal d < 3 := by
  cases d <;> decide

/-- 编号与还原互逆。 -/
theorem dirOf_dirVal (d : Dir) : dirOf (dirVal d) = d := by
  cases d <;> rfl

/-- 模拟器的状态总数（q 个被模拟状态、2^b 个选择、9 种符号/方向、15 个阶段）。 -/
def stateCount (q b : Nat) : Nat := q * 2 ^ b * 9 * 15

/-- 状态总数的括号重排。 -/
theorem stateCount_eq (q b : Nat) : stateCount q b = q * (2 ^ b * 9 * 15) := by
  unfold stateCount
  ac_rfl

/-- 状态号里的 m 一定小于 q。 -/
theorem unpackM_lt (q b n : Nat) (hn : n < stateCount q b) :
    unpackM (2 ^ b) 9 15 n < q := by
  unfold unpackM
  have hn' : n < (2 ^ b * 9 * 15) * q := by
    rw [stateCount_eq] at hn
    rw [Nat.mul_comm] at hn
    exact hn
  exact Nat.div_lt_of_lt_mul hn' 

/-- 压缩后的状态号在合法范围内。 -/
theorem packIdx_lt {D Z P q m c z ph : Nat} (hD : 0 < D) (hZ : 0 < Z) (hP : 0 < P)
    (hm : m < q) (hc : c < D) (hz : z < Z) (hph : ph < P) :
    packIdx D Z P m c z ph < q * D * Z * P := by
  have hz1 : z + 1 ≤ Z := hz
  have hp1 : ph + 1 ≤ P := hph
  have hc1 : c + 1 ≤ D := hc
  have hDpos := hD
  have hm1 : m + 1 ≤ q := hm
  -- 主干上界：m*D + c + 1 ≤ q*D
  have hmain : m * D + c + 1 ≤ q * D := by
    have h1 : m * D + c + 1 ≤ m * D + D := by omega
    have h2 : m * D + D = (m + 1) * D := by rw [Nat.add_mul, Nat.one_mul]
    have h3 : (m + 1) * D ≤ q * D := Nat.mul_le_mul_right D hm1
    omega
  have hle : packIdx D Z P m c z ph + 1 ≤ q * D * Z * P := by
    calc packIdx D Z P m c z ph + 1
        = (((m * D + c) * Z + z) * P + ph) + 1 := rfl
      _ ≤ ((m * D + c) * Z + z) * P + P := by omega
      _ = (((m * D + c) * Z + z) + 1) * P := by
          conv =>
            rhs
            rw [Nat.add_mul, Nat.one_mul]
      _ ≤ ((m * D + c) * Z + Z) * P := by
          have h : (m * D + c) * Z + z + 1 ≤ (m * D + c) * Z + Z := by omega
          exact Nat.mul_le_mul_right P h
      _ = ((m * D + c + 1) * Z) * P := by
          congr 1
          conv =>
            rhs
            rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          rw [Nat.add_mul]
      _ ≤ ((q * D) * Z) * P := by
          exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right Z hmain)
      _ = q * D * Z * P := by rw [Nat.mul_assoc]
  omega

/-- 构造合法状态号。 -/
def codeState (q b : Nat) (m c z ph : Nat)
    (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (hph : ph < 15) :
    Fin (stateCount q b) :=
  ⟨packIdx (2 ^ b) 9 15 m c z ph,
    by
      unfold stateCount
      exact packIdx_lt (Nat.two_pow_pos b) (by decide) (by decide) hm hc hz hph⟩

/-- 解出被模拟状态（带范围证明）。 -/
def decM (q b : Nat) (st : Fin (stateCount q b)) : Fin q :=
  ⟨unpackM (2 ^ b) 9 15 st.val, unpackM_lt q b st.val st.isLt⟩

/-- 解出选择编号。 -/
def decC (b : Nat) (st : Fin (stateCount q b)) : Nat :=
  unpackC (2 ^ b) 9 15 st.val

/-- 解出符号/方向组合。 -/
def decZ (b : Nat) (st : Fin (stateCount q b)) : Nat :=
  unpackZ (2 ^ b) 9 15 st.val

/-- 查表：当前状态、当前符号的第 c 个候选动作。 -/
def lookupRes (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (st : Fin (stateCount q b)) : Option (Fin q × Sym × Dir) :=
  pick (tab (decM q b st) (symOfIdx (decZ b st))) (decC b st)

/-- 单步模拟机。 -/
def simStep (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    DTM (stateCount q b) where
  step := fun st a =>
    let m := unpackM (2 ^ b) 9 15 st.val
    let c := unpackC (2 ^ b) 9 15 st.val
    let z := unpackZ (2 ^ b) 9 15 st.val
    let ph := unpackPh (2 ^ b) 9 15 st.val
    let hm : m < q := unpackM_lt q b st.val st.isLt
    let hc : c < 2 ^ b := unpackC_lt _ _ _ _ (Nat.two_pow_pos b)
    let hz : z < 9 := unpackZ_lt (2 ^ b) 9 15 st.val (by decide)
    let hph : ph < 15 := unpackPh_lt (2 ^ b) 9 15 st.val (by decide)
    if ph = 0 then (codeState q b m c z 1 hm hc hz (by decide), a, Dir.left)
    else if ph = 1 then
      (codeState q b m c (symIdx a) 2 hm hc (by have := symIdx_lt a; omega) (by decide), a, Dir.left)
    else if ph = 2 then
      (codeState q b m c (symIdxOfCode a (symOfIdx z)) 3 hm hc
        (by have := symIdxOfCode_lt a (symOfIdx z); omega) (by decide), a, Dir.right)
    else if ph = 3 then (codeState q b m c z 4 hm hc hz (by decide), a, Dir.right)
    else if ph = 4 then
      match lookupRes q b tab st with
      | none => (codeState q b m c z 14 hm hc hz (by decide), a, Dir.stay)
      | some (m', s', d) =>
          (codeState q b m'.val c (symIdx s' * 3 + dirVal d) 5 m'.isLt hc
            (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), a, Dir.stay)
    else if ph = 5 then (codeState q b m c z 6 hm hc hz (by decide), a, Dir.left)
    else if ph = 6 then
      (codeState q b m c z 7 hm hc hz (by decide), codeSnd (symOfIdx (z / 3)), Dir.left)
    else if ph = 7 then
      (codeState q b m c z 8 hm hc hz (by decide), codeFst (symOfIdx (z / 3)), Dir.right)
    else if ph = 8 then (codeState q b m c z 9 hm hc hz (by decide), a, Dir.right)
    else if ph = 9 then (codeState q b m c z 10 hm hc hz (by decide), some false, dirOf (z % 3))
    else if ph = 10 then (codeState q b m c z 11 hm hc hz (by decide), a, dirOf (z % 3))
    else if ph = 11 then (codeState q b m c z 12 hm hc hz (by decide), a, dirOf (z % 3))
    else if ph = 12 then (codeState q b m c z 13 hm hc hz (by decide), some true, Dir.stay)
    else (st, a, Dir.stay)
  start := codeState q b s0.val 0 0 0 s0.isLt (Nat.two_pow_pos b) (by decide) (by decide)
  accept := codeState q b s0.val 0 0 13 s0.isLt (Nat.two_pow_pos b) (by decide) (by decide)
  reject := codeState q b s0.val 0 0 13 s0.isLt (Nat.two_pow_pos b) (by decide) (by decide)

/-- 查表这一步（阶段 4）的规格（失败分支）：不移动、不写纸带，进入阶段 14。 -/
theorem simStep_step_phase4_none (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 4) (h : lookupRes q b tab st = none) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
        (unpackZ (2 ^ b) 9 15 st.val) 14
        (unpackM_lt q b st.val st.isLt)
        (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
        (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, simStep, hP, h]
  rw [if_neg (show ¬(4 = 0) by decide), if_neg (show ¬(4 = 1) by decide),
    if_neg (show ¬(4 = 2) by decide), if_neg (show ¬(4 = 3) by decide),
    if_pos trivial]
  rfl

/-- 查表这一步（阶段 4）的规格（命中分支）：携带新状态、新符号编号与方向，
    进入阶段 5；不移动、不写纸带。 -/
theorem simStep_step_phase4_some (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 4) (m' : Fin q) (s' : Sym) (d : Dir)
    (h : lookupRes q b tab st = some (m', s', d)) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b m'.val (unpackC (2 ^ b) 9 15 st.val)
        (symIdx s' * 3 + dirVal d) 5 m'.isLt
        (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
        (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, simStep, hP, h]
  rw [if_neg (show ¬(4 = 0) by decide), if_neg (show ¬(4 = 1) by decide),
    if_neg (show ¬(4 = 2) by decide), if_neg (show ¬(4 = 3) by decide),
    if_pos trivial]
  rfl

/-- 试验：阶段 0 的一步规格。 -/
theorem simStep_step_phase0 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 0) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val)
        (unpackZ (2 ^ b) 9 15 st.val) 1
        (unpackM_lt q b st.val st.isLt)
        (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b))
        (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      ((Tape.mk L (a :: R)).move Dir.left) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 1 的一步规格：记下第二个编码符号的编号，左移。 -/
theorem simStep_step_phase1 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 1) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (symIdx a) 2 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (by have := symIdx_lt a; omega) (by decide))
      (((Tape.mk L (a :: R)).write a).move Dir.left) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 2 的一步规格：用两个编码符号解码出符号编号，右移。 -/
theorem simStep_step_phase2 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 2) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (symIdxOfCode a (symOfIdx (unpackZ (2 ^ b) 9 15 st.val))) 3 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (by have := symIdxOfCode_lt a (symOfIdx (unpackZ (2 ^ b) 9 15 st.val)); omega) (by decide))
      (((Tape.mk L (a :: R)).write a).move Dir.right) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 3 的一步规格：回到标记位，右移。 -/
theorem simStep_step_phase3 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 3) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 4 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write a).move Dir.right) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 5 的一步规格：进入改写脚本，左移到第二个编码符号。 -/
theorem simStep_step_phase5 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 5) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 6 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write a).move Dir.left) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 6 的一步规格：写入新编码的第二个符号，左移。 -/
theorem simStep_step_phase6 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 6) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 7 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write (codeSnd (symOfIdx (unpackZ (2 ^ b) 9 15 st.val / 3)))).move Dir.left) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 7 的一步规格：写入新编码的第一个符号，右移。 -/
theorem simStep_step_phase7 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 7) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 8 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write (codeFst (symOfIdx (unpackZ (2 ^ b) 9 15 st.val / 3)))).move Dir.right) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 8 的一步规格：回到标记位，右移。 -/
theorem simStep_step_phase8 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 8) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 9 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write a).move Dir.right) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 9 的一步规格：在标记位写 `some false`，沿模拟方向移动一格。 -/
theorem simStep_step_phase9 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 9) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 10 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write (some false)).move (dirOf (unpackZ (2 ^ b) 9 15 st.val % 3))) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 10 的一步规格：沿模拟方向移动一格。 -/
theorem simStep_step_phase10 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 10) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 11 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write a).move (dirOf (unpackZ (2 ^ b) 9 15 st.val % 3))) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 11 的一步规格：沿模拟方向再移动一格。 -/
theorem simStep_step_phase11 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 11) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 12 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write a).move (dirOf (unpackZ (2 ^ b) 9 15 st.val % 3))) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 12 的一步规格：在新位置写标记 `some true`，进入阶段 13。 -/
theorem simStep_step_phase12 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 12) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk
      (codeState q b (unpackM (2 ^ b) 9 15 st.val) (unpackC (2 ^ b) 9 15 st.val) (unpackZ (2 ^ b) 9 15 st.val) 13 (unpackM_lt q b st.val st.isLt) (unpackC_lt (2 ^ b) 9 15 st.val (Nat.two_pow_pos b)) (unpackZ_lt (2 ^ b) 9 15 st.val (by decide)) (by decide))
      (((Tape.mk L (a :: R)).write (some true)).move Dir.stay) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 13 的一步规格：成功终止态，不再移动。 -/
theorem simStep_step_phase13 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 13) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk st (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
  simp [Tape.move]

/-- 阶段 14 的一步规格：失败终止态，不再移动。 -/
theorem simStep_step_phase14 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (st : Fin (stateCount q b)) (a : Sym) (L R : List Sym)
    (hP : unpackPh (2 ^ b) 9 15 st.val = 14) :
    (simStep q b tab s0).stepConfig (Config.mk st (Tape.mk L (a :: R))) =
    Config.mk st (Tape.mk L (a :: R)) := by
  simp only [DTM.stepConfig, simStep, hP, Tape.read, Tape.write, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
  simp [Tape.move]

/-- 编号合成再还原：符号编号与符号来回无损。 -/
theorem symOfIdx_symIdx (s : Sym) : symOfIdx (symIdx s) = s := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- 阶段不同 ⇒ 压缩后的状态号不同（用于判定未停机）。 -/
theorem packIdx_ph_ne (D Z P m c z ph m' c' z' : Nat) (hD : 0 < D) (hZ : 0 < Z)
    (hP : 0 < P) (hph : ph < P) (hph' : 13 < P) (h : ph ≠ 13) :
    packIdx D Z P m c z ph ≠ packIdx D Z P m' c' z' 13 := by
  intro heq
  have h1 := congrArg (unpackPh D Z P) heq
  rw [unpackPh_pack_of_lt D Z P m c z ph hph,
    unpackPh_pack_of_lt D Z P m' c' z' 13 hph'] at h1
  exact h h1

/-- 在「查表专用状态」上，`lookupRes` 就是 `pick (tab m s) c`。 -/
theorem lookupRes_packIdxForm (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (hph : ph < 15)
    (hn : packIdx (2 ^ b) 9 15 m c z ph < stateCount q b) :
    lookupRes q b tab (⟨packIdx (2 ^ b) 9 15 m c z ph, hn⟩ : Fin (stateCount q b))
      = pick (tab (⟨m, hm⟩ : Fin q) (symOfIdx z)) c := by
  simp only [lookupRes, decM, decC, decZ,
    unpackM_pack_of_lt (2 ^ b) 9 15 m c z ph (Nat.two_pow_pos b) (by decide) (by decide) hc hz hph,
    unpackC_pack_of_lt (2 ^ b) 9 15 m c z ph (Nat.two_pow_pos b) (by decide) (by decide) hz hph hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c z ph (by decide) (by decide) hph hz]

/-- `codeState` 形式下的同一结论。 -/
theorem lookupRes_codeState (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9) (hph : ph < 15) :
    lookupRes q b tab (codeState q b m c z ph hm hc hz hph)
      = pick (tab (⟨m, hm⟩ : Fin q) (symOfIdx z)) c := by
  unfold codeState
  exact lookupRes_packIdxForm q b tab m c z ph hm hc hz hph _

/-- 阶段不等于 13 时，模拟机尚未停机（accept/reject 都编码为阶段 13）。 -/
theorem simStep_halted_eq_false (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9)
    (hph : ph < 15) (h : ph ≠ 13) (t : Tape) :
    (simStep q b tab s0).halted
      (Config.mk (codeState q b m c z ph hm hc hz hph) t) = false := by
  have hne : codeState q b m c z ph hm hc hz hph
      ≠ codeState q b s0.val 0 0 13 s0.isLt (Nat.two_pow_pos b) (by decide) (by decide) := by
    intro heq
    exact packIdx_ph_ne (2 ^ b) 9 15 m c z ph s0.val 0 0 (Nat.two_pow_pos b) (by decide)
      (by decide) hph (by decide) h (congrArg Fin.val heq)
  simp [DTM.halted, simStep, hne]

/-- 标记位左侧的规范形：两个编码符号紧挨着标记位左侧。 -/
theorem tape_marker_left (s : Sym) (pre : List (Sym × Bool)) (L : List Sym) :
    List.reverse (codeCells pre ++ symCode s) ++ L
      = codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L) := by
  rw [symCode_eq s, List.reverse_append]
  simp


/-- `codeState` 的数值就是压缩结果（便于在 simp 中精确化简）。 -/
@[simp] theorem codeState_val (q b m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) :
    (codeState q b m c z ph hm hc hz hph).val = packIdx (2 ^ b) 9 15 m c z ph := rfl

/-- 读符号第 0 步：在标记位左移一格（不改纸带符号）。 -/
theorem simStep_readStep0 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L))
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m c 0 1 hm hc (by decide) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c 0 0 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c 0 0 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by decide) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c 0 0 (Nat.two_pow_pos b) (by decide) (by decide)
      (by decide) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c 0 0 (by decide) (by decide) (by decide) (by decide),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 读符号第 1 步：在第二个编码符号处记录编号，左移。 -/
theorem simStep_readStep1 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c 0 1 hm hc (by decide) (by decide))
        (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
                 (codeSnd s :: some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc
        (by have := symIdx_lt (codeSnd s); omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre) ++ L)
               (codeFst s :: codeSnd s :: some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c 0 1 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c 0 1 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by decide) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c 0 1 (Nat.two_pow_pos b) (by decide) (by decide)
      (by decide) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c 0 1 (by decide) (by decide) (by decide) (by decide),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 读符号第 2 步：在两个编码符号上解码出符号编号，右移。 -/
theorem simStep_readStep2 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc
          (by have := symIdx_lt (codeSnd s); omega) (by decide))
        (Tape.mk (List.reverse (codeCells pre) ++ L)
                 (codeFst s :: codeSnd s :: some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s) 3 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx (codeSnd s)) 2 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx (codeSnd s)) 2 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt (codeSnd s); omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx (codeSnd s)) 2 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt (codeSnd s); omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx (codeSnd s)) 2 (by decide) (by decide) (by decide)
      (by have := symIdx_lt (codeSnd s); omega),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail, symOfIdx_symIdx, symIdxOfCode_symCode]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 读符号第 3 步：回到标记位，进入查表阶段。 -/
theorem simStep_readStep3 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s) 3 hm hc
          (by have := symIdx_lt s; omega) (by decide))
        (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
                 (codeSnd s :: some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s) 4 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L))
               (some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 3 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 3 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 3 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 3 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s; omega),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 4 步链：给定每步的 `stepConfig` 等式与未停机证据，4 步后的配置就是 `c4`。 -/
theorem run_four_of_steps (M : DTM q) {c0 c1 c2 c3 c4 : Config q}
    (h0 : M.halted c0 = false) (h1 : M.halted c1 = false)
    (h2 : M.halted c2 = false) (h3 : M.halted c3 = false)
    (e0 : M.stepConfig c0 = c1) (e1 : M.stepConfig c1 = c2)
    (e2 : M.stepConfig c2 = c3) (e3 : M.stepConfig c3 = c4) :
    M.run 4 c0 = c4 := by
  rw [show (4 : Nat) = 3 + 1 by rfl, DTM.run_succ_of_not_halted M 3 c0 h0, e0]
  rw [show (3 : Nat) = 2 + 1 by rfl, DTM.run_succ_of_not_halted M 2 c1 h1, e1]
  rw [show (2 : Nat) = 1 + 1 by rfl, DTM.run_succ_of_not_halted M 1 c2 h2, e2]
  rw [DTM.run_succ_of_not_halted M 0 c3 h3, e3]
  simp [DTM.run]

/-- 读符号整体：从阶段 0、读写头在标记位出发，4 步后回到标记位，
    状态携带 `symIdx s` 并进入阶段 4，纸带完全恢复。 -/
theorem simStep_read_run (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).run 4
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s) 4 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
               (some true :: codeCells post)) := by
  rw [tape_marker_left s pre L]
  refine run_four_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c 0 1 hm hc (by decide) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc
        (by have := symIdx_lt (codeSnd s); omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre) ++ L)
               (codeFst s :: codeSnd s :: some true :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s) 3 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c 0 0 hm hc (by decide) (by decide)
      (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c 0 1 hm hc (by decide) (by decide)
      (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx (codeSnd s)) 2 hm hc
      (by have := symIdx_lt (codeSnd s); omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s) 3 hm hc
      (by have := symIdx_lt s; omega) (by decide) (by decide) _
  · exact simStep_readStep0 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep1 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep2 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep3 q b tab s0 m c hm hc s pre post L

/-- 查表步（失败）：阶段 4 查不到候选动作，转入失败阶段 14，纸带不变。 -/
theorem simStep_lookupStep_none (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (a : Sym) (L R : List Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = none) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s) 4 hm hc
          (by have := symIdx_lt s; omega) (by decide))
        (Tape.mk L (a :: R))) =
    Config.mk (codeState q b m c (symIdx s) 14 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk L (a :: R)) := by
  have hP : unpackPh (2 ^ b) 9 15 (codeState q b m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide)).val = 4 := by
    simp only [codeState_val,
      unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide)]
  have h' : lookupRes q b tab (codeState q b m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide)) = none := by
    rw [lookupRes_codeState, symOfIdx_symIdx]
    exact h
  rw [simStep_step_phase4_none q b tab s0
      (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide))
      a L R hP h']
  simp only [codeState_val,
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s; omega)]

/-- 查表步（命中）：记下新状态、新符号编号与方向，进入写脚本阶段 5，纸带不变。 -/
theorem simStep_lookupStep_some (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (a : Sym) (L R : List Sym) (m' : Fin q) (s' : Sym) (d : Dir)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', d)) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s) 4 hm hc
          (by have := symIdx_lt s; omega) (by decide))
        (Tape.mk L (a :: R))) =
    Config.mk (codeState q b m'.val c (symIdx s' * 3 + dirVal d) 5 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk L (a :: R)) := by
  have hP : unpackPh (2 ^ b) 9 15 (codeState q b m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide)).val = 4 := by
    simp only [codeState_val,
      unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide)]
  have h' : lookupRes q b tab (codeState q b m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide)) = some (m', s', d) := by
    rw [lookupRes_codeState, symOfIdx_symIdx]
    exact h
  rw [simStep_step_phase4_some q b tab s0
      (codeState q b m c (symIdx s) 4 hm hc (by have := symIdx_lt s; omega) (by decide))
      a L R hP m' s' d h']
  simp only [codeState_val,
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s; omega) (by decide) hc]

/-- 5 步链：在 4 步链的基础上再接一步。 -/
theorem run_five_of_steps (M : DTM q) {c0 c1 c2 c3 c4 c5 : Config q}
    (h0 : M.halted c0 = false) (h1 : M.halted c1 = false)
    (h2 : M.halted c2 = false) (h3 : M.halted c3 = false)
    (h4 : M.halted c4 = false)
    (e0 : M.stepConfig c0 = c1) (e1 : M.stepConfig c1 = c2)
    (e2 : M.stepConfig c2 = c3) (e3 : M.stepConfig c3 = c4)
    (e4 : M.stepConfig c4 = c5) :
    M.run 5 c0 = c5 := by
  rw [show (5 : Nat) = 4 + 1 by rfl, DTM.run_add]
  rw [run_four_of_steps M h0 h1 h2 h3 e0 e1 e2 e3]
  rw [show (1 : Nat) = 0 + 1 by rfl, DTM.run_succ_of_not_halted M 0 c4 h4, e4]
  simp [DTM.run]

/-- 读符号 + 查表（失败）：5 步后进入失败阶段 14，纸带不变。 -/
theorem simStep_readLookup_run_none (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = none) :
    (simStep q b tab s0).run 5
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s) 14 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
               (some true :: codeCells post)) := by
  rw [tape_marker_left s pre L]
  refine run_five_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c 0 1 hm hc (by decide) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc
        (by have := symIdx_lt (codeSnd s); omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre) ++ L)
               (codeFst s :: codeSnd s :: some true :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s) 3 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)))
    (c4 := Config.mk (codeState q b m c (symIdx s) 4 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L))
               (some true :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c 0 0 hm hc (by decide) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c 0 1 hm hc (by decide) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx (codeSnd s)) 2 hm hc
      (by have := symIdx_lt (codeSnd s); omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s) 3 hm hc
      (by have := symIdx_lt s; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide) (by decide) _
  · exact simStep_readStep0 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep1 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep2 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep3 q b tab s0 m c hm hc s pre post L
  · exact simStep_lookupStep_none q b tab s0 m c hm hc s (some true)
      (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells post) h

/-- 读符号 + 查表（命中）：5 步后进入写脚本阶段 5，状态携带 `m'`、新符号编号与方向，
    纸带不变。 -/
theorem simStep_readLookup_run_some (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) (m' : Fin q) (s' : Sym) (d : Dir)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', d)) :
    (simStep q b tab s0).run 5
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m'.val c (symIdx s' * 3 + dirVal d) 5 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
               (some true :: codeCells post)) := by
  rw [tape_marker_left s pre L]
  refine run_five_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c 0 1 hm hc (by decide) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx (codeSnd s)) 2 hm hc
        (by have := symIdx_lt (codeSnd s); omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre) ++ L)
               (codeFst s :: codeSnd s :: some true :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s) 3 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)))
    (c4 := Config.mk (codeState q b m c (symIdx s) 4 hm hc
        (by have := symIdx_lt s; omega) (by decide))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L))
               (some true :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c 0 0 hm hc (by decide) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c 0 1 hm hc (by decide) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx (codeSnd s)) 2 hm hc
      (by have := symIdx_lt (codeSnd s); omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s) 3 hm hc
      (by have := symIdx_lt s; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide) (by decide) _
  · exact simStep_readStep0 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep1 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep2 q b tab s0 m c hm hc s pre post L
  · exact simStep_readStep3 q b tab s0 m c hm hc s pre post L
  · exact simStep_lookupStep_some q b tab s0 m c hm hc s (some true)
      (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeCells post)
      m' s' d h

/-- 写脚本第 5 步：左移到旧格的第二个编码符号（进入改写脚本）。 -/
theorem simStep_writeStep5 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 5 hm hc
          (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
        (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L))
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 6 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L))
               (codeSnd s :: some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 5 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 5 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 5 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 5 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 编码后的符号编号除以 3 就是新符号。 -/
theorem symIdx_div_three (s' : Sym) (d : Dir) :
    (symIdx s' * 3 + dirVal d) / 3 = symIdx s' := by
  rw [Nat.mul_comm (symIdx s') 3, Nat.mul_add_div (by decide),
    Nat.div_eq_of_lt (dirVal_lt d), Nat.add_zero]

theorem symOfIdx_div_three (s' : Sym) (d : Dir) :
    symOfIdx ((symIdx s' * 3 + dirVal d) / 3) = s' := by
  rw [symIdx_div_three, symOfIdx_symIdx]

/-- 编码后的方向编号取模 3 就是移动方向。 -/
theorem dirVal_mod_three (s' : Sym) (d : Dir) :
    (symIdx s' * 3 + dirVal d) % 3 = dirVal d := by
  rw [Nat.mul_comm (symIdx s') 3, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (dirVal_lt d)]

theorem dirOf_mod_three (s' : Sym) (d : Dir) :
    dirOf ((symIdx s' * 3 + dirVal d) % 3) = d := by
  rw [dirVal_mod_three, dirOf_dirVal]


/-- 写脚本第 6 步：在旧格的第二个编码符号写入新符号的第二位，左移。 -/
theorem simStep_writeStep6 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
        (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 6 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 6 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 6 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 6 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), symOfIdx_div_three s' d,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 7 步：在旧格的第一个编码符号写入新符号的第一位，右移。 -/
theorem simStep_writeStep7 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
        (Tape.mk ((List.reverse (codeCells pre) ++ L)) (codeFst s :: codeSnd s' :: some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 7 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 7 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 7 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 7 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), symOfIdx_div_three s' d,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 8 步：回到旧格标记位，右移（下一步才按方向处理标记）。 -/
theorem simStep_writeStep8 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
        (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 8 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 8 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 8 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 8 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 写脚本第 9 步（原地）：把旧格标记改为 false。 -/
theorem simStep_writeStep9_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 9 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 9 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega), dirOf_mod_three s' Dir.stay,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 10 步（原地）：不移动。 -/
theorem simStep_writeStep10_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 10 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 10 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega), dirOf_mod_three s' Dir.stay,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 11 步（原地）：不移动。 -/
theorem simStep_writeStep11_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 11 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.stay) 11 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega), dirOf_mod_three s' Dir.stay,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 12 步（原地）：在新位置（仍是原格）写标记 true，进入阶段 13。 -/
theorem simStep_writeStep12_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir)
    (pre post : List (Sym × Bool)) (L : List Sym) (hd : d = Dir.stay) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal d) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 12 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal d) 12 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 写脚本整体（原地）：4 步后回到阶段 13，纸带恢复原样（标记仍为 true）。 -/
theorem simStep_writeRun_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).run 4
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 9 hm hc
          (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 13 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (some true :: codeCells post)) := by
  refine run_four_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 10 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (some false :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 11 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (some false :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 12 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (some false :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 9 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 10 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 11 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 12 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_writeStep9_stay q b tab s0 m c hm hc s s' pre post L
  · exact simStep_writeStep10_stay q b tab s0 m c hm hc s s' pre post L
  · exact simStep_writeStep11_stay q b tab s0 m c hm hc s s' pre post L
  · exact simStep_writeStep12_stay q b tab s0 m c hm hc s s' Dir.stay pre post L rfl

/-- 写脚本第 9 步（右移）：旧格标记改 false，右移一格。 -/
theorem simStep_writeStep9_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 9 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 9 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega), dirOf_mod_three s' Dir.right,
    cellCode, symCode_eq, hp, List.append_assoc, List.append_nil,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 10 步（右移）：移到右邻格第一个编码符号。 -/
theorem simStep_writeStep10_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
        (Tape.mk (some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: some false :: codeCells post')) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 10 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 10 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega), dirOf_mod_three s' Dir.right,
    cellCode, symCode_eq, hp, List.append_assoc, List.append_nil,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 11 步（右移）：移到右邻格标记位。 -/
theorem simStep_writeStep11_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
        (Tape.mk (codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: some false :: codeCells post'))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post')) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 11 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 11 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega), dirOf_mod_three s' Dir.right,
    cellCode, symCode_eq, hp, List.append_assoc, List.append_nil,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 12 步（右移）：在右邻格写标记 true，进入阶段 13。 -/
theorem simStep_writeStep12_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
        (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post'))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post')) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 12 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.right) 12 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega),
    cellCode, symCode_eq, hp, List.append_assoc, List.append_nil,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 新当前格挪到右邻格后，左部编码的逆序展开（供规范形对齐）。 -/
theorem codeCells_snoc_false_reverse (s' : Sym) (pre : List (Sym × Bool)) :
    List.reverse (codeCells (pre ++ [(s', false)]))
      = some false :: codeSnd s' :: codeFst s' :: List.reverse (codeCells pre) := by
  simp [codeCells, cellCode_of_false, symCode_eq, List.reverse_append]

/-- 写脚本整体（右移）：4 步后当前格移到右邻格，旧格标记置 false、
    新格标记置 true，纸带呈新规范形。 -/
theorem simStep_writeRun_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) :
    (simStep q b tab s0).run 4
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 9 hm hc
          (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
                 (some true :: codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post'))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 13 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false ::
          codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (some true :: codeCells post')) := by
  refine run_four_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 10 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    (c2 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 11 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L))
               (codeSnd p.1 :: some false :: codeCells post')))
    (c3 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 12 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' ::
          (List.reverse (codeCells pre) ++ L))
               (some false :: codeCells post')))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 9 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 10 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 11 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 12 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_writeStep9_right q b tab s0 m c hm hc s s' p post' pre L hp
  · exact simStep_writeStep10_right q b tab s0 m c hm hc s s' p post' pre L hp
  · exact simStep_writeStep11_right q b tab s0 m c hm hc s s' p post' pre L hp
  · exact simStep_writeStep12_right q b tab s0 m c hm hc s s' p post' pre L hp

/-- 写脚本第 9 步（左移）：旧格标记改 false，左移一格。 -/
theorem simStep_writeStep9_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' :: (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))) (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeFst s' :: (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))) (codeSnd s' :: some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 9 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 9 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega), dirOf_mod_three s' Dir.left,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 10 步（左移）：移到旧格第一个编码符号。 -/
theorem simStep_writeStep10_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
        (Tape.mk (codeFst s' :: (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))) (codeSnd s' :: some false :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 10 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 10 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega), dirOf_mod_three s' Dir.left,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 11 步（左移）：移到左邻格标记位。 -/
theorem simStep_writeStep11_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
        (Tape.mk (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: some false :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some false :: codeFst s' :: codeSnd s' :: some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 11 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 11 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega), dirOf_mod_three s' Dir.left,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 写脚本第 12 步（左移）：在左邻格写标记 true，进入阶段 13。 -/
theorem simStep_writeStep12_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).stepConfig
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
        (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some false :: codeFst s' :: codeSnd s' :: some false :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeFst s' :: codeSnd s' :: some false :: codeCells post)) := by
  simp only [DTM.stepConfig, simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 12 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s' * 3 + dirVal Dir.left) 12 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega),
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    Prod.fst, Prod.snd, List.headD, List.tail]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 写脚本整体（左移）：4 步后当前格移到左邻格，旧格标记置 false、
    新格标记置 true。 -/
theorem simStep_writeRun_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).run 4
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 9 hm hc
          (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
        (Tape.mk (codeSnd s' :: codeFst s' ::
            some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 13 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
               (some true :: codeFst s' :: codeSnd s' :: some false :: codeCells post)) := by
  refine run_four_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 10 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeFst s' :: some false :: codeSnd cq.1 :: codeFst cq.1 ::
          (List.reverse (codeCells pre') ++ L))
               (codeSnd s' :: some false :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 11 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
               (codeFst s' :: codeSnd s' :: some false :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 12 hm hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
               (some false :: codeFst s' :: codeSnd s' :: some false :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 9 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 10 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 11 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 12 hm hc
      (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_writeStep9_left q b tab s0 m c hm hc s s' cq pre' post L
  · exact simStep_writeStep10_left q b tab s0 m c hm hc s s' cq pre' post L
  · exact simStep_writeStep11_left q b tab s0 m c hm hc s s' cq pre' post L
  · exact simStep_writeStep12_left q b tab s0 m c hm hc s s' cq pre' post L

/-- 8 步链：两次 4 步链拼接。 -/
theorem run_eight_of_steps (M : DTM q) {c0 c1 c2 c3 c4 c5 c6 c7 c8 : Config q}
    (h0 : M.halted c0 = false) (h1 : M.halted c1 = false)
    (h2 : M.halted c2 = false) (h3 : M.halted c3 = false)
    (h4 : M.halted c4 = false) (h5 : M.halted c5 = false)
    (h6 : M.halted c6 = false) (h7 : M.halted c7 = false)
    (e0 : M.stepConfig c0 = c1) (e1 : M.stepConfig c1 = c2)
    (e2 : M.stepConfig c2 = c3) (e3 : M.stepConfig c3 = c4)
    (e4 : M.stepConfig c4 = c5) (e5 : M.stepConfig c5 = c6)
    (e6 : M.stepConfig c6 = c7) (e7 : M.stepConfig c7 = c8) :
    M.run 8 c0 = c8 := by
  rw [show (8 : Nat) = 4 + 4 by rfl, DTM.run_add]
  rw [run_four_of_steps M h0 h1 h2 h3 e0 e1 e2 e3]
  rw [run_four_of_steps M h4 h5 h6 h7 e4 e5 e6 e7]

/-- 写脚本整体（原地，8 步）：阶段 5 → 13，纸带恢复原样。 -/
theorem simStep_write8_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) :
    (simStep q b tab s0).run 8
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post)) := by
  refine run_eight_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: some true :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre) ++ L) (codeFst s :: codeSnd s' :: some true :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: some true :: codeCells post)))
    (c4 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post)))
    (c5 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post)))
    (c6 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post)))
    (c7 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.stay) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.stay) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide) (by decide) _
  · exact simStep_writeStep5 q b tab s0 m c hm hc s s' Dir.stay pre post L
  · exact simStep_writeStep6 q b tab s0 m c hm hc s s' Dir.stay pre post L
  · exact simStep_writeStep7 q b tab s0 m c hm hc s s' Dir.stay pre post L
  · exact simStep_writeStep8 q b tab s0 m c hm hc s s' Dir.stay pre post L
  · exact simStep_writeStep9_stay q b tab s0 m c hm hc s s' pre post L
  · exact simStep_writeStep10_stay q b tab s0 m c hm hc s s' pre post L
  · exact simStep_writeStep11_stay q b tab s0 m c hm hc s s' pre post L
  · exact simStep_writeStep12_stay q b tab s0 m c hm hc s s' Dir.stay pre post L rfl

/-- 把 5 步链与 8 步链拼成 13 步。 -/
theorem run_13_of_5_8 (M : DTM q) {c0 c5 c13 : Config q}
    (h5 : M.run 5 c0 = c5) (h8 : M.run 8 c5 = c13) : M.run 13 c0 = c13 := by
  rw [show (13 : Nat) = 5 + 8 by rfl, DTM.run_add]
  rw [h5, h8]

/-- 一整轮模拟（原地）：从阶段 0、读写头在标记位出发，13 步后到达阶段 13，
    纸带恢复原样（当前格不变，符号已改写）。 -/
theorem simStep_round_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre post : List (Sym × Bool)) (L : List Sym) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.stay)) :
    (simStep q b tab s0).run 13
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre ++ symCode s') ++ L)
               (some true :: codeCells post)) := by
  have h5 := simStep_readLookup_run_some q b tab s0 m c hm hc s pre post L m' s' Dir.stay h
  rw [tape_marker_left s pre L] at h5
  have h8 := simStep_write8_stay q b tab s0 m'.val c m'.isLt hc s s' pre post L
  have h13 := run_13_of_5_8 (simStep q b tab s0) h5 h8
  rw [tape_marker_left s pre L]
  rw [h13]
  rw [← tape_marker_left s' pre L]

/-- 写脚本整体（右移，8 步）：阶段 5 → 13，当前格移到右邻格。 -/
theorem simStep_write8_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (pre : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) :
    (simStep q b tab s0).run 8
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd s :: codeFst s :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells (p :: post')))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells post')) := by
  refine run_eight_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeFst s :: (List.reverse (codeCells pre) ++ L)) (codeSnd s :: some true :: codeCells (p :: post'))))
    (c2 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (List.reverse (codeCells pre) ++ L) (codeFst s :: codeSnd s' :: some true :: codeCells (p :: post'))))
    (c3 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd s' :: some true :: codeCells (p :: post'))))
    (c4 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some true :: codeCells (p :: post'))))
    (c5 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeFst p.1 :: codeSnd p.1 :: some false :: codeCells post')))
    (c6 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (codeSnd p.1 :: some false :: codeCells post')))
    (c7 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.right) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells pre) ++ L)) (some false :: codeCells post')))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.right) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide) (by decide) _
  · exact simStep_writeStep5 q b tab s0 m c hm hc s s' Dir.right pre (p :: post') L
  · exact simStep_writeStep6 q b tab s0 m c hm hc s s' Dir.right pre (p :: post') L
  · exact simStep_writeStep7 q b tab s0 m c hm hc s s' Dir.right pre (p :: post') L
  · exact simStep_writeStep8 q b tab s0 m c hm hc s s' Dir.right pre (p :: post') L
  · simpa only [codeCells, List.flatMap_cons, cellCode, symCode_eq, hp, Bool.false_eq_true, ite_false,
      List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using
      simStep_writeStep9_right q b tab s0 m c hm hc s s' p post' pre L hp
  · simpa only [codeCells, List.flatMap_cons, cellCode, symCode_eq, hp, Bool.false_eq_true, ite_false,
      List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using
      simStep_writeStep10_right q b tab s0 m c hm hc s s' p post' pre L hp
  · simpa only [codeCells, List.flatMap_cons, cellCode, symCode_eq, hp, Bool.false_eq_true, ite_false,
      List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using
      simStep_writeStep11_right q b tab s0 m c hm hc s s' p post' pre L hp
  · simpa only [codeCells, List.flatMap_cons, cellCode, symCode_eq, hp, Bool.false_eq_true, ite_false,
      List.cons_append, List.singleton_append, List.append_assoc, List.nil_append] using
      simStep_writeStep12_right q b tab s0 m c hm hc s s' p post' pre L hp

/-- 一整轮模拟（右移）：从阶段 0 出发，13 步后当前格移到右邻格。 -/
theorem simStep_round_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre : List (Sym × Bool)) (p : Sym × Bool) (post' : List (Sym × Bool)) (L : List Sym)
    (hp : p.2 = false) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.right)) :
    (simStep q b tab s0).run 13
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (List.reverse (codeCells pre ++ symCode s) ++ L)
                 (some true :: codeCells (p :: post')))) =
    Config.mk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide))
      (Tape.mk (codeSnd p.1 :: codeFst p.1 ::
          List.reverse (codeCells (pre ++ [(s', false)])) ++ L)
               (some true :: codeCells post')) := by
  have h5 := simStep_readLookup_run_some q b tab s0 m c hm hc s pre (p :: post') L
    m' s' Dir.right h
  rw [tape_marker_left s pre L] at h5
  have h8 := simStep_write8_right q b tab s0 m'.val c m'.isLt hc s s' p post' pre L hp
  have h13 := run_13_of_5_8 (simStep q b tab s0) h5 h8
  rw [tape_marker_left s pre L]
  rw [h13]
  rw [show codeSnd p.1 :: codeFst p.1 :: some false :: codeSnd s' :: codeFst s' ::
        (List.reverse (codeCells pre) ++ L)
      = codeSnd p.1 :: codeFst p.1 ::
          List.reverse (codeCells (pre ++ [(s', false)])) ++ L from by
    rw [codeCells_snoc_false_reverse]
    rfl]

/-- 在左侧串上追加一格（标记 false）后逆序展开。 -/
theorem codeCells_snoc_false_reverse_gen (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) :
    List.reverse (codeCells (pre' ++ [cq]))
      = some false :: codeSnd cq.1 :: codeFst cq.1 :: List.reverse (codeCells pre') := by
  simp [codeCells, cellCode_of_false, symCode_eq, List.reverse_append, hq]

/-- 写脚本整体（左移，8 步）：阶段 5 → 13，当前格移到左邻格。 -/
theorem simStep_write8_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (post : List (Sym × Bool)) (L : List Sym)
    (hq : cq.2 = false) :
    (simStep q b tab s0).run 8
      (Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd s :: codeFst s :: some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeCells post))) =
    Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeFst s' :: codeSnd s' :: some false :: codeCells post)) := by
  refine run_eight_of_steps (simStep q b tab s0)
    (c1 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeFst s :: some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s :: some true :: codeCells post)))
    (c2 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s :: codeSnd s' :: some true :: codeCells post)))
    (c3 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeFst s' :: some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: some true :: codeCells post)))
    (c4 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd s' :: codeFst s' :: some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some true :: codeCells post)))
    (c5 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeFst s' :: some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeSnd s' :: some false :: codeCells post)))
    (c6 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (codeFst s' :: codeSnd s' :: some false :: codeCells post)))
    (c7 := Config.mk (codeState q b m c (symIdx s' * 3 + dirVal Dir.left) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) (some false :: codeFst s' :: codeSnd s' :: some false :: codeCells post)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · exact simStep_halted_eq_false q b tab s0 m c (symIdx s' * 3 + dirVal Dir.left) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide) (by decide) _
  · simpa [codeCells, cellCode, symCode_eq, hq] using
      simStep_writeStep5 q b tab s0 m c hm hc s s' Dir.left (pre' ++ [cq]) post L
  · simpa [codeCells, cellCode, symCode_eq, hq] using
      simStep_writeStep6 q b tab s0 m c hm hc s s' Dir.left (pre' ++ [cq]) post L
  · simpa [codeCells, cellCode, symCode_eq, hq] using
      simStep_writeStep7 q b tab s0 m c hm hc s s' Dir.left (pre' ++ [cq]) post L
  · simpa [codeCells, cellCode, symCode_eq, hq] using
      simStep_writeStep8 q b tab s0 m c hm hc s s' Dir.left (pre' ++ [cq]) post L
  · exact simStep_writeStep9_left q b tab s0 m c hm hc s s' cq pre' post L
  · exact simStep_writeStep10_left q b tab s0 m c hm hc s s' cq pre' post L
  · exact simStep_writeStep11_left q b tab s0 m c hm hc s s' cq pre' post L
  · exact simStep_writeStep12_left q b tab s0 m c hm hc s s' cq pre' post L


/-- 一整轮模拟（左移）：从阶段 0 出发，13 步后当前格移到左邻格。 -/
theorem simStep_round_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (pre' : List (Sym × Bool)) (cq : Sym × Bool) (post : List (Sym × Bool)) (L : List Sym)
    (hq : cq.2 = false) (m' : Fin q) (s' : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', Dir.left)) :
    (simStep q b tab s0).run 13
      (Config.mk (codeState q b m c 0 0 hm hc (by decide) (by decide))
        (Tape.mk (codeSnd s :: codeFst s ::
            some false :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
                 (some true :: codeCells post))) =
    Config.mk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc
        (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide))
      (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
               (some true :: codeCells ((s', false) :: post))) := by
  have hkey : List.reverse (codeCells (pre' ++ [cq]) ++ symCode s) ++ L
      = codeSnd s :: codeFst s :: some false :: codeSnd cq.1 :: codeFst cq.1 ::
          (List.reverse (codeCells pre') ++ L) := by
    rw [tape_marker_left s (pre' ++ [cq]) L, codeCells_snoc_false_reverse_gen cq pre' hq]
    rfl
  have h5 := simStep_readLookup_run_some q b tab s0 m c hm hc s (pre' ++ [cq]) post L
    m' s' Dir.left h
  rw [hkey] at h5
  have h8 := simStep_write8_left q b tab s0 m'.val c m'.isLt hc s s' cq pre' post L hq
  have h13 := run_13_of_5_8 (simStep q b tab s0) h5 h8
  rw [h13]
  rw [show some true :: codeFst s' :: codeSnd s' :: some false :: codeCells post
      = some true :: codeCells ((s', false) :: post) from by
    simp [codeCells, cellCode_of_false, symCode_eq]]

/-- `codeState` 上阶段解包。 -/
theorem codeState_unpackPh (q b m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) :
    unpackPh (2 ^ b) 9 15 (codeState q b m c z ph hm hc hz hph).val = ph := by
  rw [codeState_val, unpackPh_pack_of_lt (2 ^ b) 9 15 m c z ph hph]

/-- `codeState` 上状态解包。 -/
theorem codeState_unpackM (q b m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) :
    unpackM (2 ^ b) 9 15 (codeState q b m c z ph hm hc hz hph).val = m := by
  rw [codeState_val, unpackM_pack_of_lt (2 ^ b) 9 15 m c z ph
    (Nat.two_pow_pos b) (by decide) (by decide) hc hz hph]

/-- `codeState` 上选择编号解包。 -/
theorem codeState_unpackC (q b m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) :
    unpackC (2 ^ b) 9 15 (codeState q b m c z ph hm hc hz hph).val = c := by
  rw [codeState_val, unpackC_pack_of_lt (2 ^ b) 9 15 m c z ph
    (Nat.two_pow_pos b) (by decide) (by decide) hz hph hc]

/-- `codeState` 上符号/方向组合解包。 -/
theorem codeState_unpackZ (q b m c z ph : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (hz : z < 9) (hph : ph < 15) :
    unpackZ (2 ^ b) 9 15 (codeState q b m c z ph hm hc hz hph).val = z := by
  rw [codeState_val, unpackZ_pack_of_lt (2 ^ b) 9 15 m c z ph (by decide) (by decide) hph hz]

/-- 阶段 0 的 step 级一步（供 `simAll` 链使用）。 -/
theorem simStep_stepC0 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c 0 0 hm hc (by decide) (by decide)).val,
        (codeState q b m c 0 0 hm hc (by decide) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some true)
      = (codeState q b m c 0 1 hm hc (by decide) (by decide), some true, Dir.left) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c 0 0 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c 0 0 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by decide) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c 0 0 (Nat.two_pow_pos b) (by decide) (by decide)
      (by decide) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c 0 0 (by decide) (by decide) (by decide) (by decide)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 1 的 step 级一步。 -/
theorem simStep_stepC1 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c (0) 1 hm hc (by decide) (by decide)).val,
        (codeState q b m c (0) 1 hm hc (by decide) (by decide)).isLt⟩ : Fin (stateCount q b))
      (codeSnd s)
      = (codeState q b m c ((symIdx (codeSnd s))) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide), codeSnd s, Dir.left) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (0) 1 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (0) 1 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by decide) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (0) 1 (Nat.two_pow_pos b) (by decide) (by decide)
      (by decide) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (0) 1 (by decide) (by decide) (by decide)
      (by decide)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 2 的 step 级一步。 -/
theorem simStep_stepC2 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx (codeSnd s))) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).val,
        (codeState q b m c ((symIdx (codeSnd s))) 2 hm hc (by have := symIdx_lt (codeSnd s); omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (codeFst s)
      = (codeState q b m c ((symIdx s)) 3 hm hc (by have := symIdx_lt s; omega) (by decide), codeFst s, Dir.right) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx (codeSnd s))) 2 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx (codeSnd s))) 2 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt (codeSnd s); omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx (codeSnd s))) 2 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt (codeSnd s); omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx (codeSnd s))) 2 (by decide) (by decide) (by decide)
      (by have := symIdx_lt (codeSnd s); omega), symOfIdx_symIdx, symIdxOfCode_symCode]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 3 的 step 级一步。 -/
theorem simStep_stepC3 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s)) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).val,
        (codeState q b m c ((symIdx s)) 3 hm hc (by have := symIdx_lt s; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (codeSnd s)
      = (codeState q b m c ((symIdx s)) 4 hm hc (by have := symIdx_lt s; omega) (by decide), codeSnd s, Dir.right) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s)) 3 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s)) 3 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s)) 3 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s)) 3 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s; omega)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 5 的 step 级一步。 -/
theorem simStep_stepC5 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 5 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some true)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), some true, Dir.left) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 5 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 5 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 5 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 5 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 6 的 step 级一步。 -/
theorem simStep_stepC6 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 6 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (codeSnd s)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), codeSnd s', Dir.left) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 6 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 6 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 6 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 6 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), symOfIdx_div_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 7 的 step 级一步。 -/
theorem simStep_stepC7 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 7 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (codeFst s)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), codeFst s', Dir.right) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 7 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 7 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 7 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 7 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), symOfIdx_div_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 8 的 step 级一步。 -/
theorem simStep_stepC8 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 8 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (codeSnd s')
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), codeSnd s', Dir.right) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 8 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 8 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 8 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 8 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 9 的 step 级一步。 -/
theorem simStep_stepC9 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 9 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some true)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), some false, dirOf ((symIdx s' * 3 + dirVal d) % 3)) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 9 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 9 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 9 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), dirOf_mod_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 10 的 step 级一步。 -/
theorem simStep_stepC10 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some false)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), some false, dirOf ((symIdx s' * 3 + dirVal d) % 3)) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), dirOf_mod_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 11 的 step 级一步。 -/
theorem simStep_stepC11 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some false)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), some false, dirOf ((symIdx s' * 3 + dirVal d) % 3)) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), dirOf_mod_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]
/-- 阶段 12 的 step 级一步。 -/
theorem simStep_stepC12 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some false)
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), some true, Dir.stay) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 10 的 step 级一步（任意读入符号）。 -/
theorem simStep_stepC10' (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) (a : Sym) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 10 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      a
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), a, dirOf ((symIdx s' * 3 + dirVal d) % 3)) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 10 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), dirOf_mod_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 11 的 step 级一步（任意读入符号）。 -/
theorem simStep_stepC11' (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) (a : Sym) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 11 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      a
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), a, dirOf ((symIdx s' * 3 + dirVal d) % 3)) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 11 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega), dirOf_mod_three s' d]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 12 的 step 级一步（任意读入符号）。 -/
theorem simStep_stepC12' (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir) (a : Sym) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c ((symIdx s' * 3 + dirVal d)) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).val,
        (codeState q b m c ((symIdx s' * 3 + dirVal d)) 12 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      a
      = (codeState q b m c ((symIdx s' * 3 + dirVal d)) 13 hm hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide), some true, Dir.stay) := by
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c ((symIdx s' * 3 + dirVal d)) 12 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s'; have := dirVal_lt d; omega)]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 4 的 step 级一步：查表并转移到阶段 5。 -/
theorem simStep_stepC4 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s s' : Sym) (d : Dir)
    (m' : Fin q) (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = some (m', s', d)) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c (symIdx s) 4 hm hc
          (by have := symIdx_lt s; omega) (by decide)).val,
        (codeState q b m c (symIdx s) 4 hm hc
          (by have := symIdx_lt s; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some true)
      = (codeState q b m'.val c (symIdx s' * 3 + dirVal d) 5 m'.isLt hc
          (by have := symIdx_lt s'; have := dirVal_lt d; omega) (by decide),
         some true, Dir.stay) := by
  have hlk : lookupRes q b tab
      (⟨packIdx (2 ^ b) 9 15 m c (symIdx s) 4, by
        unfold stateCount
        exact packIdx_lt (Nat.two_pow_pos b) (by decide) (by decide) hm hc
          (by have := symIdx_lt s; omega) (by decide)⟩ : Fin (stateCount q b))
      = pick (tab (⟨m, hm⟩ : Fin q) s) c := by
    rw [lookupRes_packIdxForm q b tab m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide) _]
    rw [symOfIdx_symIdx]
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s; omega),
    hlk, symOfIdx_symIdx, h]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

/-- 阶段 4 的 step 级一步（查表失败）：转移到失败阶段 14。 -/
theorem simStep_stepC4_none (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) (s : Sym)
    (h : pick (tab (⟨m, hm⟩ : Fin q) s) c = none) :
    (simStep q b tab s0).step
      (⟨(codeState q b m c (symIdx s) 4 hm hc
          (by have := symIdx_lt s; omega) (by decide)).val,
        (codeState q b m c (symIdx s) 4 hm hc
          (by have := symIdx_lt s; omega) (by decide)).isLt⟩ : Fin (stateCount q b))
      (some true)
      = (codeState q b m c (symIdx s) 14 hm hc
          (by have := symIdx_lt s; omega) (by decide),
         some true, Dir.stay) := by
  have hlk : lookupRes q b tab
      (⟨packIdx (2 ^ b) 9 15 m c (symIdx s) 4, by
        unfold stateCount
        exact packIdx_lt (Nat.two_pow_pos b) (by decide) (by decide) hm hc
          (by have := symIdx_lt s; omega) (by decide)⟩ : Fin (stateCount q b))
      = pick (tab (⟨m, hm⟩ : Fin q) s) c := by
    rw [lookupRes_packIdxForm q b tab m c (symIdx s) 4 hm hc
      (by have := symIdx_lt s; omega) (by decide) _]
    rw [symOfIdx_symIdx]
  simp only [simStep, codeState_val,
    unpackPh_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide),
    unpackM_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      hc (by have := symIdx_lt s; omega) (by decide),
    unpackC_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (Nat.two_pow_pos b) (by decide) (by decide)
      (by have := symIdx_lt s; omega) (by decide) hc,
    unpackZ_pack_of_lt (2 ^ b) 9 15 m c (symIdx s) 4 (by decide) (by decide) (by decide)
      (by have := symIdx_lt s; omega),
    hlk, symOfIdx_symIdx, h]
  repeat' first | rw [if_neg (by decide)] | rw [if_pos (by decide)]

end DTM

end Pnp
