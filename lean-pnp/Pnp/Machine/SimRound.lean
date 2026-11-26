/-
  文件：Pnp/Machine/SimRound.lean
  File: Pnp/Machine/SimRound.lean

  主题：把「一轮模拟 13 步 + 进入导航 1 步」合成整轮 14 步规格（B5 阶段 3c-ii）。
  Topic: compose "13-step simulation round + 1 entry step into navigation" into a
  14-step round spec (B5 stage 3c-ii).

  取自 `simDrive` 的相位 13 分支：一轮结束后头停在模拟区的标记符号 `some true` 上，
  该步把计数清零、保留被模拟状态 `m`，进入导航层子相位 0 并向左移一格
  （新头 = 当前格的第 2 个符号 `codeSnd s'`）。
  The phase-13 branch of `simDrive`: after a round the head rests on the marker
  symbol `some true`; this step clears the counter, keeps the simulated state `m`,
  enters navigation subphase 0 and moves left (new head = `codeSnd s'`).

  本文件给出：
    - `simDrive_step_ph13`：相位 13 的单步规格（读非空白，任意 `z`）；
    - `simDrive_run14_{stay,right,left}`：整轮 14 步规格（纸带用 `Reg.enc` 表述）；
    - `codeFst_ne_none` / `codeSnd_ne_none`：编码两符号非空白（回扫前提）；
    - `simDrive_roundNav_{stay,right,left}`：整轮 + 回扫，共 `14 + |L0| + 2` 步；
    - `simDrive_skipCount`：跳零 + 计数，共 `z + k + 3` 步，终值 `K = k + 2`；
    - `simDrive_roundNavCount_{stay,right,left}`：整轮 + 回扫 + 跳零 + 计数；
    - `replicate_ne_none` / `run_one`：擦除前提与「`run 1` = 一步」小工具；
    - `simDrive_ph2Erase`：读 `xc` 后把选择区擦成 0，进入子相位 4；
    - `simDrive_ph4Seek`：扫描选择区找到标记格，子相位 7；
    - `simDrive_roundFull_{stay,right,left}`：完整一轮（模拟→回扫→计数→擦除→找标记），
      终点回到模拟层相位 0、计数 `K - 1`，纸带恢复为新 `Reg.enc`。
  This file provides the phase-13 single-step spec, the three 14-step round specs
  (tapes via `Reg.enc`), the non-blank facts `codeFst_ne_none`/`codeSnd_ne_none`,
  the round-plus-rewind compositions (`14 + |L0| + 2` steps), the skip-plus-count
  segment (`z + k + 3` steps), their four-stage compositions, the erase/seek
  segments (`simDrive_ph2Erase`, `simDrive_ph4Seek`), and the full-round specs
  returning to simulation phase 0 with counter `K - 1`.
-/

import Pnp.Machine.SimDriveNav

set_option maxHeartbeats 2000000

namespace Pnp

namespace DTM

/-- **相位 13 单步**（读非空白符号）：一轮结束，进入导航层子相位 0，
    计数清零、向左移一格。
    Phase-13 step (non-blank read symbol): enter navigation subphase 0 with a cleared
    counter and move left. -/
theorem simDrive_step_ph13 (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c z : Nat) (hm : m < q) (hc : c < 2 ^ b) (hz : z < 9)
    (a : Sym) (ha : a ≠ none) :
    (simDrive q b tab s0).step
      (embS (codeState q b m c z 13 hm hc hz (by decide))) a =
    (embN (codeState q b m 0 0 0 hm (Nat.two_pow_pos b) (by decide) (by decide)),
      a, Dir.left) := by
  have h1 : (embS (codeState q b m c z 13 hm hc hz (by decide))).val
      < stateCount q b := by
    simp only [embS, Fin.val_mk]
    exact (codeState q b m c z 13 hm hc hz (by decide)).isLt
  have hp : unpackPh (2 ^ b) 9 15
      (embS (codeState q b m c z 13 hm hc hz (by decide))).val = 13 := by
    simp only [embS, Fin.val_mk]
    exact codeState_unpackPh q b m c z 13 hm hc hz (by decide)
  have hmv : unpackM (2 ^ b) 9 15
      (embS (codeState q b m c z 13 hm hc hz (by decide))).val = m := by
    simp only [embS, Fin.val_mk]
    exact codeState_unpackM q b m c z 13 hm hc hz (by decide)
  simp only [simDrive, dite_eq_left h1, hp, hmv]
  simp only [if_neg ha, if_true]

/-- **整轮 14 步（原地 / stay）**：13 步模拟 + 1 步进入导航，纸带停在当前格第 2 个符号上。
    14-step round (stay): 13 simulation steps + 1 navigation-entry step. -/
theorem simDrive_run14_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (L : List Sym) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simDrive q b tab s0).run 14
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L)) =
    Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk (codeFst s' :: (List.reverse (codeCells x.pre) ++ L))
        (codeSnd s' :: some true :: codeCells x.post)) := by
  rw [show (14 : Nat) = 13 + 1 from rfl]
  rw [DTM.run_add (simDrive q b tab s0) 13 1 _]
  change (simDrive q b tab s0).run 1
      ((simDrive q b tab s0).run 13
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L))) =
    Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk (codeFst s' :: (List.reverse (codeCells x.pre) ++ L))
        (codeSnd s' :: some true :: codeCells x.post))
  rw [simDrive_round_stay q b tab s0 m c hm hc x L m' s' hx h]
  rw [show (1 : Nat) = 0 + 1 from rfl,
    DTM.run_succ_of_not_halted _ 0 _
      (simDrive_halted_embS q b tab s0 _ _)]
  simp only [DTM.run]
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph13 q b tab s0 m'.val c
    (symIdx s' * 3 + dirVal Dir.stay) m'.isLt hc
    (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (some true) (by decide))]
  simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, Reg.enc, List.tail]

/-- **整轮 14 步（右移 / right）**：13 步模拟 + 1 步进入导航。
    14-step round (right move). -/
theorem simDrive_run14_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (L : List Sym) (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post') (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simDrive q b tab s0).run 14
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L)) =
    Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk (codeFst p.1 :: (List.reverse (codeCells (x.pre ++ [(s', false)])) ++ L))
        (codeSnd p.1 :: some true :: codeCells post')) := by
  rw [show (14 : Nat) = 13 + 1 from rfl]
  rw [DTM.run_add (simDrive q b tab s0) 13 1 _]
  change (simDrive q b tab s0).run 1
      ((simDrive q b tab s0).run 13
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L))) =
    Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk (codeFst p.1 :: (List.reverse (codeCells (x.pre ++ [(s', false)])) ++ L))
        (codeSnd p.1 :: some true :: codeCells post'))
  rw [simDrive_round_right q b tab s0 m c hm hc x L p post' hp hpost m' s' hx h]
  rw [show (1 : Nat) = 0 + 1 from rfl,
    DTM.run_succ_of_not_halted _ 0 _
      (simDrive_halted_embS q b tab s0 _ _)]
  simp only [DTM.run]
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph13 q b tab s0 m'.val c
    (symIdx s' * 3 + dirVal Dir.right) m'.isLt hc
    (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (some true) (by decide))]
  simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, Reg.enc, List.tail]

/-- **整轮 14 步（左移 / left）**：13 步模拟 + 1 步进入导航。
    14-step round (left move). -/
theorem simDrive_run14_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (L : List Sym) (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre : x.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simDrive q b tab s0).run 14
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L)) =
    Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk (codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
        (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))) := by
  rw [show (14 : Nat) = 13 + 1 from rfl]
  rw [DTM.run_add (simDrive q b tab s0) 13 1 _]
  change (simDrive q b tab s0).run 1
      ((simDrive q b tab s0).run 13
        (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide))) (x.enc L))) =
    Config.mk (embN (codeState q b m'.val 0 0 0 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk (codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
        (codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)))
  rw [simDrive_round_left q b tab s0 m c hm hc x L cq pre' hq hpre m' s' hx h]
  rw [show (1 : Nat) = 0 + 1 from rfl,
    DTM.run_succ_of_not_halted _ 0 _
      (simDrive_halted_embS q b tab s0 _ _)]
  simp only [DTM.run]
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph13 q b tab s0 m'.val c
    (symIdx s' * 3 + dirVal Dir.left) m'.isLt hc
    (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (some true) (by decide))]
  simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, Reg.enc, List.tail]


/-- 编码首符号非空白（供回扫引理使用）。-/
theorem codeFst_ne_none (s : Sym) : codeFst s ≠ none := by
  cases s with
  | none => simp [codeFst, symCode]
  | some b => cases b <;> simp [codeFst, symCode]

/-- 编码次符号非空白（供回扫引理使用）。-/
theorem codeSnd_ne_none (s : Sym) : codeSnd s ≠ none := by
  cases s with
  | none => simp [codeSnd, symCode]
  | some b => cases b <;> simp [codeSnd, symCode]

/-- **整轮 + 回扫**（原地 / stay）：14 步整轮后接导航回扫，共 `14 + |L0| + 2` 步，
    停在数字区第一个块（块 1）的右端符号 `a0` 上，子相位 1。
    Round + rewind (stay): 14-step round followed by the leftward rewind; the head ends
    on `a0`, the rightmost symbol of block 1, in subphase 1. -/
theorem simDrive_roundNav_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (a0 : Sym) (Z' : List Sym) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simDrive q b tab s0).run
        (14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: a0 :: Z'))) =
    Config.mk (embN (codeState q b m'.val 0 0 1 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk Z' (a0 :: none :: (codeFst s' :: List.reverse (codeCells x.pre)).reverse
        ++ codeSnd s' :: some true :: codeCells x.post)) := by
  rw [DTM.run_add (simDrive q b tab s0) 14 _]
  rw [simDrive_run14_stay q b tab s0 m c hm hc x (none :: a0 :: Z') m' s' hx h]
  simp only [← List.cons_append]
  rw [simDrive_rewind q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
    (codeSnd s') (codeFst s' :: List.reverse (codeCells x.pre)) (codeSnd_ne_none s')
    ?_ a0 Z' (some true :: codeCells x.post)]
  · intro y hy
    rcases (List.mem_cons.mp hy) with hy | hy
    · exact hy ▸ codeFst_ne_none s'
    · have hy' := List.mem_reverse.mp hy
      simp only [codeCells, List.mem_flatMap] at hy'
      obtain ⟨p, _, hp⟩ := hy'
      exact cellCode_ne_none p y hp


/-- **整轮 + 回扫**（右移 / right）。Round + rewind (right move). -/
theorem simDrive_roundNav_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (a0 : Sym) (Z' : List Sym) (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post') (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simDrive q b tab s0).run
        (14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: a0 :: Z'))) =
    Config.mk (embN (codeState q b m'.val 0 0 1 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk Z' (a0 :: none ::
        (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
        ++ codeSnd p.1 :: some true :: codeCells post')) := by
  rw [DTM.run_add (simDrive q b tab s0) 14 _]
  rw [simDrive_run14_right q b tab s0 m c hm hc x (none :: a0 :: Z') p post' hp hpost
    m' s' hx h]
  simp only [← List.cons_append]
  rw [simDrive_rewind q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
    (codeSnd p.1) (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)])))
    (codeSnd_ne_none p.1) ?_ a0 Z' (some true :: codeCells post')]
  · intro y hy
    rcases (List.mem_cons.mp hy) with hy | hy
    · exact hy ▸ codeFst_ne_none p.1
    · have hy' := List.mem_reverse.mp hy
      simp only [codeCells, List.mem_flatMap] at hy'
      obtain ⟨q0, _, hq0⟩ := hy'
      exact cellCode_ne_none q0 y hq0

/-- **整轮 + 回扫**（左移 / left）。Round + rewind (left move). -/
theorem simDrive_roundNav_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (a0 : Sym) (Z' : List Sym) (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre : x.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simDrive q b tab s0).run
        (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: a0 :: Z'))) =
    Config.mk (embN (codeState q b m'.val 0 0 1 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide)))
      (Tape.mk Z' (a0 :: none ::
        (codeFst cq.1 :: List.reverse (codeCells pre')).reverse
        ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))) := by
  rw [DTM.run_add (simDrive q b tab s0) 14 _]
  rw [simDrive_run14_left q b tab s0 m c hm hc x (none :: a0 :: Z') cq pre' hq hpre
    m' s' hx h]
  simp only [← List.cons_append]
  rw [simDrive_rewind q b tab s0 m'.val 0 m'.isLt (Nat.two_pow_pos b)
    (codeSnd cq.1) (codeFst cq.1 :: List.reverse (codeCells pre'))
    (codeSnd_ne_none cq.1) ?_ a0 Z' (some true :: codeCells ((s', false) :: x.post))]
  · intro y hy
    rcases (List.mem_cons.mp hy) with hy | hy
    · exact hy ▸ codeFst_ne_none cq.1
    · have hy' := List.mem_reverse.mp hy
      simp only [codeCells, List.mem_flatMap] at hy'
      obtain ⟨q0, _, hq0⟩ := hy'
      exact cellCode_ne_none q0 y hq0



/-- **跳零 + 计数**：子相位 1 从块终结符 0 出发，左跳 `z` 个已消费的 0、
    计完本块 `k + 2` 个 1，共 `z + k + 3` 步，终值 `K = k + 2`（位数 + 1），
    头停在 `x`（非 1）上、子相位 2。
    Skip + count: from the block terminator 0, skip `z` consumed zeros and count the
    block's `k + 2` ones; after `z + k + 3` steps the counter is `K = k + 2`, subphase 2. -/
theorem simDrive_skipCount (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m K : Nat) (hm : m < q) (hK : K < 2 ^ b) :
    ∀ (z k : Nat), K = k + 2 → ∀ (x : Sym) (X' R0 : List Sym), x ≠ some true →
      (simDrive q b tab s0).run (z + k + 3)
        (Config.mk (embN (codeState q b m 0 0 1 hm (Nat.two_pow_pos b)
            (by decide) (by decide)))
          (Tape.mk (List.replicate z (some false)
              ++ (some true :: (List.replicate (k + 1) (some true) ++ (x :: X'))))
            (some false :: R0))) =
        Config.mk (embN (codeState q b m K 0 2 hm hK (by decide) (by decide)))
          (Tape.mk X' (x :: (List.replicate (k + 1) (some true)
            ++ (some true :: (List.replicate (z + 1) (some false) ++ R0))))) := by
  intro z k he x X' R0 hx
  have hb : 1 < 2 ^ b := by omega
  rw [show z + k + 3 = (z + 1) + (1 + (k + 1)) from by omega]
  rw [DTM.run_add (simDrive q b tab s0) (z + 1) (1 + (k + 1))]
  rw [simDrive_skip q b tab s0 m 0 hm (Nat.two_pow_pos b) z (some true)
    (List.replicate (k + 1) (some true) ++ (x :: X')) R0]
  simp only [List.cons_append]
  rw [show 1 + (k + 1) = (k + 1) + 1 from by omega]
  rw [DTM.run_succ_of_not_halted _ (k + 1) _
    (simDrive_halted_embN q b tab s0 _ _)]
  rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph1_true q b tab s0 m 0 hm
    (Nat.two_pow_pos b) hb)]
  simp only [Tape.write, Tape.move, Tape.moveLeft, Tape.read, List.tail,
    List.replicate_succ, List.cons_append]
  rw [simDrive_count2 q b tab s0 m K hm hK 1 k (by omega) hb x X'
    (some true :: (some false :: (List.replicate z (some false) ++ R0))) hx]
  simp only [List.cons_append, List.replicate_succ, List.append_assoc]


/-- **整轮 + 回扫 + 跳零 + 计数**（原地 / stay）：`14 + |L0| + 2 + (z + k + 3)` 步后
    计数为 `K = k + 2`、子相位 2，头停在 `xc`（非 1）上。
    Round + rewind + skip + count (stay). -/
theorem simDrive_roundNavCount_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simDrive q b tab s0).run
        ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)) + (z + k + 3))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
    Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
      (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
        ++ (some true :: (List.replicate (z + 1) (some false)
          ++ (none :: (codeFst s' :: List.reverse (codeCells x.pre)).reverse
            ++ codeSnd s' :: some true :: codeCells x.post)))))) := by
  refine (DTM.run_add (simDrive q b tab s0)
    (14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2)) (z + k + 3)
    (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (x.enc (none :: (some false) :: (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))))).trans ?_
  refine (congrArg (fun cfg => (simDrive q b tab s0).run (z + k + 3) cfg)
    (simDrive_roundNav_stay q b tab s0 m c hm hc x (some false)
      (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      m' s' hx h)).trans ?_
  exact simDrive_skipCount q b tab s0 m'.val K m'.isLt hK z k hK2 xc X'
    (none :: (codeFst s' :: List.reverse (codeCells x.pre)).reverse
      ++ codeSnd s' :: some true :: codeCells x.post) hxc

/-- **整轮 + 回扫 + 跳零 + 计数**（右移 / right）。Round + rewind + skip + count (right). -/
theorem simDrive_roundNavCount_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post') (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simDrive q b tab s0).run
        ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
          + (z + k + 3))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
    Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
      (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
        ++ (some true :: (List.replicate (z + 1) (some false)
          ++ (none :: (codeFst p.1
              :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
            ++ codeSnd p.1 :: some true :: codeCells post')))))) := by
  refine (DTM.run_add (simDrive q b tab s0)
    (14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2))
    (z + k + 3)
    (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (x.enc (none :: (some false) :: (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))))).trans ?_
  refine (congrArg (fun cfg => (simDrive q b tab s0).run (z + k + 3) cfg)
    (simDrive_roundNav_right q b tab s0 m c hm hc x (some false)
      (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      p post' hp hpost m' s' hx h)).trans ?_
  exact simDrive_skipCount q b tab s0 m'.val K m'.isLt hK z k hK2 xc X'
    (none :: (codeFst p.1
        :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
      ++ codeSnd p.1 :: some true :: codeCells post') hxc

/-- **整轮 + 回扫 + 跳零 + 计数**（左移 / left）。Round + rewind + skip + count (left). -/
theorem simDrive_roundNavCount_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre : x.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simDrive q b tab s0).run
        ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) + (z + k + 3))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
    Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
      (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
        ++ (some true :: (List.replicate (z + 1) (some false)
          ++ (none :: (codeFst cq.1 :: List.reverse (codeCells pre')).reverse
            ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))))))) := by
  refine (DTM.run_add (simDrive q b tab s0)
    (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) (z + k + 3)
    (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
      (x.enc (none :: (some false) :: (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))))))).trans ?_
  refine (congrArg (fun cfg => (simDrive q b tab s0).run (z + k + 3) cfg)
    (simDrive_roundNav_left q b tab s0 m c hm hc x (some false)
      (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))
      cq pre' hq hpre m' s' hx h)).trans ?_
  exact simDrive_skipCount q b tab s0 m'.val K m'.isLt hK z k hK2 xc X'
    (none :: (codeFst cq.1 :: List.reverse (codeCells pre')).reverse
      ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)) hxc


/-- `replicate` 保持非空白。Repetition preserves non-blank symbols. -/
theorem replicate_ne_none (n : Nat) (a : Sym) (ha : a ≠ none) :
    ∀ y ∈ List.replicate n a, y ≠ none := by
  induction n with
  | zero =>
      intro y hy
      simp at hy
  | succ n ih =>
      intro y hy
      simp only [List.replicate_succ, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ha
      · exact ih y hy

/-- 未停机时 `run 1` 就是一步。`run 1` is exactly one step when not halted. -/
theorem run_one {n : Nat} (M : DTM n) (c : Config n) (h : M.halted c = false) :
    M.run 1 c = M.stepConfig c := by
  rw [show (1 : Nat) = 0 + 1 from rfl, DTM.run_succ_of_not_halted _ 0 _ h]
  rfl

/-- **计数后返回擦除**（子相位 2 → 4）：读 `xc`（非 1）进入子相位 3、右移，
    再把 `D = 1^(k+1) ++ [1] ++ 0^(z+1)` 擦成 0，遇分隔空白进入子相位 4；
    共 `1 + (|D| + 1)` 步。
    Count-then-erase (subphase 2 -> 4): read `xc`, enter subphase 3, move right,
    erase `D` to zeros, then step into subphase 4 on the separator blank. -/
theorem simDrive_ph2Erase (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m K : Nat) (hm : m < q) (hK : K < 2 ^ b) :
    ∀ (z k : Nat) (xc : Sym) (X' R2' : List Sym), xc ≠ some true →
      (simDrive q b tab s0).run
          (1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
        (Config.mk (embN (codeState q b m K 0 2 hm hK (by decide) (by decide)))
          (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
            ++ (some true :: (List.replicate (z + 1) (some false)
              ++ (none :: R2'))))))) =
        Config.mk (embN (codeState q b m K 0 4 hm hK (by decide) (by decide)))
          (Tape.mk (none :: List.replicate
              (List.replicate (k + 1) (some true)
                ++ (some true :: List.replicate (z + 1) (some false))).length
              (some false) ++ xc :: X') R2') := by
  intro z k xc X' R2' hxc
  generalize hDdef : (List.replicate (k + 1) (some true)
    ++ (some true :: List.replicate (z + 1) (some false))) = D
  have hD : ∀ y ∈ D, y ≠ none := by
    intro y hy
    rw [← hDdef] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact replicate_ne_none (k + 1) (some true) (by decide) y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact (by decide)
      · exact replicate_ne_none (z + 1) (some false) (by decide) y hy
  have hstep1 : (simDrive q b tab s0).run 1
      (Config.mk (embN (codeState q b m K 0 2 hm hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: R2'))))))) =
      Config.mk (embN (codeState q b m K 0 3 hm hK (by decide) (by decide)))
        (Tape.mk (xc :: X') (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: R2'))))) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
      DTM.run_succ_of_not_halted _ 0 _
        (simDrive_halted_embN q b tab s0 _ _)]
    simp only [DTM.run]
    rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph2_other q b tab s0 m K hm hK xc hxc)]
    simp only [Tape.write, Tape.move, Tape.moveRight, Tape.read, List.tail]
  have hC2eq : Config.mk (embN (codeState q b m K 0 3 hm hK (by decide) (by decide)))
        (Tape.mk (xc :: X') (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: R2'))))) =
      Config.mk (embN (codeState q b m K 0 3 hm hK (by decide) (by decide)))
        (Tape.mk (xc :: X') (D ++ none :: R2')) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embN, Fin.val_mk, codeState_val]
    · rw [← hDdef]
      simp only [List.append_assoc, List.cons_append]
  refine (DTM.run_add (simDrive q b tab s0) 1 (D.length + 1)
    (Config.mk (embN (codeState q b m K 0 2 hm hK (by decide) (by decide)))
      (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
        ++ (some true :: (List.replicate (z + 1) (some false)
          ++ (none :: R2')))))))).trans ?_
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (D.length + 1) cfg) hstep1).trans ?_)
  exact (congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (D.length + 1) cfg) hC2eq).trans
    (simDrive_erase q b tab s0 m K hm hK D hD xc X' R2')


/-- **找标记 + 回模拟层**（子相位 4 → 7 → 模拟层相位 0）：`3|cs| + 3 + 1` 步，
    计数变成 `c - 1`（读到的选择编号）。
    Find the marker, then return to simulation phase 0 with counter `c - 1`. -/
theorem simDrive_ph4Seek (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) →
      ∀ (s : Sym) (rest : List (Sym × Bool)) (L : List Sym),
        (simDrive q b tab s0).run (3 * cs.length + 3 + 1)
          (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
            (Tape.mk L (codeCells cs ++ cellCode (s, true) ++ codeCells rest))) =
        Config.mk (embS (codeState q b m (c - 1) 0 0 hm
            (by have := hc; omega) (by decide) (by decide)))
          (Tape.mk (List.reverse (codeCells cs ++ symCode s) ++ L)
            (some true :: codeCells rest)) := by
  intro cs hcs s rest L
  have hseek := simDrive_seek q b tab s0 m c hm hc cs hcs s rest L
  have hph7 : (simDrive q b tab s0).run 1
      (Config.mk (embN (codeState q b m c 0 7 hm hc (by decide) (by decide)))
        (Tape.mk (List.reverse (codeCells cs ++ symCode s) ++ L)
          (some true :: codeCells rest))) =
      Config.mk (embS (codeState q b m (c - 1) 0 0 hm
          (by have := hc; omega) (by decide) (by decide)))
        (Tape.mk (List.reverse (codeCells cs ++ symCode s) ++ L)
          (some true :: codeCells rest)) := by
    rw [run_one _ _ (simDrive_halted_embN q b tab s0 _ _)]
    rw [stepConfig_of_step _ _ _ _ _ _ (simDrive_step_ph7 q b tab s0 m c hm hc (some true))]
    simp only [Tape.write, Tape.move, List.tail]
  refine (DTM.run_add (simDrive q b tab s0) (3 * cs.length + 3) 1
    (Config.mk (embN (codeState q b m c 0 4 hm hc (by decide) (by decide)))
      (Tape.mk L (codeCells cs ++ cellCode (s, true) ++ codeCells rest)))).trans ?_
  exact (congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run 1 cfg) hseek).trans hph7


/-- **完整一轮（原地 / stay）**：14 步模拟 + 回扫 + 跳零计数 + 擦除 + 找标记 + 回模拟层，
    共 `14 + |L0| + 2 + (z+k+3) + (1 + (|D|+1)) + (3|pre|+3+1)` 步；终点回到模拟层相位 0，
    计数 `K - 1`（即本轮读到的选择编号），纸带恢复为新 `Reg.enc`。
    Full round (stay): simulation + rewind + skip/count + erase + seek + return to
    simulation phase 0 with counter `K - 1`. -/
theorem simDrive_roundFull_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simDrive q b tab s0).run
        ((14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
          + ((1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
            + (3 * x.pre.length + 3 + 1)))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
    Config.mk (embS (codeState q b m'.val (K - 1) 0 0 m'.isLt
        (by omega) (by decide) (by decide)))
      (Tape.mk (List.reverse (codeCells x.pre ++ symCode s')
          ++ (none :: List.replicate
            (List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length
            (some false) ++ xc :: X'))
        (some true :: codeCells x.post)) := by
  generalize hDdef : (List.replicate (k + 1) (some true)
    ++ (some true :: List.replicate (z + 1) (some false))) = D
  set_option pp.proofs false in
  -- 中间格局：计数后（子相位 2）、擦除后（子相位 4）
  have hC1 : (simDrive q b tab s0).run
      (14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
      Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: (codeFst s' :: List.reverse (codeCells x.pre)).reverse
              ++ codeSnd s' :: some true :: codeCells x.post)))))) :=
    simDrive_roundNavCount_stay q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc m' s' hx h
  refine (DTM.run_add (simDrive q b tab s0)
    (14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
    ((1 + (D.length + 1)) + (3 * x.pre.length + 3 + 1)) _).trans ?_
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run ((1 + (D.length + 1)) + (3 * x.pre.length + 3 + 1)) cfg)
    hC1).trans ?_)
  refine (DTM.run_add (simDrive q b tab s0) (1 + (D.length + 1))
    (3 * x.pre.length + 3 + 1) _).trans ?_
  have hP2 := simDrive_ph2Erase q b tab s0 m'.val K m'.isLt hK z k xc X'
    ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
      ++ codeSnd s' :: some true :: codeCells x.post) hxc
  rw [hDdef] at hP2
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (3 * x.pre.length + 3 + 1) cfg) hP2)).trans ?_
  have hC2eq : Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK
        (by decide) (by decide)))
      (Tape.mk (none :: List.replicate D.length (some false) ++ xc :: X')
        ((codeFst s' :: List.reverse (codeCells x.pre)).reverse
          ++ codeSnd s' :: some true :: codeCells x.post)) =
      Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK (by decide) (by decide)))
        (Tape.mk (none :: List.replicate D.length (some false) ++ xc :: X')
          (codeCells x.pre ++ cellCode (s', true) ++ codeCells x.post)) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embN, Fin.val_mk, codeState_val]
    · simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc,
        List.cons_append, List.nil_append, cellCode, symCode_eq, if_true]
  have hP4 := simDrive_ph4Seek q b tab s0 m'.val K m'.isLt hK x.pre hpre s' x.post
    (none :: List.replicate
      (List.replicate (k + 1) (some true)
        ++ (some true :: List.replicate (z + 1) (some false))).length
      (some false) ++ xc :: X')
  rw [hDdef] at hP4
  exact (congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (3 * x.pre.length + 3 + 1) cfg) hC2eq).trans hP4

/-- **完整一轮（原地 / stay）**：14 步模拟 + 回扫 + 跳零计数 + 擦除 + 找标记 + 回模拟层，
    共 `14 + |L0| + 2 + (z+k+3) + (1 + (|D|+1)) + (3|pre|+3+1)` 步；终点回到模拟层相位 0，
    计数 `K - 1`（即本轮读到的选择编号），纸带恢复为新 `Reg.enc`。
    Full round (stay): simulation + rewind + skip/count + erase + seek + return to
    simulation phase 0 with counter `K - 1`. -/
theorem simDrive_roundFull_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ c0 ∈ x.pre, c0.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simDrive q b tab s0).run
        ((14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
          + ((1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
            + (3 * (x.pre ++ [(s', false)]).length + 3 + 1)))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
    Config.mk (embS (codeState q b m'.val (K - 1) 0 0 m'.isLt
        (by omega) (by decide) (by decide)))
      (Tape.mk (List.reverse (codeCells (x.pre ++ [(s', false)]) ++ symCode p.1)
          ++ (none :: List.replicate
            (List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length
            (some false) ++ xc :: X'))
        (some true :: codeCells post')) := by
  have hpreR : ∀ c0 ∈ x.pre ++ [(s', false)], c0.2 = false := by
    intro c0 hc0
    rcases List.mem_append.mp hc0 with hc0' | hc0'
    · exact hpre c0 hc0'
    · rw [List.mem_singleton] at hc0'
      subst hc0'
      rfl
  generalize hDdef : (List.replicate (k + 1) (some true)
    ++ (some true :: List.replicate (z + 1) (some false))) = D
  set_option pp.proofs false in
  -- 中间格局：计数后（子相位 2）、擦除后（子相位 4）
  have hC1 : (simDrive q b tab s0).run
      (14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
      Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: (codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
              ++ codeSnd p.1 :: some true :: codeCells post')))))) :=
    simDrive_roundNavCount_right q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc p post' hp hpost m' s' hx h
  refine (DTM.run_add (simDrive q b tab s0)
    (14 + ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
    ((1 + (D.length + 1)) + (3 * (x.pre ++ [(s', false)]).length + 3 + 1)) _).trans ?_
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run ((1 + (D.length + 1)) + (3 * (x.pre ++ [(s', false)]).length + 3 + 1)) cfg)
    hC1).trans ?_)
  refine (DTM.run_add (simDrive q b tab s0) (1 + (D.length + 1))
    (3 * (x.pre ++ [(s', false)]).length + 3 + 1) _).trans ?_
  have hP2 := simDrive_ph2Erase q b tab s0 m'.val K m'.isLt hK z k xc X'
    ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
      ++ codeSnd p.1 :: some true :: codeCells post') hxc
  rw [hDdef] at hP2
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (3 * (x.pre ++ [(s', false)]).length + 3 + 1) cfg) hP2)).trans ?_
  have hC2eq : Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK
        (by decide) (by decide)))
      (Tape.mk (none :: List.replicate D.length (some false) ++ xc :: X')
        ((codeFst p.1 :: List.reverse (codeCells (x.pre ++ [(s', false)]))).reverse
          ++ codeSnd p.1 :: some true :: codeCells post')) =
      Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK (by decide) (by decide)))
        (Tape.mk (none :: List.replicate D.length (some false) ++ xc :: X')
          (codeCells (x.pre ++ [(s', false)]) ++ cellCode (p.1, true) ++ codeCells post')) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embN, Fin.val_mk, codeState_val]
    · simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc,
        List.cons_append, List.nil_append, cellCode, symCode_eq, if_true]
  have hP4 := simDrive_ph4Seek q b tab s0 m'.val K m'.isLt hK (x.pre ++ [(s', false)]) hpreR p.1 post'
    (none :: List.replicate
      (List.replicate (k + 1) (some true)
        ++ (some true :: List.replicate (z + 1) (some false))).length
      (some false) ++ xc :: X')
  rw [hDdef] at hP4
  exact (congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (3 * (x.pre ++ [(s', false)]).length + 3 + 1) cfg) hC2eq).trans hP4

/-- **完整一轮（原地 / stay）**：14 步模拟 + 回扫 + 跳零计数 + 擦除 + 找标记 + 回模拟层，
    共 `14 + |L0| + 2 + (z+k+3) + (1 + (|D|+1)) + (3|pre|+3+1)` 步；终点回到模拟层相位 0，
    计数 `K - 1`（即本轮读到的选择编号），纸带恢复为新 `Reg.enc`。
    Full round (stay): simulation + rewind + skip/count + erase + seek + return to
    simulation phase 0 with counter `K - 1`. -/
theorem simDrive_roundFull_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ c0 ∈ x.pre, c0.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre2 : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simDrive q b tab s0).run
        ((14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
          + ((1 + ((List.replicate (k + 1) (some true)
            ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
            + (3 * pre'.length + 3 + 1)))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
    Config.mk (embS (codeState q b m'.val (K - 1) 0 0 m'.isLt
        (by omega) (by decide) (by decide)))
      (Tape.mk (List.reverse (codeCells pre' ++ symCode cq.1)
          ++ (none :: List.replicate
            (List.replicate (k + 1) (some true)
              ++ (some true :: List.replicate (z + 1) (some false))).length
            (some false) ++ xc :: X'))
        (some true :: codeCells ((s', false) :: x.post))) := by
  have hpreL : ∀ c0 ∈ pre', c0.2 = false := by
    intro c0 hc0
    exact hpre c0 (by rw [hpre2]; exact List.mem_append_left _ hc0)
  generalize hDdef : (List.replicate (k + 1) (some true)
    ++ (some true :: List.replicate (z + 1) (some false))) = D
  set_option pp.proofs false in
  -- 中间格局：计数后（子相位 2）、擦除后（子相位 4）
  have hC1 : (simDrive q b tab s0).run
      (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
      (Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
        (x.enc (none :: (some false) :: (List.replicate z (some false)
          ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X'))))))) =
      Config.mk (embN (codeState q b m'.val K 0 2 m'.isLt hK (by decide) (by decide)))
        (Tape.mk X' (xc :: (List.replicate (k + 1) (some true)
          ++ (some true :: (List.replicate (z + 1) (some false)
            ++ (none :: (codeFst cq.1 :: List.reverse (codeCells pre')).reverse
              ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))))))) :=
    simDrive_roundNavCount_left q b tab s0 m c hm hc x z k K hK hK2 xc X' hxc cq pre' hq hpre2 m' s' hx h
  refine (DTM.run_add (simDrive q b tab s0)
    (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
    ((1 + (D.length + 1)) + (3 * pre'.length + 3 + 1)) _).trans ?_
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run ((1 + (D.length + 1)) + (3 * pre'.length + 3 + 1)) cfg)
    hC1).trans ?_)
  refine (DTM.run_add (simDrive q b tab s0) (1 + (D.length + 1))
    (3 * pre'.length + 3 + 1) _).trans ?_
  have hP2 := simDrive_ph2Erase q b tab s0 m'.val K m'.isLt hK z k xc X'
    ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
      ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post)) hxc
  rw [hDdef] at hP2
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (3 * pre'.length + 3 + 1) cfg) hP2)).trans ?_
  have hC2eq : Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK
        (by decide) (by decide)))
      (Tape.mk (none :: List.replicate D.length (some false) ++ xc :: X')
        ((codeFst cq.1 :: List.reverse (codeCells pre')).reverse
          ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: x.post))) =
      Config.mk (embN (codeState q b m'.val K 0 4 m'.isLt hK (by decide) (by decide)))
        (Tape.mk (none :: List.replicate D.length (some false) ++ xc :: X')
          (codeCells pre' ++ cellCode (cq.1, true) ++ codeCells ((s', false) :: x.post))) := by
    refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embN, Fin.val_mk, codeState_val]
    · simp only [List.reverse_cons, List.reverse_reverse, List.append_assoc,
        List.cons_append, List.nil_append, cellCode, symCode_eq, if_true]
  have hP4 := simDrive_ph4Seek q b tab s0 m'.val K m'.isLt hK pre' hpreL cq.1 ((s', false) :: x.post)
    (none :: List.replicate
      (List.replicate (k + 1) (some true)
        ++ (some true :: List.replicate (z + 1) (some false))).length
      (some false) ++ xc :: X')
  rw [hDdef] at hP4
  exact (congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (3 * pre'.length + 3 + 1) cfg) hC2eq).trans hP4

end DTM

end Pnp
