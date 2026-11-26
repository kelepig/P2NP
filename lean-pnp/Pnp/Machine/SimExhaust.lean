/-
  文件：Pnp/Machine/SimExhaust.lean
  File: Pnp/Machine/SimExhaust.lean

  主题：通路结束后的「耗尽轮」——数字区已空时，驱动器再模拟一步（第 `T` 步），
        随后在导航层发现无剩余块，转入模拟层失败相位 14。
  Topic: the exhaustion round after a finished pass. With an empty digit area the
  driver performs one more simulated step (the `T`-th step), then the navigation
  layer finds no remaining block and enters the failure phase 14.

  这样一条分支的运行总是终止：接受则观察机命中 `obsAcc`，否则命中 `obsFail`；
  既不会因耗尽而无限左移，也不会在预算之外多模拟一步造成误接受。
  Hence every branch run terminates: acceptance yields `obsAcc`, otherwise `obsFail`;
  no endless left march and no extra simulated step that could falsely accept.

  本文件给出：
    - `simDrive_exhaust_zero` / `simDrive_exhaust_succ`：子相位 1 在空数字区
      读到空白/跳过零后读到空白，`z + 1` 步进相位 14；
    - `simDrive_passEnd_exhaust_{stay,right,left}`：`passEnd` 起的耗尽整轮
      （14 步模拟 + 回扫 + 跳零 + 耗尽），到达相位 14 的精确步数。
  This file provides the phase-14 arrival lemmas for the empty digit area and the
  composite exhaustion round from `passEnd` in the three move directions.
-/

import Pnp.Machine.SimDriveNav
import Pnp.Machine.SimRound
import Pnp.Machine.SimPass

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **耗尽（零计数 0）**：子相位 1 直接读到左边界空白，1 步进相位 14。
    Exhaustion with no consumed zeros: one step into phase 14. -/
theorem simDrive_exhaust_zero (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m : Nat) (hm : m < q) (R0 : List Sym) :
    (simDrive q b tab s0).run 1
      (Config.mk (embN (codeState q b m 0 0 1 hm (Nat.two_pow_pos b) (by decide) (by decide)))
        (Tape.mk [] (none :: R0))) =
    Config.mk (embS (codeState q b m 0 0 14 hm (Nat.two_pow_pos b) (by decide) (by decide)))
      (Tape.mk [] (none :: R0)) := by
  rw [run_one (simDrive q b tab s0) _ (simDrive_halted_embN q b tab s0 _ _)]
  rw [simDrive_stepConfig_ph1_blank q b tab s0 m 0 hm (Nat.two_pow_pos b) [] R0]
  simp only [Tape.write, Tape.move, List.tail]

/-- **耗尽（零计数 `z + 1`）**：子相位 1 左跳 `z` 个已消费的 0，再读到左边界空白，
    `z + 2` 步进相位 14。
    Exhaustion with `z + 1` consumed zeros: skip the zeros, then hit the boundary
    blank; `z + 2` steps into phase 14. -/
theorem simDrive_exhaust_succ (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m : Nat) (hm : m < q) (z : Nat) (R0 : List Sym) :
    (simDrive q b tab s0).run (z + 2)
      (Config.mk (embN (codeState q b m 0 0 1 hm (Nat.two_pow_pos b) (by decide) (by decide)))
        (Tape.mk (List.replicate z (some false) ++ [none]) (some false :: R0))) =
    Config.mk (embS (codeState q b m 0 0 14 hm (Nat.two_pow_pos b) (by decide) (by decide)))
      (Tape.mk [] (none :: (List.replicate (z + 1) (some false) ++ R0))) := by
  rw [show z + 2 = (z + 1) + 1 from by omega, DTM.run_add]
  rw [simDrive_skip q b tab s0 m 0 hm (Nat.two_pow_pos b) z none [] R0]
  simp only [List.cons_append]
  rw [simDrive_exhaust_zero q b tab s0 m hm
    (List.replicate (z + 1) (some false) ++ R0)]

/-- **耗尽整轮（原地 / stay）**：`passEnd` 出发，再跑「14 步模拟 + 回扫 + 跳零 + 耗尽」，
    在 `17 + |L0| + z` 步后到达模拟层失败相位 14，其中 `L0 = codeFst s' :: reverse cells pre`。
    Exhaustion round (stay): from `passEnd`, one more `14 + rewind + skip + exhaust` chain
    reaches failure phase 14 within `17 + |L0| + z` steps. -/
theorem simDrive_passEnd_exhaust_stay (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) (r : PassRes q b)
    (m' : Fin q) (s' : Sym)
    (hpk : pick (tab r.reg.state r.reg.cur) r.c = some (m', s', Dir.stay)) :
    ∃ T : Tape,
      (simDrive q b tab s0).run
        (17 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + r.z)
        (passEnd r) =
      Config.mk (embS (codeState q b m'.val 0 0 14 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide))) T := by
  cases hz : r.z with
  | zero =>
      have h1 := simDrive_roundNav_stay q b tab s0 r.reg.state.val r.c
        r.reg.state.isLt r.hc r.reg none [] m' s' rfl hpk
      rw [show 17 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + 0
          = (14 + ((codeFst s' :: List.reverse (codeCells r.reg.pre)).length + 2)) + 1
          from by omega,
        DTM.run_add]
      have hpe : passEnd r
          = Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
              (by decide) (by decide))) (r.reg.enc (none :: none :: [])) := by
        simp only [passEnd, hz, List.replicate_zero, List.nil_append, List.cons_append,
          digitArea]
      rw [hpe]
      rw [h1]
      rw [List.cons_append]
      exact ⟨_, simDrive_exhaust_zero q b tab s0 m'.val m'.isLt
        ((none :: (codeFst s' :: List.reverse (codeCells r.reg.pre)).reverse)
          ++ codeSnd s' :: some true :: codeCells r.reg.post)⟩
  | succ j =>
      have h1 := simDrive_roundNav_stay q b tab s0 r.reg.state.val r.c
        r.reg.state.isLt r.hc r.reg (some false) (List.replicate j (some false) ++ [none])
        m' s' rfl hpk
      rw [show 17 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + (j + 1)
          = (14 + ((codeFst s' :: List.reverse (codeCells r.reg.pre)).length + 2)) + (j + 2)
          from by omega,
        DTM.run_add]
      have hpe : passEnd r
          = Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
              (by decide) (by decide)))
            (r.reg.enc (none :: some false :: (List.replicate j (some false) ++ [none]))) := by
        simp only [passEnd, hz, List.replicate_succ, List.cons_append, digitArea]
      rw [hpe]
      rw [h1]
      simp only [List.cons_append]
      exact ⟨_, simDrive_exhaust_succ q b tab s0 m'.val m'.isLt j
        ((none :: (codeFst s' :: List.reverse (codeCells r.reg.pre)).reverse)
          ++ codeSnd s' :: some true :: codeCells r.reg.post)⟩

/-- **耗尽整轮（右移 / right）**：同 `simDrive_passEnd_exhaust_stay`，
    回扫段按右移后的区域长度计算。
    Exhaustion round (right move). -/
theorem simDrive_passEnd_exhaust_right (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) (r : PassRes q b)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : r.reg.post = p :: post') (m' : Fin q) (s' : Sym)
    (hpk : pick (tab r.reg.state r.reg.cur) r.c = some (m', s', Dir.right)) :
    ∃ T : Tape,
      (simDrive q b tab s0).run
        (17 + (codeFst p.1 :: List.reverse (codeCells (r.reg.pre ++ [(s', false)]))).length
          + r.z)
        (passEnd r) =
      Config.mk (embS (codeState q b m'.val 0 0 14 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide))) T := by
  cases hz : r.z with
  | zero =>
      have h1 := simDrive_roundNav_right q b tab s0 r.reg.state.val r.c
        r.reg.state.isLt r.hc r.reg none [] p post' hp hpost m' s' rfl hpk
      rw [show 17 + (codeFst p.1 :: List.reverse (codeCells (r.reg.pre ++ [(s', false)]))).length
            + 0
          = (14 + ((codeFst p.1 :: List.reverse
              (codeCells (r.reg.pre ++ [(s', false)]))).length + 2)) + 1
          from by omega,
        DTM.run_add]
      have hpe : passEnd r
          = Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
              (by decide) (by decide))) (r.reg.enc (none :: none :: [])) := by
        simp only [passEnd, hz, List.replicate_zero, List.nil_append, List.cons_append,
          digitArea]
      rw [hpe]
      rw [h1]
      rw [List.cons_append]
      exact ⟨_, simDrive_exhaust_zero q b tab s0 m'.val m'.isLt
        ((none :: (codeFst p.1 :: List.reverse
            (codeCells (r.reg.pre ++ [(s', false)]))).reverse)
          ++ codeSnd p.1 :: some true :: codeCells post')⟩
  | succ j =>
      have h1 := simDrive_roundNav_right q b tab s0 r.reg.state.val r.c
        r.reg.state.isLt r.hc r.reg (some false) (List.replicate j (some false) ++ [none])
        p post' hp hpost m' s' rfl hpk
      rw [show 17 + (codeFst p.1 :: List.reverse (codeCells (r.reg.pre ++ [(s', false)]))).length
            + (j + 1)
          = (14 + ((codeFst p.1 :: List.reverse
              (codeCells (r.reg.pre ++ [(s', false)]))).length + 2)) + (j + 2)
          from by omega,
        DTM.run_add]
      have hpe : passEnd r
          = Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
              (by decide) (by decide)))
            (r.reg.enc (none :: some false :: (List.replicate j (some false) ++ [none]))) := by
        simp only [passEnd, hz, List.replicate_succ, List.cons_append, digitArea]
      rw [hpe]
      rw [h1]
      simp only [List.cons_append]
      exact ⟨_, simDrive_exhaust_succ q b tab s0 m'.val m'.isLt j
        ((none :: (codeFst p.1 :: List.reverse
            (codeCells (r.reg.pre ++ [(s', false)]))).reverse)
          ++ codeSnd p.1 :: some true :: codeCells post')⟩

/-- **耗尽整轮（左移 / left）**：同 `simDrive_passEnd_exhaust_stay`，
    回扫段按左移后的区域长度计算。
    Exhaustion round (left move). -/
theorem simDrive_passEnd_exhaust_left (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) (r : PassRes q b)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hpre : r.reg.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hpk : pick (tab r.reg.state r.reg.cur) r.c = some (m', s', Dir.left)) :
    ∃ T : Tape,
      (simDrive q b tab s0).run
        (17 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + r.z)
        (passEnd r) =
      Config.mk (embS (codeState q b m'.val 0 0 14 m'.isLt (Nat.two_pow_pos b)
        (by decide) (by decide))) T := by
  cases hz : r.z with
  | zero =>
      have h1 := simDrive_roundNav_left q b tab s0 r.reg.state.val r.c
        r.reg.state.isLt r.hc r.reg none [] cq pre' hq hpre m' s' rfl hpk
      rw [show 17 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + 0
          = (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) + 1
          from by omega,
        DTM.run_add]
      have hpe : passEnd r
          = Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
              (by decide) (by decide))) (r.reg.enc (none :: none :: [])) := by
        simp only [passEnd, hz, List.replicate_zero, List.nil_append, List.cons_append,
          digitArea]
      rw [hpe]
      rw [h1]
      rw [List.cons_append]
      exact ⟨_, simDrive_exhaust_zero q b tab s0 m'.val m'.isLt
        ((none :: (codeFst cq.1 :: List.reverse (codeCells pre')).reverse)
          ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: r.reg.post))⟩
  | succ j =>
      have h1 := simDrive_roundNav_left q b tab s0 r.reg.state.val r.c
        r.reg.state.isLt r.hc r.reg (some false) (List.replicate j (some false) ++ [none])
        cq pre' hq hpre m' s' rfl hpk
      rw [show 17 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + (j + 1)
          = (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2)) + (j + 2)
          from by omega,
        DTM.run_add]
      have hpe : passEnd r
          = Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
              (by decide) (by decide)))
            (r.reg.enc (none :: some false :: (List.replicate j (some false) ++ [none]))) := by
        simp only [passEnd, hz, List.replicate_succ, List.cons_append, digitArea]
      rw [hpe]
      rw [h1]
      simp only [List.cons_append]
      exact ⟨_, simDrive_exhaust_succ q b tab s0 m'.val m'.isLt j
        ((none :: (codeFst cq.1 :: List.reverse (codeCells pre')).reverse)
          ++ codeSnd cq.1 :: some true :: codeCells ((s', false) :: r.reg.post))⟩

end DTM

end Pnp
