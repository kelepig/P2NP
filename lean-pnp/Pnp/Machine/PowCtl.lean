/-
  文件：Pnp/Machine/PowCtl.lean
  File: Pnp/Machine/PowCtl.lean

  主题：**U 控制器 `powCtl` 的第一件——`nstep` 相位机**。从值块（unary 计数块）左端出发，
        左行跨过分隔空白、跳过已消费的 `some false` 段，把最近的未消费 `some true`
        翻成 `some false`（消费一个 n 单位），再右行回到值块左端；
        若 n 块已空（读 n 块左端空白），则停机报告耗尽。
  Topic: the first piece of the U-controller `powCtl` — the phase machine `nstep`: it walks left
  from the value block over the separator blank and the consumed `some false` run, flips the
  nearest unconsumed `some true` to `some false` (consuming one `n` unit), then walks right back
  to the value block's first cell; an empty n block (left-end blank reached) halts exhausted.

  纸带布局（`left` 逆序、最近在前；`c` 已消费格数，`r` 未消费格数）：
      `⟨none（分隔）:: false^c ++ true^r ++ none（n 块左端）++ F,  值块 ++ [none] ⟩`
  成功分支：n 块非空（最近的未消费格是 `some true`）——`c = 0` 时 6 步，
  `c ≥ 1` 时 `2c + 6` 步，消费一格后 `c+1 / r-1`；
  耗尽分支：n 块为空——`c = 0` 时 3 步、`c ≥ 1` 时 `c + 3` 步停机。
  Layout (left tape nearest-first): separator, consumed falses, unconsumed trues, the n block's
  left-end blank, then F; the right tape is the value block followed by one blank.

  本文件给出（#221）：
    - 机器 `nstep : DTM 6`（0 初动 / 3 跨分隔 / 4 块内左行并翻单元 / 1 右行回程 /
      5 到值块 = 接受 / 2 耗尽 = 拒绝）；
    - 单步套路 `nstep_halted_ne` / `estepNP`（配 `etapeP` 纸带归一）、跨分隔 `nstep_cross`、
      左行跳过 `nstep_walk_false` / `nstep_walk_false_none`、翻单元 `nstep_flip`、
      右行回程 `nstep_return`；
    - 两条整段规格 `nstep_consume_zero` / `nstep_consume_pos`（消费一个 n 单位并回到值块）
      与耗尽分支 `nstep_exhaust_zero` / `nstep_exhaust_pos`。
  This file gives the machine, its step idioms, the segment lemmas and the whole-phase specs.
-/

import Pnp.Machine.LenRound
import Pnp.Machine.DblOnce
import Pnp.Machine.DblRounds

namespace Pnp

namespace DTM

/-- **n 单位消费相位机**：0 先左移退到分隔空白；3 跨分隔进 n 块；4 跳过 `some false`
    并把 `some true` 翻成 `some false`（状态 1）；1 右行直至值块首格（状态 5，相位结束，
    **不停机**——供上位控制器改接）；4 遇空白进 2（耗尽）。accept = reject = 2（只有耗尽态停机）。
    The `n`-unit consumption phase machine: consume one `true` unit and return to the value
    block (state 5, not halting, so an enclosing controller can rewire it), or halt exhausted
    at state 2. `accept = reject = 2`. -/
def nstep : DTM 6 where
  step := fun st a =>
    match st.val with
    | 0 => (⟨3, by omega⟩, a, Dir.left)
    | 1 => (match a with
       | some true => (⟨5, by omega⟩, some true, Dir.stay)
       | _ => (⟨1, by omega⟩, a, Dir.right))
    | 3 => (⟨4, by omega⟩, a, Dir.left)
    | 4 => (match a with
       | some false => (⟨4, by omega⟩, some false, Dir.left)
       | some true => (⟨1, by omega⟩, some false, Dir.stay)
       | none => (⟨2, by omega⟩, none, Dir.stay))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨2, by omega⟩
  reject := ⟨2, by omega⟩

/-- 同符号的「复制段 ++ 单元素」右移一格：`rep^k s ++ (s :: T) = s :: (rep^k s ++ T)`。
    Shifting one copy of `s` from before a cons to after the replicated block. -/
theorem rep_cons_shift (k : Nat) (s : Sym) (T : List Sym) :
    List.replicate k s ++ (s :: T) = s :: (List.replicate k s ++ T) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

/-- `nstep` 除耗尽态 2 外永不 no-op / 不停机。 The phase machine only halts at state 2. -/
theorem nstep_halted_ne (st : Nat) (hst : st < 6) (h2 : st ≠ 2) (t : Tape) :
    nstep.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show nstep.accept.val = 2 from rfl] at hv
    exact h2 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show nstep.reject.val = 2 from rfl] at hv
    exact h2 hv

/-- `nstep` 的纸带归一（在 `etape` 基础上额外展开 `List.replicate`）。
    Tape normalisation for `nstep`, also unfolding `List.replicate`. -/
macro "etapeP" : tactic => `(tactic|
  (dsimp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, List.tail_cons,
     List.headD_cons, List.headD_nil, List.cons_append, List.append_assoc, List.nil_append,
     List.replicate]))

/-- `nstep` 的单步套路。 The one-step idiom for `nstep`. -/
theorem estepNP (st : Nat) (hst : st < 6) (a : Sym) (q' : Fin 6) (s : Sym) (d : Dir)
    (h : nstep.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym)
    (h2 : st ≠ 2) :
    nstep.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (nstep_halted_ne st hst h2 _)]
  exact stepConfig_of_step nstep ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **成功分支不停机**：若 `nstep` 某段运行的终点状态是 5（回到值块首格），
    则该段运行全程不停机（`accept = reject = 2`，5 与它们不同）。
    A successful segment never halts: halting is confined to state 2. -/
theorem nstep_no_halt (n : Nat) (c : Config 6) (q : Fin 6) (t : Tape)
    (h : nstep.run n c = ⟨q, t⟩) (hq : q.val = 5) :
    ∀ k, k < n → nstep.halted (nstep.run k c) = false := by
  refine halted_false_before nstep n c ?_ ?_
  · rw [h]
    intro hh
    have hv : q.val = nstep.accept.val := congrArg Fin.val hh
    have h2 : nstep.accept.val = 2 := rfl
    omega
  · rw [h]
    intro hh
    have hv : q.val = nstep.reject.val := congrArg Fin.val hh
    have h2 : nstep.reject.val = 2 := rfl
    omega

/-- **跨分隔空白**：状态 0 与 3 各左移一格，头落到 n 块最近一格（状态 4）。
    Crossing the separator in two steps, landing on the n block's nearest cell. -/
theorem nstep_cross (x a : Sym) (Xs R : List Sym) :
    nstep.run 2 ⟨(⟨0, by omega⟩ : Fin 6), Tape.mk (none :: (x :: Xs)) (a :: R)⟩
      = ⟨(⟨4, by omega⟩ : Fin 6), Tape.mk Xs (x :: (none :: a :: R))⟩ := by
  rw [show (2 : Nat) = 1 + 1 from rfl, DTM.run_add nstep 1 1]
  rw [estepNP 0 (by omega) a (⟨3, by omega⟩ : Fin 6) a Dir.left
    (by rfl) _ _ (by omega)]
  etapeP
  rw [estepNP 3 (by omega) none (⟨4, by omega⟩ : Fin 6) none Dir.left
    (by rfl) _ _ (by omega)]
  etapeP

/-- **左行跳过已消费格**：状态 4 从最近的已消费格（`some false`）出发，再左行 `k` 格越过
    整段已消费格，停在最近的未消费 `some true` 上（状态仍 4）。
    Walking left over `k` more consumed cells, stopping on the nearest unconsumed `some true`. -/
theorem nstep_walk_false (k r : Nat) (F W : List Sym) :
    nstep.run (k + 1)
      ⟨(⟨4, by omega⟩ : Fin 6),
        Tape.mk (List.replicate k (some false) ++ (some true :: (List.replicate r (some true) ++ none :: F)))
          (some false :: W)⟩
      = ⟨(⟨4, by omega⟩ : Fin 6),
          Tape.mk (List.replicate r (some true) ++ none :: F)
            (some true :: (List.replicate (k + 1) (some false) ++ W))⟩ := by
  induction k generalizing W with
  | zero =>
      rw [estepNP 4 (by omega) (some false) (⟨4, by omega⟩ : Fin 6) (some false) Dir.left
        (by rfl) _ _ (by omega)]
      etapeP
  | succ k ih =>
      rw [DTM.run_succ_of_not_halted nstep (k + 1) _
        (nstep_halted_ne 4 (by omega) (by omega) _)]
      rw [stepConfig_of_step nstep
        ⟨(⟨4, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (k + 1) (some false)
              ++ (some true :: (List.replicate r (some true) ++ none :: F)))
            (some false :: W)⟩
        (⟨4, by omega⟩ : Fin 6) (some false) Dir.left (by rfl)]
      etapeP
      rw [ih (some false :: W)]
      rw [rep_cons_shift (k + 1) (some false) W]
      etapeP

/-- **左行跳过已消费格（耗尽）**：状态 4 越过整段已消费格后停到 n 块左端空白。
    Walking left over the consumed run and stopping on the n block's left-end blank. -/
theorem nstep_walk_false_none (k : Nat) (F W : List Sym) :
    nstep.run (k + 1)
      ⟨(⟨4, by omega⟩ : Fin 6),
        Tape.mk (List.replicate k (some false) ++ none :: F) (some false :: W)⟩
      = ⟨(⟨4, by omega⟩ : Fin 6), Tape.mk F (none :: (List.replicate (k + 1) (some false) ++ W))⟩ := by
  induction k generalizing W with
  | zero =>
      rw [estepNP 4 (by omega) (some false) (⟨4, by omega⟩ : Fin 6) (some false) Dir.left
        (by rfl) _ _ (by omega)]
      etapeP
  | succ k ih =>
      rw [DTM.run_succ_of_not_halted nstep (k + 1) _
        (nstep_halted_ne 4 (by omega) (by omega) _)]
      rw [stepConfig_of_step nstep
        ⟨(⟨4, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (k + 1) (some false) ++ none :: F) (some false :: W)⟩
        (⟨4, by omega⟩ : Fin 6) (some false) Dir.left (by rfl)]
      etapeP
      rw [ih (some false :: W)]
      rw [rep_cons_shift (k + 1) (some false) W]
      etapeP

/-- **翻单元**：状态 4 读最近的未消费 `some true`，原地改写成 `some false`（进状态 1）。
    Flipping the nearest unconsumed `some true` to `some false`, entering the return phase. -/
theorem nstep_flip (L R : List Sym) :
    nstep.run 1 ⟨(⟨4, by omega⟩ : Fin 6), Tape.mk L (some true :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 6), Tape.mk L (some false :: R)⟩ := by
  rw [estepNP 4 (by omega) (some true) (⟨1, by omega⟩ : Fin 6) (some false) Dir.stay
    (by rfl) _ _ (by omega)]
  etapeP

/-- **右行回程**：状态 1 从翻好的单元出发，右行越过 `c` 个已消费格与分隔空白，
    停在值块首格（`some true`），进状态 5（接受）。
    Walking right over the consumed run and the separator back to the value block's first cell. -/
theorem nstep_return (c : Nat) (T : List Sym) (R0' : List Sym) :
    nstep.run (c + 3)
      ⟨(⟨1, by omega⟩ : Fin 6),
        Tape.mk T (some false :: (List.replicate c (some false)
          ++ (none :: (some true :: R0'))))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (none :: (List.replicate c (some false) ++ (some false :: T)))
            (some true :: R0')⟩ := by
  induction c generalizing T with
  | zero =>
      rw [DTM.run_add nstep 1 2]
      rw [estepNP 1 (by omega) (some false) (⟨1, by omega⟩ : Fin 6) (some false) Dir.right
        (by rfl) _ _ (by omega)]
      etapeP
      rw [DTM.run_add nstep 1 1]
      rw [estepNP 1 (by omega) none (⟨1, by omega⟩ : Fin 6) none Dir.right
        (by rfl) _ _ (by omega)]
      etapeP
      rw [estepNP 1 (by omega) (some true) (⟨5, by omega⟩ : Fin 6) (some true) Dir.stay
        (by rfl) _ _ (by omega)]
      etapeP
  | succ c ih =>
      rw [show c + 1 + 3 = 1 + (c + 3) from by omega]
      rw [DTM.run_add nstep 1 (c + 3)]
      rw [estepNP 1 (by omega) (some false) (⟨1, by omega⟩ : Fin 6) (some false) Dir.right
        (by rfl) _ _ (by omega)]
      etapeP
      rw [ih (some false :: T)]
      rw [rep_cons_shift c (some false) (some false :: T)]

/-- **右行回程（无已消费格）**：`nstep_return` 在 `c = 0` 的展开形（3 步）。
    The `c = 0` instance of `nstep_return`, with the blank run dropped (three steps). -/
theorem nstep_return_zero (T R0' : List Sym) :
    nstep.run 3
      ⟨(⟨1, by omega⟩ : Fin 6), Tape.mk T (some false :: (none :: (some true :: R0')))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6), Tape.mk (none :: (some false :: T)) (some true :: R0')⟩ := by
  simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using nstep_return 0 T R0'

/-- **消费一个 n 单位（尚无已消费格）**：n 块非空，6 步消费最近一格并回到值块首格。
    Consuming one `n` unit when nothing has been consumed yet (six steps). -/
theorem nstep_consume_zero (r m : Nat) (F R : List Sym) :
    nstep.run 6
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some true :: (List.replicate r (some true) ++ none :: F)))
          (some true :: (List.replicate m (some true) ++ (none :: R)))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (none :: (some false :: (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: R)))⟩ := by
  rw [DTM.run_add nstep 2 4]
  rw [nstep_cross (some true) (some true)
    (List.replicate r (some true) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]
  rw [DTM.run_add nstep 1 3]
  rw [nstep_flip (List.replicate r (some true) ++ none :: F)
    (none :: (some true :: (List.replicate m (some true) ++ (none :: R))))]
  rw [nstep_return_zero (List.replicate r (some true) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]

/-- **消费一个 n 单位（已有已消费格）**：头下（最近）一个是已消费 `some false`，其左再 `c` 个
    已消费格，n 块仍非空；`2c + 8` 步越过整段、翻掉最近的未消费格并回到值块首格。
    Consuming one `n` unit below `c + 1` already-consumed cells (`2c + 8` steps). -/
theorem nstep_consume_pos (c r m : Nat) (F R : List Sym) :
    nstep.run (2 * c + 8)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some false :: (List.replicate c (some false)
            ++ (some true :: (List.replicate r (some true) ++ none :: F)))))
          (some true :: (List.replicate m (some true) ++ (none :: R)))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (none :: (List.replicate (c + 2) (some false)
              ++ (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: R)))⟩ := by
  rw [show 2 * c + 8 = 2 + ((c + 1) + (1 + (c + 1 + 3))) from by omega]
  rw [DTM.run_add nstep 2 ((c + 1) + (1 + (c + 1 + 3)))]
  rw [nstep_cross (some false) (some true)
    (List.replicate c (some false) ++ (some true :: (List.replicate r (some true) ++ none :: F)))
    (List.replicate m (some true) ++ (none :: R))]
  rw [DTM.run_add nstep (c + 1) (1 + (c + 1 + 3))]
  rw [nstep_walk_false c r F
    (none :: (some true :: (List.replicate m (some true) ++ (none :: R))))]
  rw [DTM.run_add nstep 1 (c + 1 + 3)]
  rw [nstep_flip (List.replicate r (some true) ++ none :: F)
    (List.replicate (c + 1) (some false)
      ++ (none :: (some true :: (List.replicate m (some true) ++ (none :: R)))))]
  rw [nstep_return (c + 1) (List.replicate r (some true) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]
  rw [rep_cons_shift (c + 1) (some false) (List.replicate r (some true) ++ none :: F)]
  etapeP

/-- **耗尽（尚未消费任何格）**：n 块为空，3 步停机（拒绝态 2）。
    Halted exhausted when nothing has been consumed (three steps). -/
theorem nstep_exhaust_zero (m : Nat) (F R : List Sym) :
    nstep.run 3
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (none :: F))
          (some true :: (List.replicate m (some true) ++ (none :: R)))⟩
      = ⟨(⟨2, by omega⟩ : Fin 6),
          Tape.mk F (none :: (none :: (some true :: (List.replicate m (some true) ++ (none :: R)))))⟩ := by
  rw [DTM.run_add nstep 2 1]
  rw [nstep_cross none (some true) F (List.replicate m (some true) ++ (none :: R))]
  rw [estepNP 4 (by omega) none (⟨2, by omega⟩ : Fin 6) none Dir.stay
    (by rfl) _ _ (by omega)]
  etapeP

/-- **耗尽（已有已消费格）**：头下（最近）一个是已消费 `some false`，其左再 `c` 个已消费格，
    n 块已空；`c + 4` 步停机（拒绝态 2）。
    Halted exhausted below `c + 1` already-consumed cells (`c + 4` steps). -/
theorem nstep_exhaust_pos (c m : Nat) (F R : List Sym) :
    nstep.run (c + 4)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some false :: (List.replicate c (some false) ++ none :: F)))
          (some true :: (List.replicate m (some true) ++ (none :: R)))⟩
      = ⟨(⟨2, by omega⟩ : Fin 6),
          Tape.mk F (none :: (List.replicate (c + 1) (some false)
            ++ (none :: (some true :: (List.replicate m (some true) ++ (none :: R))))))⟩ := by
  rw [show c + 4 = 2 + (c + 1 + 1) from by omega]
  rw [DTM.run_add nstep 2 (c + 1 + 1)]
  rw [nstep_cross (some false) (some true)
    (List.replicate c (some false) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]
  rw [DTM.run_add nstep (c + 1) 1]
  rw [nstep_walk_false_none c F
    (none :: (some true :: (List.replicate m (some true) ++ (none :: R))))]
  rw [estepNP 4 (by omega) none (⟨2, by omega⟩ : Fin 6) none Dir.stay
    (by rfl) _ _ (by omega)]
  etapeP

/-! ## 相位 1+2 的「到达前一刻」前缀（#223）

   `nstep_return` 的最后一步只是「读到值块首格、原地转 5」，纸带不变。
   把最后一步剥掉就得到停在状态 1、头已在值块首格的前缀版本——`powCtl` 的交接点。
   The prefix ending one step before `nstep`'s arrival (state 1, head on the value block's
   first cell); `powCtl` hands off from exactly here. -/

/-- **右行回程（到达前一刻）**：与 `nstep_return` 同一段路，但停在状态 1（最后一步未走）。
    The return walk one step before arrival (still in state 1). -/
theorem nstep_return_pre (c : Nat) (T R0' : List Sym) :
    nstep.run (c + 2)
      ⟨(⟨1, by omega⟩ : Fin 6),
        Tape.mk T (some false :: (List.replicate c (some false)
          ++ (none :: (some true :: R0'))))⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk (none :: (List.replicate c (some false) ++ (some false :: T)))
            (some true :: R0')⟩ := by
  induction c generalizing T with
  | zero =>
      rw [show (0 : Nat) + 2 = 1 + 1 from rfl, DTM.run_add nstep 1 1]
      rw [estepNP 1 (by omega) (some false) (⟨1, by omega⟩ : Fin 6) (some false) Dir.right
        (by rfl) _ _ (by omega)]
      etapeP
      rw [estepNP 1 (by omega) none (⟨1, by omega⟩ : Fin 6) none Dir.right
        (by rfl) _ _ (by omega)]
      etapeP
  | succ c ih =>
      rw [show c + 1 + 2 = 1 + (c + 2) from by omega, DTM.run_add nstep 1 (c + 2)]
      rw [estepNP 1 (by omega) (some false) (⟨1, by omega⟩ : Fin 6) (some false) Dir.right
        (by rfl) _ _ (by omega)]
      etapeP
      rw [ih (some false :: T)]
      rw [rep_cons_shift c (some false) (some false :: T)]

/-- **右行回程（到达前一刻，无已消费格）**：`nstep_return_pre` 在 `c = 0` 的展开形（2 步）。
    The `c = 0` instance of `nstep_return_pre` (two steps). -/
theorem nstep_return_pre_zero (T R0' : List Sym) :
    nstep.run 2
      ⟨(⟨1, by omega⟩ : Fin 6), Tape.mk T (some false :: (none :: (some true :: R0')))⟩
      = ⟨(⟨1, by omega⟩ : Fin 6), Tape.mk (none :: (some false :: T)) (some true :: R0')⟩ := by
  simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using nstep_return_pre 0 T R0'

/-- **消费一个 n 单位的前缀（尚无已消费格）**：5 步后头在值块首格、状态 1（最后一步未走）。
    The consume prefix when nothing has been consumed yet (five steps). -/
theorem nstep_consume_pre_zero (r m : Nat) (F R : List Sym) :
    nstep.run 5
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some true :: (List.replicate r (some true) ++ none :: F)))
          (some true :: (List.replicate m (some true) ++ (none :: R)))⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk (none :: (some false :: (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: R)))⟩ := by
  rw [show 5 = 2 + (1 + 2) from by omega, DTM.run_add nstep 2 (1 + 2)]
  rw [nstep_cross (some true) (some true)
    (List.replicate r (some true) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]
  rw [DTM.run_add nstep 1 2]
  rw [nstep_flip (List.replicate r (some true) ++ none :: F)
    (none :: (some true :: (List.replicate m (some true) ++ (none :: R))))]
  rw [nstep_return_pre_zero (List.replicate r (some true) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]

/-- **消费一个 n 单位的前缀（已有已消费格）**：`2c + 7` 步后头在值块首格、状态 1。
    The consume prefix below `c + 1` already-consumed cells (`2c + 7` steps, state 1). -/
theorem nstep_consume_pre_pos (c r m : Nat) (F R : List Sym) :
    nstep.run (2 * c + 7)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some false :: (List.replicate c (some false)
            ++ (some true :: (List.replicate r (some true) ++ none :: F)))))
          (some true :: (List.replicate m (some true) ++ (none :: R)))⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk (none :: (List.replicate (c + 2) (some false)
              ++ (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: R)))⟩ := by
  rw [show 2 * c + 7 = 2 + ((c + 1) + (1 + (c + 3))) from by omega]
  rw [DTM.run_add nstep 2 ((c + 1) + (1 + (c + 3)))]
  rw [nstep_cross (some false) (some true)
    (List.replicate c (some false) ++ (some true :: (List.replicate r (some true) ++ none :: F)))
    (List.replicate m (some true) ++ (none :: R))]
  rw [DTM.run_add nstep (c + 1) (1 + (c + 3))]
  rw [nstep_walk_false c r F
    (none :: (some true :: (List.replicate m (some true) ++ (none :: R))))]
  rw [DTM.run_add nstep 1 (c + 3)]
  rw [nstep_flip (List.replicate r (some true) ++ none :: F)
    (List.replicate (c + 1) (some false)
      ++ (none :: (some true :: (List.replicate m (some true) ++ (none :: R)))))]
  rw [nstep_return_pre (c + 1) (List.replicate r (some true) ++ none :: F)
    (List.replicate m (some true) ++ (none :: R))]
  rw [rep_cons_shift (c + 1) (some false) (List.replicate r (some true) ++ none :: F)]
  etapeP

/-- **状态 5 是「陷阱」**：一旦 `nstep` 进入状态 5，之后任意步数状态都是 5。
    State 5 is absorbing: once entered, the state stays 5 for any number of steps. -/
theorem nstep_run_state_five (k : Nat) :
    ∀ (c : Config 6), c.state = (⟨5, by omega⟩ : Fin 6) →
      (nstep.run k c).state = (⟨5, by omega⟩ : Fin 6) := by
  induction k with
  | zero => intro c h; exact h
  | succ k ih =>
      intro c h
      have hstep : (nstep.stepConfig c).state = (⟨5, by omega⟩ : Fin 6) := by
        rw [DTM.stepConfig_state, h]
        rfl
      rw [DTM.run]
      by_cases hh : nstep.halted c
      · simp only [hh, ite_true]
        exact h
      · simp only [hh, Bool.false_eq_true, ite_false]
        exact ih (nstep.stepConfig c) hstep

/-- **前缀内不可能提前到达**：若 `m` 步时已在状态 5，则 `n` 步（`n ≥ m`）时仍是 5。
    于是「终态是 1」就排除了前 `n` 步内经过状态 5。
    Reaching state 5 early makes the endpoint 5; an endpoint of 1 therefore excludes it. -/
theorem nstep_state_five_stable {m n : Nat} (hmn : m ≤ n) (c : Config 6)
    (h5 : (nstep.run m c).state = (⟨5, by omega⟩ : Fin 6)) :
    (nstep.run n c).state = (⟨5, by omega⟩ : Fin 6) := by
  rw [← Nat.add_sub_of_le hmn, DTM.run_add nstep m (n - m) c]
  exact nstep_run_state_five (n - m) (nstep.run m c) h5

/-! ## U 控制器整机 `powCtl R`（#223）

   `powCtl R` 把两块已机检的积木拼成一台机器：
   - 状态 0..5：**逐字照抄 `nstep` 的转移表**（唯一例外：状态 5 = 相位结束，原地改接
     到倍增段起点）；`nstep` 的耗尽态 2 同时是整机的 accept = reject。
   - 状态 6..6+7R：**逐字照抄 `dblRounds R` 的转移表**（唯一例外：终止态 `6+7R` 改接回
     状态 0，形成「消费一个 n 单元 → 跑 R 轮倍增 → 回来再消费」的循环）。
   The U-controller `powCtl R`: states 0..5 copy `nstep` (state 5 hands off to the doubling
   block), states 6..6+7R copy `dblRounds R` (its terminal rewired back to state 0).
-/

/-- 把倍增段（`Fin (7R+1)`）的状态抬到控制器右端：偏移 +6。
    Lifting a doubling-block state into the controller (offset 6). -/
def dblEmb (R : Nat) (s : Fin (7 * R + 1)) : Fin (7 * R + 8) :=
  ⟨6 + s.val, by have := s.isLt; omega⟩

/-- 把 `nstep` 的状态（`Fin 6`）放进制器左端：编号不变。
    Placing an `nstep` state inside the controller (same index). -/
def emb6 (R : Nat) (s : Fin 6) : Fin (7 * R + 8) :=
  ⟨s.val, by have := s.isLt; omega⟩

/-- **U 控制器 `powCtl R`**：n 单位消费相位（照抄 `nstep`）+ 固定 R 轮倍增相位
    （照抄 `dblRounds R`），两条改接转移把它们首尾相接。停机 = `nstep` 耗尽（状态 2）。
    The U-controller: `nstep` phase + `dblRounds R` phase with two rewiring transitions. -/
def powCtl (R : Nat) : DTM (7 * R + 8) where
  step := fun st a =>
    if h6 : st.val < 6 then
      if h5 : st.val = 5 then
        -- 相位结束：原地改接进倍增段起点（纸带不动）
        (dblEmb R (dblRounds R).start, a, Dir.stay)
      else
        -- 逐字照抄 `nstep` 的转移
        let r := nstep.step ⟨st.val, h6⟩ a
        (emb6 R r.1, r.2.1, r.2.2)
    else
      if hb : st.val - 6 < 7 * R + 1 then
        if hs : (⟨st.val - 6, hb⟩ : Fin (7 * R + 1)) = (dblRounds R).accept then
          -- 倍增段终止：回到相位 0，再消费下一个 n 单元
          (⟨0, by omega⟩, a, Dir.stay)
        else
          let r := (dblRounds R).step ⟨st.val - 6, hb⟩ a
          (dblEmb R r.1, r.2.1, r.2.2)
      else (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨2, by omega⟩
  reject := ⟨2, by omega⟩

/-- 控制器起始态编号 0。 The start state index is 0. -/
theorem powCtl_start_val (R : Nat) : (powCtl R).start.val = 0 := rfl

/-- 控制器接受态编号 2（= `nstep` 耗尽态）。 The accept index is 2. -/
theorem powCtl_accept_val (R : Nat) : (powCtl R).accept.val = 2 := rfl

/-- 控制器拒绝态编号 2。 The reject index is 2. -/
theorem powCtl_reject_val (R : Nat) : (powCtl R).reject.val = 2 := rfl

/-- 控制器只在状态 2 停机（`nstep` 的耗尽态）。 Only state 2 halts. -/
theorem powCtl_halted_ne (R : Nat) (s : Fin (7 * R + 8)) (h2 : s.val ≠ 2) (t : Tape) :
    (powCtl R).halted ⟨s, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (powCtl R).accept.val = 2 from rfl] at hv
    exact h2 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show (powCtl R).reject.val = 2 from rfl] at hv
    exact h2 hv

/-- **左段的单步照抄**：只要 `nstep` 的状态不是 5，控制器在该状态上的转移与 `nstep` 完全一致。
    The left block copies `nstep` on every state other than 5. -/
theorem powCtl_step_copy (R : Nat) (s : Fin 6) (a : Sym) (h5 : s.val ≠ 5) :
    (powCtl R).step (emb6 R s) a
      = (emb6 R (nstep.step s a).1, (nstep.step s a).2) := by
  have hlt : (emb6 R s).val < 6 := s.isLt
  have hne : ¬ ((emb6 R s).val = 5) := h5
  simp only [powCtl]
  rw [dite_eq_left hlt, dite_eq_right hne]
  rfl

/-- **右段的单步照抄**：倍增段非终止态与 `dblRounds R` 完全一致。
    The right block copies `dblRounds R` away from its terminal state. -/
theorem powCtl_step_dbl (R : Nat) (s : Fin (7 * R + 1)) (a : Sym)
    (hne : s ≠ (dblRounds R).accept) :
    (powCtl R).step (dblEmb R s) a
      = (dblEmb R ((dblRounds R).step s a).1, ((dblRounds R).step s a).2) := by
  have hlt : ¬ ((dblEmb R s).val < 6) := by
    show ¬ (6 + s.val < 6)
    omega
  have hb : (dblEmb R s).val - 6 < 7 * R + 1 := by
    show 6 + s.val - 6 < 7 * R + 1
    omega
  have h1 : (⟨(dblEmb R s).val - 6, hb⟩ : Fin (7 * R + 1)) = s :=
    Fin.ext (by show 6 + s.val - 6 = s.val; omega)
  have hs : ¬ ((⟨(dblEmb R s).val - 6, hb⟩ : Fin (7 * R + 1)) = (dblRounds R).accept) := by
    rw [h1]
    exact hne
  simp only [powCtl]
  rw [dite_eq_right hlt, dite_eq_left hb, dite_eq_right hs, h1]

/-- **左段整体搬运**：`nstep` 在前 `n` 步不停机且不经过状态 2/5，则控制器照搬整段运行。
    Lifting a whole `nstep` run into the controller (states 2 and 5 excluded). -/
theorem powCtl_run_consume_pre (R n : Nat) (c : Config 6) (q : Fin 6) (t : Tape)
    (h : nstep.run n c = ⟨q, t⟩) (hq : q = (⟨1, by omega⟩ : Fin 6)) :
    (powCtl R).run n ⟨emb6 R c.state, c.tape⟩ = ⟨emb6 R q, t⟩ := by
  -- 整段不停机（终点状态 1 不是 `nstep` 的终止态 2）
  have hA : ∀ m, m < n → nstep.halted (nstep.run m c) = false := by
    intro m hm
    refine halted_false_before nstep n c ?_ ?_ m hm
    · rw [h]
      intro hh
      have hqq : q = nstep.accept := hh
      have h2 : q.val = nstep.accept.val := congrArg Fin.val hqq
      have h3 : nstep.accept.val = 2 := rfl
      have hq1 : q.val = 1 := congrArg Fin.val hq
      omega
    · rw [h]
      intro hh
      have hqq : q = nstep.reject := hh
      have h2 : q.val = nstep.reject.val := congrArg Fin.val hqq
      have h3 : nstep.reject.val = 2 := rfl
      have hq1 : q.val = 1 := congrArg Fin.val hq
      omega
  -- 前缀内状态既非 2（否则会停机）也非 5（否则终点也是 5）
  have hok : ∀ m, m < n → (nstep.run m c).state.val ≠ 2 ∧ (nstep.run m c).state.val ≠ 5 := by
    intro m hm
    have hnh := hA m hm
    constructor
    · intro hv
      have hacc : (nstep.run m c).state = nstep.accept := Fin.ext (by rw [hv]; rfl)
      rw [DTM.halted, hacc] at hnh
      simp at hnh
    · intro hv
      have h5 := nstep_state_five_stable (Nat.le_of_lt hm) c (Fin.ext hv)
      rw [h] at h5
      have hqq : q = (⟨5, by omega⟩ : Fin 6) := h5
      have h2 : q.val = 5 := by
        have hq5 := congrArg Fin.val hqq
        simpa using hq5
      have h1 : q.val = 1 := congrArg Fin.val hq
      omega
  have hmain := run_lift nstep (powCtl R) (emb6 R)
    (fun s => s.val ≠ 2 ∧ s.val ≠ 5)
    (fun s a hs => powCtl_step_copy R s a hs.2)
    (fun s hs => by
      constructor
      · intro he
        have hv := congrArg Fin.val he
        rw [show (powCtl R).accept.val = 2 from rfl] at hv
        exact hs.1 hv.symm
      · intro he
        have hv := congrArg Fin.val he
        rw [show (powCtl R).reject.val = 2 from rfl] at hv
        exact hs.1 hv.symm)
    n c hA hok
  rw [h] at hmain
  exact hmain

/-- **到站一步**：状态 1 读到值块首格 `some true`，转进状态 5（纸带不变）。
    The arrival step: state 1 on the value block's first cell moves to state 5. -/
theorem powCtl_arrive (R : Nat) (M Rt : List Sym) :
    (powCtl R).run 1
      ⟨emb6 R (⟨1, by omega⟩ : Fin 6), Tape.mk M (some true :: Rt)⟩
      = ⟨emb6 R (⟨5, by omega⟩ : Fin 6), Tape.mk M (some true :: Rt)⟩ := by
  show (powCtl R).run (0 + 1)
    ⟨emb6 R (⟨1, by omega⟩ : Fin 6), Tape.mk M (some true :: Rt)⟩
    = ⟨emb6 R (⟨5, by omega⟩ : Fin 6), Tape.mk M (some true :: Rt)⟩
  rw [DTM.run_succ_of_not_halted (powCtl R) 0 _
    (powCtl_halted_ne R _ (by show (1 : Nat) ≠ 2; decide) _)]
  exact stepConfig_of_step (powCtl R)
    ⟨emb6 R (⟨1, by omega⟩ : Fin 6), Tape.mk M (some true :: Rt)⟩
    (emb6 R (⟨5, by omega⟩ : Fin 6)) (some true) Dir.stay (by
      show (powCtl R).step (emb6 R (⟨1, by omega⟩ : Fin 6)) (some true)
        = (emb6 R (⟨5, by omega⟩ : Fin 6), (some true, Dir.stay))
      rw [powCtl_step_copy R (⟨1, by omega⟩ : Fin 6) (some true)
        (by show (1 : Nat) ≠ 5; decide)]
      rfl)

/-- **交接一步**：状态 5 原地转入倍增段起点（纸带不动）。
    The handoff step: state 5 rewires into the doubling block's start. -/
theorem powCtl_handoff (R : Nat) (a : Sym) (M Rt : List Sym) :
    (powCtl R).run 1
      ⟨emb6 R (⟨5, by omega⟩ : Fin 6), Tape.mk M (a :: Rt)⟩
      = ⟨dblEmb R (dblRounds R).start, Tape.mk M (a :: Rt)⟩ := by
  show (powCtl R).run (0 + 1)
    ⟨emb6 R (⟨5, by omega⟩ : Fin 6), Tape.mk M (a :: Rt)⟩
    = ⟨dblEmb R (dblRounds R).start, Tape.mk M (a :: Rt)⟩
  rw [DTM.run_succ_of_not_halted (powCtl R) 0 _
    (powCtl_halted_ne R _ (by show (5 : Nat) ≠ 2; decide) _)]
  exact stepConfig_of_step (powCtl R)
    ⟨emb6 R (⟨5, by omega⟩ : Fin 6), Tape.mk M (a :: Rt)⟩
    (dblEmb R (dblRounds R).start) a Dir.stay (by
      show (powCtl R).step (emb6 R (⟨5, by omega⟩ : Fin 6)) a
        = (dblEmb R (dblRounds R).start, (a, Dir.stay))
      simp only [powCtl]
      rw [dite_eq_left (by show (5 : Nat) < 6; omega),
        dite_eq_left (by show (5 : Nat) = 5; omega)])

/-- **消费一个 n 单位（尚无已消费格）**：前半段 5 步（`nstep` 前缀）+ 到站 1 步 + 交接 1 步。
    Consuming one `n` unit when nothing has been consumed (7 steps total). -/
theorem powCtl_consume_zero (R r m : Nat) (F Rt : List Sym) :
    (powCtl R).run 7
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some true :: (List.replicate r (some true) ++ none :: F)))
          (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
      = ⟨dblEmb R (dblRounds R).start,
          Tape.mk (none :: (some false :: (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩ := by
  have hpre := powCtl_run_consume_pre R 5 _ _ _
    (nstep_consume_pre_zero r m F Rt) rfl
  show (powCtl R).run (5 + 1 + 1)
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some true :: (List.replicate r (some true) ++ none :: F)))
          (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
      = ⟨dblEmb R (dblRounds R).start,
          Tape.mk (none :: (some false :: (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
  rw [DTM.run_add (powCtl R) (5 + 1) 1, DTM.run_add (powCtl R) 5 1, hpre,
    powCtl_arrive R, powCtl_handoff R (some true)]

/-- **消费一个 n 单位（已有已消费格）**：前半段 `2c + 7` 步 + 到站 1 步 + 交接 1 步。
    Consuming one `n` unit below `c + 1` consumed cells (`2c + 9` steps total). -/
theorem powCtl_consume_pos (R c r m : Nat) (F Rt : List Sym) :
    (powCtl R).run (2 * c + 9)
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some false :: (List.replicate c (some false)
            ++ (some true :: (List.replicate r (some true) ++ none :: F)))))
          (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
      = ⟨dblEmb R (dblRounds R).start,
          Tape.mk (none :: (List.replicate (c + 2) (some false)
              ++ (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩ := by
  have hpre := powCtl_run_consume_pre R (2 * c + 7) _ _ _
    (nstep_consume_pre_pos c r m F Rt) rfl
  show (powCtl R).run ((2 * c + 7) + 1 + 1)
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some false :: (List.replicate c (some false)
            ++ (some true :: (List.replicate r (some true) ++ none :: F)))))
          (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
      = ⟨dblEmb R (dblRounds R).start,
          Tape.mk (none :: (List.replicate (c + 2) (some false)
              ++ (List.replicate r (some true) ++ none :: F)))
            (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
  rw [DTM.run_add (powCtl R) ((2 * c + 7) + 1) 1,
    DTM.run_add (powCtl R) (2 * c + 7) 1, hpre, powCtl_arrive R, powCtl_handoff R (some true)]

/-- 控制器左段的单步套路（状态照抄 `nstep`）。 The one-step idiom for the controller's left block. -/
theorem estepPC (R : Nat) (st : Nat) (hst : st < 6) (a : Sym) (q' : Fin 6) (s : Sym)
    (d : Dir) (h : nstep.step ⟨st, hst⟩ a = (q', s, d)) (M Rt : List Sym)
    (h2 : st ≠ 2) (h5s : st ≠ 5) :
    (powCtl R).run 1 ⟨emb6 R (⟨st, hst⟩ : Fin 6), Tape.mk M (a :: Rt)⟩
      = ⟨emb6 R q', (Tape.mk M (a :: Rt)).write s |>.move d⟩ := by
  show (powCtl R).run (0 + 1)
    ⟨emb6 R (⟨st, hst⟩ : Fin 6), Tape.mk M (a :: Rt)⟩
    = ⟨emb6 R q', (Tape.mk M (a :: Rt)).write s |>.move d⟩
  rw [DTM.run_succ_of_not_halted (powCtl R) 0 _
    (powCtl_halted_ne R _ (by show st ≠ 2; exact h2) _)]
  exact stepConfig_of_step (powCtl R)
    ⟨emb6 R (⟨st, hst⟩ : Fin 6), Tape.mk M (a :: Rt)⟩ (emb6 R q') s d (by
      show (powCtl R).step (emb6 R (⟨st, hst⟩ : Fin 6)) a = (emb6 R q', s, d)
      rw [powCtl_step_copy R ⟨st, hst⟩ a h5s, h])

/-- **跨分隔空白（控制器版）**：与 `nstep_cross` 同一段路。 -/
theorem powCtl_cross (R : Nat) (x a : Sym) (Xs Rt : List Sym) :
    (powCtl R).run 2
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6), Tape.mk (none :: (x :: Xs)) (a :: Rt)⟩
      = ⟨emb6 R (⟨4, by omega⟩ : Fin 6), Tape.mk Xs (x :: (none :: a :: Rt))⟩ := by
  show (powCtl R).run (1 + 1)
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6), Tape.mk (none :: (x :: Xs)) (a :: Rt)⟩
      = ⟨emb6 R (⟨4, by omega⟩ : Fin 6), Tape.mk Xs (x :: (none :: a :: Rt))⟩
  rw [DTM.run_add (powCtl R) 1 1]
  rw [estepPC R 0 (by omega) a (⟨3, by omega⟩ : Fin 6) a Dir.left (by rfl) _ _
    (by omega) (by omega)]
  etapeP
  rw [estepPC R 3 (by omega) none (⟨4, by omega⟩ : Fin 6) none Dir.left (by rfl) _ _
    (by omega) (by omega)]
  etapeP

/-- **左行跳过已消费格（耗尽版，控制器版）**：与 `nstep_walk_false_none` 同一段路。 -/
theorem powCtl_walk_false_none (R k : Nat) (F W : List Sym) :
    (powCtl R).run (k + 1)
      ⟨emb6 R (⟨4, by omega⟩ : Fin 6),
        Tape.mk (List.replicate k (some false) ++ none :: F) (some false :: W)⟩
      = ⟨emb6 R (⟨4, by omega⟩ : Fin 6),
          Tape.mk F (none :: (List.replicate (k + 1) (some false) ++ W))⟩ := by
  induction k generalizing W with
  | zero =>
      rw [estepPC R 4 (by omega) (some false) (⟨4, by omega⟩ : Fin 6) (some false) Dir.left
        (by rfl) _ _ (by omega) (by omega)]
      etapeP
  | succ k ih =>
      show (powCtl R).run ((k + 1) + 1)
        ⟨emb6 R (⟨4, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (k + 1) (some false) ++ none :: F) (some false :: W)⟩
        = ⟨emb6 R (⟨4, by omega⟩ : Fin 6),
            Tape.mk F (none :: (List.replicate (k + 1 + 1) (some false) ++ W))⟩
      rw [DTM.run_succ_of_not_halted (powCtl R) (k + 1) _
        (powCtl_halted_ne R _ (by show (4 : Nat) ≠ 2; decide) _)]
      rw [stepConfig_of_step (powCtl R)
        ⟨emb6 R (⟨4, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (k + 1) (some false) ++ none :: F) (some false :: W)⟩
        (emb6 R (⟨4, by omega⟩ : Fin 6)) (some false) Dir.left (by
          show (powCtl R).step (emb6 R (⟨4, by omega⟩ : Fin 6)) (some false)
            = (emb6 R (⟨4, by omega⟩ : Fin 6), (some false, Dir.left))
          rw [powCtl_step_copy R (⟨4, by omega⟩ : Fin 6) (some false)
            (by show (4 : Nat) ≠ 5; decide)]
          rfl)]
      etapeP
      rw [ih (some false :: W)]
      rw [rep_cons_shift (k + 1) (some false) W]
      etapeP

/-- **耗尽（尚未消费任何格，控制器版）**：n 块为空，3 步停机（状态 2）。
    Exhausted with nothing consumed: halts in three steps at state 2. -/
theorem powCtl_exhaust_zero (R m : Nat) (F Rt : List Sym) :
    (powCtl R).run 3
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (none :: F))
          (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
      = ⟨(⟨2, by omega⟩ : Fin (7 * R + 8)),
          Tape.mk F
            (none :: (none :: (some true :: (List.replicate m (some true) ++ (none :: Rt)))))⟩ := by
  rw [show (3 : Nat) = 2 + 1 from rfl]
  rw [DTM.run_add (powCtl R) 2 1]
  rw [powCtl_cross R none (some true) F (List.replicate m (some true) ++ (none :: Rt))]
  rw [estepPC R 4 (by omega) none (⟨2, by omega⟩ : Fin 6) none Dir.stay (by rfl) _ _
    (by omega) (by omega)]
  etapeP
  rfl

/-- **耗尽（已有已消费格，控制器版）**：n 块已空，`c + 4` 步停机（状态 2）。
    Exhausted below `c + 1` consumed cells: halts in `c + 4` steps at state 2. -/
theorem powCtl_exhaust_pos (R c m : Nat) (F Rt : List Sym) :
    (powCtl R).run (c + 4)
      ⟨emb6 R (⟨0, by omega⟩ : Fin 6),
        Tape.mk (none :: (some false :: (List.replicate c (some false) ++ none :: F)))
          (some true :: (List.replicate m (some true) ++ (none :: Rt)))⟩
      = ⟨(⟨2, by omega⟩ : Fin (7 * R + 8)),
          Tape.mk F
            (none :: (List.replicate (c + 1) (some false)
              ++ (none :: (some true :: (List.replicate m (some true) ++ (none :: Rt))))))⟩ := by
  rw [show c + 4 = 2 + (c + 1 + 1) from by omega]
  rw [DTM.run_add (powCtl R) 2 (c + 1 + 1)]
  rw [powCtl_cross R (some false) (some true)
    (List.replicate c (some false) ++ none :: F)
    (List.replicate m (some true) ++ (none :: Rt))]
  rw [DTM.run_add (powCtl R) (c + 1) 1]
  rw [powCtl_walk_false_none R c F
    (none :: (some true :: (List.replicate m (some true) ++ (none :: Rt))))]
  rw [estepPC R 4 (by omega) none (⟨2, by omega⟩ : Fin 6) none Dir.stay (by rfl) _ _
    (by omega) (by omega)]
  etapeP
  rfl

/-- **倍增段整体搬运**：控制器状态 `6 + ·` 上照抄 `dblRounds R`，整段 `R` 轮倍增原样搬进来。
    Lifting the whole `dblRounds R` run into the controller's right block. -/
theorem powCtl_run_dbl (R m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    (powCtl R).run (dblRoundsSteps R m)
      ⟨dblEmb R (dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩
      = ⟨dblEmb R (dblRounds R).accept, Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩ := by
  have hmain := run_embed (dblRounds R) (powCtl R) (dblEmb R)
    (fun s a hna _ => powCtl_step_dbl R s a hna)
    (fun s _ _ => by
      constructor
      · intro he
        have hv := congrArg Fin.val he
        rw [show (powCtl R).accept.val = 2 from rfl] at hv
        have h2 : (dblEmb R s).val = 6 + s.val := rfl
        rw [h2] at hv
        omega
      · intro he
        have hv := congrArg Fin.val he
        rw [show (powCtl R).reject.val = 2 from rfl] at hv
        have h2 : (dblEmb R s).val = 6 + s.val := rfl
        rw [h2] at hv
        omega)
    (dblRoundsSteps R m)
    ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩
    (dblRounds_no_halt R m hm L)
  rw [dblRounds_run R m hm L] at hmain
  exact hmain

/-- **倍增段终止后回到相位 0**：一步，纸带不动。 Back to phase 0 after the doubling block. -/
theorem powCtl_back (R : Nat) (a : Sym) (M Rt : List Sym) :
    (powCtl R).run 1
      ⟨dblEmb R (dblRounds R).accept, Tape.mk M (a :: Rt)⟩
      = ⟨(⟨0, by omega⟩ : Fin (7 * R + 8)), Tape.mk M (a :: Rt)⟩ := by
  show (powCtl R).run (0 + 1)
    ⟨dblEmb R (dblRounds R).accept, Tape.mk M (a :: Rt)⟩
    = ⟨(⟨0, by omega⟩ : Fin (7 * R + 8)), Tape.mk M (a :: Rt)⟩
  rw [DTM.run_succ_of_not_halted (powCtl R) 0 _
    (powCtl_halted_ne R _
      (by show ¬ (6 + (dblRounds R).accept.val = 2); omega) _)]
  exact stepConfig_of_step (powCtl R)
    ⟨dblEmb R (dblRounds R).accept, Tape.mk M (a :: Rt)⟩
    (⟨0, by omega⟩ : Fin (7 * R + 8)) a Dir.stay (by
      show (powCtl R).step (dblEmb R (dblRounds R).accept) a
        = ((⟨0, by omega⟩ : Fin (7 * R + 8)), (a, Dir.stay))
      simp only [powCtl]
      rw [dite_eq_right (by show ¬ (6 + (dblRounds R).accept.val < 6); omega),
        dite_eq_left (by show 6 + (dblRounds R).accept.val - 6 < 7 * R + 1; omega),
        dite_eq_left (by
          show (⟨6 + (dblRounds R).accept.val - 6,
              (by show 6 + (dblRounds R).accept.val - 6 < 7 * R + 1; omega)⟩
            : Fin (7 * R + 1)) = (dblRounds R).accept
          exact Fin.ext (by show 6 + (dblRounds R).accept.val - 6
            = (dblRounds R).accept.val; omega))])

end DTM

end Pnp
