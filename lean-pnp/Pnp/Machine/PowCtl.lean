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

end DTM

end Pnp
