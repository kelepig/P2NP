/-
  文件：Pnp/Machine/UnaryAdd.lean
  File: Pnp/Machine/UnaryAdd.lean

  主题：**unary 加法机 `unaryAdd`**——把 `some true^a`（源）复制 `a` 份到其右侧的 `some false`
        块之后，最后整段改写成 `some true`；`a + b + a` 的结果不是 `a + b`，因此该机是
        「重复加法」乘法机的核心部件（docs/07 补记 #201）。
  Topic: the unary addition machine. It copies each `some true` of the source block to the
  right frontier and finally rewrites the whole merged block back to `some true`.

  布局（输入，头在源块**最右格**）：
    left  = `replicate (a-1) true ++ none :: L`（源块其余单元 + 左哨兵 + 上下文）
    right = `true :: replicate b false ++ replicate (a+1) none ++ R`（最右源格 + 目标块 +
            预留空白 + 尾部）
  每轮（i = 已消费单元数）：标记源格 → 右行到前沿空白并写一个 `false` → 左行找下一个 `true`。
  耗尽后由统一相位把整块 `false` 改回 `true`。
-/

import Pnp.Machine.WalkRT
import Pnp.Machine.MarkTrue

namespace Pnp

namespace DTM

/-- unary 加法机（6 状态）：0 读源、1 右行到前沿、2 左行找下一源（空白 ⇒ 3 统一）、
    3 逐格改写、5 接受/拒绝。
    The unary addition machine: 0 reads the source, 1 walks to the frontier, 2 walks back,
    3 unifies, 5 halts. -/
def unaryAdd : DTM 6 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | some true => (⟨1, by omega⟩, some false, Dir.right)
       | _ => (⟨5, by omega⟩, a, Dir.stay))
    | 1 => (match a with
       | none => (⟨2, by omega⟩, some false, Dir.stay)
       | _ => (⟨1, by omega⟩, a, Dir.right))
    | 2 => (match a with
       | some false => (⟨2, by omega⟩, some false, Dir.left)
       | some true => (⟨0, by omega⟩, some true, Dir.stay)
       | none => (⟨3, by omega⟩, none, Dir.right))
    | 3 => (match a with
       | none => (⟨5, by omega⟩, none, Dir.stay)
       | _ => (⟨3, by omega⟩, some true, Dir.right))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 5
  reject := 5

/-- 非 5 状态一律不停机。 States other than 5 never halt. -/
theorem unaryAdd_halted_ne (st : Nat) (hst : st < 6) (h : st ≠ 5) (t : Tape) :
    unaryAdd.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show unaryAdd.accept.val = 5 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show unaryAdd.reject.val = 5 from rfl] at hv
    exact h hv

/-- `unaryAdd` 的单步运行套路。 The one-step idiom for `unaryAdd`. -/
theorem estepUA (st : Nat) (hst : st < 6) (a : Sym) (q' : Fin 6) (s : Sym) (d : Dir)
    (h : unaryAdd.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 5) :
    unaryAdd.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (unaryAdd_halted_ne st hst hne _)]
  exact stepConfig_of_step unaryAdd ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- `some false` 串里没有空白。 A `some false` block contains no blank. -/
theorem replicate_false_ne_none (n : Nat) :
    ∀ y ∈ List.replicate n (some false), y ≠ none := by
  intro y hy
  rw [List.mem_replicate] at hy
  obtain ⟨_, rfl⟩ := hy
  decide

/-- 末尾空白串拆出一个前沿空白：`replicate (k+1) none ++ R = none :: (replicate k none ++ R)`。
    Split one frontier blank off the blank reserve. -/
theorem cons_replicate_none_append (k : Nat) (R : List Sym) :
    List.replicate (k + 1) (none : Sym) ++ R
      = (none : Sym) :: (List.replicate k (none : Sym) ++ R) := by
  rw [List.replicate_succ, List.cons_append]

/-- 两个完整空白（前沿 + 终结）。 Two blanks as an explicit cons block. -/
theorem replicate_two_none (R : List Sym) :
    List.replicate 2 (none : Sym) ++ R = (none : Sym) :: ((none : Sym) :: R) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, cons_replicate_none_append, cons_replicate_none_append,
    show List.replicate 0 (none : Sym) = ([] : List Sym) from rfl, List.nil_append]

/-- **右行到前沿**：状态 1 跳过非空白串 `l`，读到空白即写 `some false` 并进状态 2。
    状态 1 右行：`|l|+1` 步。 The state-1 scan: skip `l`, write a unit at the blank. -/
theorem unaryAdd_scan : ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (L R : List Sym),
    unaryAdd.run (l.length + 1)
      ⟨(⟨1, by omega⟩ : Fin 6), Tape.mk L (l ++ none :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 6),
          Tape.mk (l.reverse ++ L) (some false :: R)⟩
  | [], _, L, R => by
      rw [show ([] : List Sym).length + 1 = 1 from by simp]
      simp only [List.nil_append, List.reverse_nil]
      rw [estepUA 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
  | a :: t, hl, L, R => by
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (by simp [hy])
      cases a with
      | none => exact absurd rfl (hl none (by simp))
      | some y =>
          rw [show (some y :: t).length + 1 = 1 + (t.length + 1) from by
                simp only [List.length_cons]; omega]
          rw [DTM.run_add unaryAdd 1 (t.length + 1)]
          rw [show ((some y :: t) ++ none :: R) = some y :: (t ++ none :: R) from rfl]
          rw [estepUA 1 (by omega) (some y) _ _ _ (by rfl) _ _ (by omega)]
          etape
          rw [show Tape.mk (some y :: L) (t ++ none :: R)
                = Tape.mk (some y :: L) (t ++ (none :: R)) from rfl]
          rw [unaryAdd_scan t ht (some y :: L) R]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **左行到下一个源格**：状态 2 跳过 `m` 个 `some false`，读到 `some true` 回到状态 0。
    The state-2 walk back to the next unread source cell. -/
theorem unaryAdd_back_true : ∀ (m : Nat) (P R : List Sym),
    unaryAdd.run (m + 2)
      ⟨(⟨2, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m (some false) ++ some true :: P) (some false :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk P (some true :: List.replicate (m + 1) (some false) ++ R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add unaryAdd 1 1]
      rw [estepUA 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepUA 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add unaryAdd 1 (m + 2)]
      rw [estepUA 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [unaryAdd_back_true m P (some false :: R)]
      simp only [List.cons_append]
      rw [replicate_succ_append (m + 1) (some false) R]

/-- **左行到左哨兵（源耗尽）**：状态 2 跳过 `m` 个 `some false` 后读到空白，
    进入状态 3 并右移一格（落在整块首格）。
    The state-2 walk reaching the left sentinel: enter state 3 on the block's first cell. -/
theorem unaryAdd_back_none : ∀ (m : Nat) (P R : List Sym),
    unaryAdd.run (m + 2)
      ⟨(⟨2, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m (some false) ++ none :: P) (some false :: R)⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk (none :: P) (List.replicate (m + 1) (some false) ++ R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      rw [show (0 + 2 : Nat) = 1 + 1 from rfl, DTM.run_add unaryAdd 1 1]
      rw [estepUA 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepUA 2 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 2 : Nat) = 1 + (m + 2) from by omega,
        DTM.run_add unaryAdd 1 (m + 2)]
      rw [estepUA 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [unaryAdd_back_none m P (some false :: R)]
      rw [replicate_succ_append (m + 1) (some false) R]

/-- **统一相位**：状态 3 逐格把 `some false` 改写成 `some true`，遇空白接受（状态 5）。
    The unification phase. -/
theorem unaryAdd_unify : ∀ (m : Nat) (P R : List Sym),
    unaryAdd.run (m + 1)
      ⟨(⟨3, by omega⟩ : Fin 6),
        Tape.mk P (List.replicate m (some false) ++ none :: R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (List.replicate m (some true) ++ P) (none :: R)⟩
  | 0, P, R => by
      simp only [List.replicate_zero, List.nil_append]
      exact estepUA 3 (by omega) none _ _ _ (by rfl) _ _ (by omega)
  | m + 1, P, R => by
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [show (m + 1 + 1 : Nat) = 1 + (m + 1) from by omega,
        DTM.run_add unaryAdd 1 (m + 1)]
      rw [estepUA 3 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [unaryAdd_unify m (some true :: P) R]
      rw [replicate_succ_append m (some true) P]

/-- **单轮**：从第 `i` 轮不变量（状态 0、头在下一个源格）出发，`2b+4i+5` 步后到达
    第 `i+1` 轮不变量。 One round of the copy loop. -/
theorem unaryAdd_round (a b i : Nat) (hi : i + 1 ≤ a - 1) (L R : List Sym) :
    unaryAdd.run (2 * b + 4 * i + 5)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1 - i) (some true) ++ none :: L)
          (some true :: List.replicate (b + 2 * i) (some false) ++
            List.replicate (a + 1 - i) none ++ R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (a - 1 - (i + 1)) (some true) ++ none :: L)
            (some true :: List.replicate (b + 2 * (i + 1)) (some false) ++
              List.replicate (a + 1 - (i + 1)) none ++ R)⟩ := by
  -- 预备：下一个源格拆成「头 + 其余」；右带变成「cons 头 + 前沿空白 + 其余空白」
  have htrue : List.replicate (a - 1 - i) (some true)
      = some true :: List.replicate (a - 1 - (i + 1)) (some true) := by
    rw [show a - 1 - i = (a - 1 - (i + 1)) + 1 from by omega, List.replicate_succ]
  have hR1 : some true :: List.replicate (b + 2 * i) (some false)
        ++ List.replicate (a + 1 - i) (none : Sym) ++ R
      = some true :: (List.replicate (b + 2 * i) (some false)
          ++ ((none : Sym) :: (List.replicate (a - i) (none : Sym) ++ R))) := by
    rw [List.append_assoc,
      show List.replicate (a + 1 - i) (none : Sym)
          = (none : Sym) :: List.replicate (a - i) (none : Sym) from by
        rw [show a + 1 - i = (a - i) + 1 from by omega, List.replicate_succ],
      List.cons_append]
    rfl
  have hL1 : (List.replicate (b + 2 * i) (some false)).reverse
        ++ (some false :: (List.replicate (a - 1 - i) (some true) ++ none :: L))
      = List.replicate (b + 2 * i + 1) (some false)
          ++ (some true :: (List.replicate (a - 1 - (i + 1)) (some true) ++ none :: L)) := by
    rw [List.reverse_replicate, htrue, List.cons_append]
    rw [replicate_succ_append (b + 2 * i) (some false)
          (some true :: (List.replicate (a - 1 - (i + 1)) (some true) ++ none :: L))]
  rw [hR1]
  -- 第 1 段：标记源格（1 步）
  rw [show (2 * b + 4 * i + 5 : Nat)
        = 1 + ((b + 2 * i + 1) + (b + 2 * i + 3)) from by omega,
      DTM.run_add unaryAdd 1 ((b + 2 * i + 1) + (b + 2 * i + 3))]
  rw [estepUA 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 第 2 段：右行到前沿并写单位（b+2i+1 步）
  rw [DTM.run_add unaryAdd (b + 2 * i + 1) (b + 2 * i + 3)]
  have hlen : (List.replicate (b + 2 * i) (some false)).length + 1 = b + 2 * i + 1 := by
    rw [List.length_replicate]
  rw [← hlen]
  rw [unaryAdd_scan (List.replicate (b + 2 * i) (some false))
        (replicate_false_ne_none (b + 2 * i)) _ _]
  -- 第 3 段：左行到下一个源格（b+2i+3 步）
  rw [hL1]
  rw [unaryAdd_back_true (b + 2 * i + 1)
        (List.replicate (a - 1 - (i + 1)) (some true) ++ none :: L)
        (List.replicate (a - i) none ++ R)]
  -- 索引与结合律对齐
  rw [show a + 1 - (i + 1) = a - i from by omega,
      show b + 2 * (i + 1) = b + 2 * i + 2 from by omega,
      List.append_assoc]
  -- 索引对齐：`b + 2*i + 1 + 1 = b + 2*i + 2`，其余按 cons 归约
  rw [show b + 2 * i + 1 + 1 = b + 2 * i + 2 from by omega]
  rfl

/-- 循环总成本：`k` 轮、起始轮号 `i`。 Total cost of `k` rounds starting at round `i`. -/
def uaLoopCost (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i => (2 * b + 4 * i + 5) + uaLoopCost b k (i + 1)

/-- **多轮**：`k` 轮复制把不变量从 `i` 推进到 `i+k`。
    `k` rounds advance the loop invariant from `i` to `i + k`. -/
theorem unaryAdd_loop (a b : Nat) : ∀ (k i : Nat), i + k ≤ a - 1 → ∀ (L R : List Sym),
    unaryAdd.run (uaLoopCost b k i)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1 - i) (some true) ++ none :: L)
          (some true :: List.replicate (b + 2 * i) (some false) ++
            List.replicate (a + 1 - i) none ++ R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (a - 1 - (i + k)) (some true) ++ none :: L)
            (some true :: List.replicate (b + 2 * (i + k)) (some false) ++
              List.replicate (a + 1 - (i + k)) none ++ R)⟩
  | 0, i, _, L, R => by
      simp [uaLoopCost, DTM.run]
  | k + 1, i, hk, L, R => by
      have h1 : i + 1 ≤ a - 1 := by omega
      have h2 : i + 1 + k ≤ a - 1 := by omega
      rw [show i + (k + 1) = i + 1 + k from by omega]
      rw [uaLoopCost, DTM.run_add unaryAdd (2 * b + 4 * i + 5) (uaLoopCost b k (i + 1))]
      rw [unaryAdd_round a b i h1 L R]
      rw [unaryAdd_loop a b k (i + 1) h2 L R]

/-- **收尾相位**：源已耗尽（第 `a-1` 轮不变量）时，标记最后一个源格、写最后一个单位、
    走到左哨兵，再把整块统一成 `some true` 并接受。
    The final phase: the last unit, then unify the whole block and accept. -/
theorem unaryAdd_final (a b : Nat) (ha : 1 ≤ a) (L R : List Sym) :
    unaryAdd.run (3 * b + 6 * a + 2)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1 - (a - 1)) (some true) ++ none :: L)
          (some true :: List.replicate (b + 2 * (a - 1)) (some false) ++
            List.replicate (a + 1 - (a - 1)) none ++ R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (b + 2 * a) (some true) ++ none :: L) (none :: R)⟩ := by
  have e1 : a - 1 - (a - 1) = 0 := by omega
  have e2 : a + 1 - (a - 1) = 2 := by omega
  have hR1 : some true :: List.replicate (b + 2 * (a - 1)) (some false)
        ++ List.replicate 2 (none : Sym) ++ R
      = some true :: (List.replicate (b + 2 * (a - 1)) (some false)
          ++ ((none : Sym) :: ((none : Sym) :: R))) := by
    rw [List.append_assoc, replicate_two_none]
    rfl
  have hL1 : (List.replicate (b + 2 * (a - 1)) (some false)).reverse
        ++ (some false :: (none :: L))
      = List.replicate (b + 2 * (a - 1) + 1) (some false) ++ (none :: L) := by
    rw [List.reverse_replicate]
    rw [replicate_succ_append (b + 2 * (a - 1)) (some false) (none :: L)]
  rw [e1, e2]
  simp only [List.replicate_zero, List.nil_append]
  rw [hR1]
  -- 第 1 段：标记（1 步）
  rw [show (3 * b + 6 * a + 2 : Nat)
        = 1 + ((b + 2 * (a - 1) + 1)
            + ((b + 2 * (a - 1) + 3) + (b + 2 * (a - 1) + 3))) from by omega,
      DTM.run_add unaryAdd 1
        ((b + 2 * (a - 1) + 1) + ((b + 2 * (a - 1) + 3) + (b + 2 * (a - 1) + 3)))]
  rw [estepUA 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 第 2 段：右行到前沿并写单位
  rw [DTM.run_add unaryAdd (b + 2 * (a - 1) + 1)
        ((b + 2 * (a - 1) + 3) + (b + 2 * (a - 1) + 3))]
  have hlen : (List.replicate (b + 2 * (a - 1)) (some false)).length + 1
      = b + 2 * (a - 1) + 1 := by
    rw [List.length_replicate]
  rw [← hlen]
  rw [unaryAdd_scan (List.replicate (b + 2 * (a - 1)) (some false))
        (replicate_false_ne_none _) _ _]
  -- 第 3 段：左行到左哨兵，进入统一相位
  rw [hL1]
  rw [DTM.run_add unaryAdd (b + 2 * (a - 1) + 3) (b + 2 * (a - 1) + 3)]
  rw [unaryAdd_back_none (b + 2 * (a - 1) + 1) L (none :: R)]
  rw [unaryAdd_unify (b + 2 * (a - 1) + 2) (none :: L) R]
  rw [show b + 2 * (a - 1) + 2 = b + 2 * a from by omega]

/-- **主定理**：`a ≥ 1` 时，`unaryAdd` 把 `a` 个源单元复制到右侧 `b` 个目标单元之后，
    并统一回 `some true`（结果块长 `a + b + a`）。
    Main theorem: unary addition copies `a` source units onto a `b`-unit block. -/
theorem unaryAdd_run (a b : Nat) (ha : 1 ≤ a) (L R : List Sym) :
    unaryAdd.run (uaLoopCost b (a - 1) 0 + (3 * b + 6 * a + 2))
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ none :: L)
          (some true :: List.replicate b (some false) ++ List.replicate (a + 1) none ++ R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (b + 2 * a) (some true) ++ none :: L) (none :: R)⟩ := by
  rw [DTM.run_add unaryAdd (uaLoopCost b (a - 1) 0) (3 * b + 6 * a + 2)]
  have hloop := unaryAdd_loop a b (a - 1) 0 (by omega) L R
  rw [show a - 1 - 0 = a - 1 from by omega,
      show b + 2 * 0 = b from by omega,
      show a + 1 - 0 = a + 1 from by omega] at hloop
  rw [hloop, show 0 + (a - 1) = a - 1 from by omega]
  exact unaryAdd_final a b ha L R

end DTM

end Pnp
