/-
  文件：Pnp/Machine/WalkRC.lean
  File: Pnp/Machine/WalkRC.lean

  主题：**跨一个空白的右走机 `walkRC`**——连续右移跳过所有非空白格，遇到一个空白就跨过它，
        再继续跳过非空白格，最终停在下一个空白上（状态 2）。
  Topic: a right-walker that skips every non-blank cell, CROSSES exactly one blank, keeps
  going, and halts on the next blank (state 2).

  用途（docs/07 补记 #204 的 unary 乘法机）：复制遍从 `A` 的最右未读格出发，右行要跨过
  源区与副本区之间的分隔空白 `sep2` 才能到达前沿空白写副本；`walkR`/`walkRT` 都只能
  「遇空白即停」。本机是 `walkLC`（#204）的右行镜像。
  Use: the multiplication copy pass walks right from the source cell, crosses the separator
  blank `sep2`, and stops at the frontier blank; `walkLC` is the left-hand mirror.
-/

import Pnp.Machine.WalkLC

namespace Pnp

namespace DTM

/-- **跨一个空白的右走机**：状态 0 跳过非空白、遇空白跨过（右移）进状态 1；
    状态 1 继续跳过非空白、遇空白 ⇒ 状态 2（前沿）。其余状态原地吸收。
    Right-walker that crosses one blank; state 2 = reached the frontier blank. -/
def walkRC : DTM 4 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | none => (⟨1, by omega⟩, none, Dir.right)
       | _ => (⟨0, by omega⟩, a, Dir.right))
    | 1 => (match a with
       | none => (⟨2, by omega⟩, none, Dir.stay)
       | _ => (⟨1, by omega⟩, a, Dir.right))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 2

/-- 非 2 状态一律不停机（接受/拒绝都是 2）。 States other than 2 never halt. -/
theorem walkRC_halted_ne (st : Nat) (hst : st < 4) (h2 : st ≠ 2)
    (t : Tape) : walkRC.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkRC.accept.val = 2 from rfl] at hv
    exact h2 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show walkRC.reject.val = 2 from rfl] at hv
    exact h2 hv

/-- `walkRC` 的单步运行套路。 The one-step idiom for `walkRC`. -/
theorem estepRC (st : Nat) (hst : st < 4) (a : Sym) (q' : Fin 4) (s : Sym) (d : Dir)
    (h : walkRC.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 2) :
    walkRC.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (walkRC_halted_ne st hst hne _)]
  exact stepConfig_of_step walkRC ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **跨空白段**：状态 0 跳过非空白串 `l1`（`l1` 中无空白），`|l1| + 1` 步后跨过其后的
    空白，头落在空白右侧的 `x0` 上并进入状态 1。
    The crossing segment: skip the non-blank list `l1`, cross the blank after it. -/
theorem walkRC_cross : ∀ (l1 : List Sym), (∀ y ∈ l1, y ≠ none) →
    ∀ (x0 : Sym) (X L : List Sym),
    walkRC.run (l1.length + 1)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk L (l1 ++ none :: x0 :: X)⟩
      = ⟨(⟨1, by omega⟩ : Fin 4),
          Tape.mk (none :: (l1.reverse ++ L)) (x0 :: X)⟩
  | [], _, x0, X, L => by
      simp only [List.length_nil, List.nil_append, List.reverse_nil]
      rw [show (0 + 1 : Nat) = 1 from rfl]
      rw [estepRC 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
  | a :: t, hl, x0, X, L => by
      have ha : a ≠ none := hl a (by simp)
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (by simp [hy])
      cases a with
      | none => exact absurd rfl ha
      | some y =>
          rw [show (some y :: t).length + 1 = 1 + (t.length + 1) from by
                simp only [List.length_cons]; omega,
            DTM.run_add walkRC 1 (t.length + 1)]
          simp only [List.cons_append]
          rw [estepRC 0 (by omega) (some y) _ _ _ (by rfl) _ _ (by omega)]
          etape
          rw [walkRC_cross t ht x0 X (some y :: L)]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **到位段**：状态 1 跳过非空白串 `l2`，`|l2| + 1` 步后停在空白上并接受（状态 2）。
    The arrival segment: skip the non-blank list `l2` and stop on the next blank. -/
theorem walkRC_skip : ∀ (l2 : List Sym), (∀ y ∈ l2, y ≠ none) →
    ∀ (L R : List Sym),
    walkRC.run (l2.length + 1)
      ⟨(⟨1, by omega⟩ : Fin 4),
        Tape.mk L (l2 ++ none :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (l2.reverse ++ L) (none :: R)⟩
  | [], _, L, R => by
      simp only [List.length_nil, List.nil_append, List.reverse_nil]
      rw [show (0 + 1 : Nat) = 1 from rfl]
      rw [estepRC 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
  | a :: t, hl, L, R => by
      have ha : a ≠ none := hl a (by simp)
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (by simp [hy])
      cases a with
      | none => exact absurd rfl ha
      | some y =>
          rw [show (some y :: t).length + 1 = 1 + (t.length + 1) from by
                simp only [List.length_cons]; omega,
            DTM.run_add walkRC 1 (t.length + 1)]
          simp only [List.cons_append]
          rw [estepRC 1 (by omega) (some y) _ _ _ (by rfl) _ _ (by omega)]
          etape
          rw [walkRC_skip t ht (some y :: L) R]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **跨过空白后第一格就是前沿**：状态 1 读到空白即一步接受。
    The single accept step when the cell after the separator is itself the frontier. -/
theorem walkRC_hit_none (L R : List Sym) :
    walkRC.run 1
      ⟨(⟨1, by omega⟩ : Fin 4), Tape.mk L (none :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 4), Tape.mk L (none :: R)⟩ := by
  rw [estepRC 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- **整段（跨过后第一格即前沿）**：分隔空白两侧都没有副本格，`|l1| + 2` 步到位。
    The whole crossing walk with no copies between the separator and the frontier. -/
theorem walkRC_run0 (l1 : List Sym) (hl1 : ∀ y ∈ l1, y ≠ none) (L R : List Sym) :
    walkRC.run (l1.length + 2)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk L (l1 ++ none :: none :: R)⟩
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (none :: (l1.reverse ++ L)) (none :: R)⟩ := by
  rw [show l1.length + 2 = (l1.length + 1) + 1 from by omega,
    DTM.run_add walkRC (l1.length + 1) 1]
  rw [walkRC_cross l1 hl1 none R L]
  rw [walkRC_hit_none (none :: (l1.reverse ++ L)) R]

/-- **整段（跨过后还有副本格）**：分隔空白之后先跳过至少一格副本（`x0 :: X`），
    再停在前沿空白上。 The whole crossing walk with at least one copy cell after the
    separator. -/
theorem walkRC_run (l1 : List Sym) (hl1 : ∀ y ∈ l1, y ≠ none)
    (x0 : Sym) (hx0 : x0 ≠ none) (X : List Sym) (hX : ∀ y ∈ X, y ≠ none)
    (L R : List Sym) :
    walkRC.run ((l1.length + 1) + ((x0 :: X).length + 1))
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk L (l1 ++ none :: x0 :: (X ++ none :: R))⟩
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk ((x0 :: X).reverse ++ (none :: (l1.reverse ++ L))) (none :: R)⟩ := by
  rw [DTM.run_add walkRC (l1.length + 1) ((x0 :: X).length + 1)]
  rw [walkRC_cross l1 hl1 x0 (X ++ none :: R) L]
  -- 把 cons 形 `x0 :: (X ++ none :: R)` 换成 append 形，套到位段引理
  have hstep :
      (⟨(⟨1, by omega⟩ : Fin 4),
          Tape.mk (none :: (l1.reverse ++ L)) (x0 :: (X ++ none :: R))⟩ : Config 4)
        = ⟨(⟨1, by omega⟩ : Fin 4),
            Tape.mk (none :: (l1.reverse ++ L)) ((x0 :: X) ++ none :: R)⟩ := by
    rw [List.cons_append]
  rw [hstep]
  rw [walkRC_skip (x0 :: X) (by
        intro y hy
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hx0
        · exact hX y hy) (none :: (l1.reverse ++ L)) R]

end DTM

end Pnp
